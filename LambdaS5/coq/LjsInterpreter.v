Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsValues.
Require Import LjsCommon.
Require Import LjsMonads.
Require Import LjsStore.
Require Import Utils.
Require Import LjsOperators.
Require Import JsNumber.

Open Scope list_scope.
Open Scope string_scope.
Open Scope container_scope.

(* Basic idea of how this file works:
* There are tree sections in this file:
* * Closures handling, for calling objects and closures.
* * The evaluators, which actually define the semantics of LambdaJS.
*   There is one evaluator per node constructor,
*   with eventually helper functions.
* * The “looping” functions, which call the evaluators. The “runs”
*   function calls eval at every iteration, with a reference to itself
*   applied to a strictly decreasing integer, to make Coq accept the
*   code.
*)

Record runs_type : Type := runs_type_intro {
    runs_type_eval : ctx -> store -> expr -> result
}.

Implicit Type runs : runs_type.
Implicit Type st : store.
Implicit Type c : ctx.

(***** Utilities ******)

(* Unpacks a store to get an object, calls the predicate with this
* object, and updates the object to the returned value. *)
Definition change_object_cont (st : store) (ptr : object_ptr) (cont : object -> (store -> object -> value -> result) -> result) : result :=
  match st \(ptr?) with
  | Some obj =>
      cont obj (fun st new_obj ret =>
        result_some (out_ter (st \(ptr := new_obj)) (res_value ret))
      )
  | None => result_impossible "Pointer to a non-existing object."
  end
.

Definition change_object (st : store) (ptr : object_ptr) (pred : object -> (store * object * value)) : result :=
  change_object_cont st ptr (fun obj cont => match pred obj with (st, new_obj, ret) => cont st new_obj ret end)
.

(* Fetches the object pointed by the ptr, gets the property associated
* with the name and passes it to the predicate (as an option).
* If the predicate returns None as the now property, the property is
* destroyed; otherwise it is updated/created with the one returned by
* the predicate. *)
Definition change_object_property_cont st (ptr : object_ptr) (name : prop_name) (cont : option attributes -> (store -> option attributes -> value -> result) -> result) : result :=
  change_object_cont st ptr (fun obj cont1 =>
    cont (get_object_property obj name) (fun st oprop res => match oprop with
      | Some prop =>
        cont1 st (set_object_property obj name prop) res
      | None =>
        (* TODO: Remove property *)
        cont1 st obj res
    end))
.

Definition change_object_property st (ptr : object_ptr) (name : prop_name) (pred : option attributes -> (store * option attributes * value)) : result :=
  change_object_property_cont st ptr name (fun attrs cont => match pred attrs with (st, oattrs, ret) => cont st oattrs ret end)
.

(***** Monadic operations for interpreting *******)

(* Evaluate an expression, and calls the continuation with
* the new store and the result of the evaluation. *)
Definition eval_cont {A : Type} runs c st e (cont : result -> resultof A) : resultof A :=
  cont (runs_type_eval runs c st e).

(* Evaluates an expression, and calls the continuation if
* the evaluation finished successfully.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_ter runs c st e (cont : store -> res -> result) : result :=
  eval_cont runs c st e (fun res => if_out_ter res cont)
.

(* Evaluates an expression, and calls the continuation if
* the evaluation returned a value.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_return runs c st e (cont : store -> value -> result) : result :=
  eval_cont runs c st e (fun res => if_value res cont)
.

(****** Closures handling ******)

(* Evaluates all arguments, passing the store from one to the next. *)
Definition eval_arg_list_aux runs c (arg_expr : expr) (cont : store -> list value -> result) st (l : list value) : result :=
  if_eval_return runs c st arg_expr (fun st arg => cont st (arg::l)) 
.

Definition eval_arg_list runs c st (args_expr : list expr) (cont : store -> list value -> result) : result :=
  fold_right (eval_arg_list_aux runs c) (fun st args => cont st (rev args)) args_expr st nil
.

Definition apply runs c st (f_loc : value) (args : list value) : result :=
  if_result_some (get_closure st f_loc) (fun clo =>
    if_result_some (get_closure_ctx clo args) (fun vh =>
      runs_type_eval runs vh st (closure_body clo))
  )
.


(********* Evaluators ********)

(* a lonely identifier.
* Fetch the associated value location and return it. *)
Definition eval_id runs c st (name : string) : result :=
  assert_deref c name (fun v => result_value st v)
.


(* if e_cond e_true else e_false.
* Evaluate the condition and get the associated value, then evaluate
* e_true or e_false depending on the value. *)
Definition eval_if runs c st (e_cond e_true e_false : expr) : result :=
  if_eval_return runs c st e_cond (fun st v =>
    assert_get_bool v (fun b =>
      if b
      then runs_type_eval runs c st e_true
      else runs_type_eval runs c st e_false
  ))
.

(* e1 ; e2.
* Evaluate e1, then e2, and return the value location returned by e2. *)
Definition eval_seq runs c st e1 e2 : result :=
  if_eval_return runs c st e1 (fun st v => runs_type_eval runs c st e2 )
.

Definition eval_jseq runs c st e1 e2 :=
  if_eval_return runs c st e1 (fun st v1 =>
    if_eval_ter runs c st e2 (fun st r =>
      match r with
      | res_exception v2 => result_exception st v2
      | res_value v2 => result_value st (overwrite_value_if_empty v1 v2)
      | res_break l v2 => result_break st l (overwrite_value_if_empty v1 v2)
      end)).

(* Evaluates properties of object literals. *)
Fixpoint eval_object_properties runs c st (l : list (string * property)) (acc : object) (cont : store -> object -> result) {struct l} : result :=
  match l with
  | nil => cont st acc
  | (name, property_data (data_intro value_expr writable_expr enumerable_expr configurable_expr)) :: tail =>
    if_eval_return runs c st configurable_expr (fun st configurable_v =>
      if_eval_return runs c st enumerable_expr (fun st enumerable_v =>
        if_eval_return runs c st value_expr (fun st value_v =>
          if_eval_return runs c st writable_expr (fun st writable_v =>
            assert_get_bool configurable_v (fun configurable =>
              assert_get_bool enumerable_v (fun enumerable => 
                assert_get_bool writable_v (fun writable => 
                  eval_object_properties runs c st tail (set_object_property acc name (
                    attributes_data_of {|
                      attributes_data_value := value_v;
                      attributes_data_writable := writable;
                      attributes_data_enumerable := enumerable;
                      attributes_data_configurable := configurable |}
                    )) cont))))))) 
  | (name, property_accessor (accessor_intro getter_expr setter_expr enumerable_expr configurable_expr)) :: tail =>
    if_eval_return runs c st configurable_expr (fun st configurable_v =>
      if_eval_return runs c st enumerable_expr (fun st enumerable_v =>
        if_eval_return runs c st getter_expr (fun st getter_v =>
          if_eval_return runs c st setter_expr (fun st setter_v =>
            assert_get_bool configurable_v (fun configurable =>
              assert_get_bool enumerable_v (fun enumerable => 
                eval_object_properties runs c st tail (set_object_property acc name (
                  attributes_accessor_of {|
                    attributes_accessor_get := getter_v;
                    attributes_accessor_set := setter_v;
                    attributes_accessor_enumerable := enumerable;
                    attributes_accessor_configurable := configurable |}
                  )) cont))))))
  end
.

(* { [ attrs ] props }
* Evaluate the primval attribute (if any), then the proto attribute (defaults
* to Undefined), then properties. Finally, allocate a new object with the
* computed values. *)
Definition eval_object_decl runs c st (attrs : objattrs) (l : list (string * property)) : result :=
  let 'objattrs_intro class_expr extensible_expr prototype_expr code_expr primval_expr := attrs in
    (* Order of evaluation as in the paper: *)
    if_eval_return runs c st class_expr (fun st class_v =>
      if_eval_return runs c st extensible_expr (fun st extensible_v =>
        if_eval_return runs c st prototype_expr (fun st prototype_v =>
          if_eval_return runs c st code_expr (fun st code_v =>
            if_eval_return runs c st primval_expr (fun st primval_v =>
              assert_get_string class_v (fun class => assert_get_bool extensible_v (fun extensible =>
                let obj := {|
                    object_attrs := {|
                      oattrs_proto := prototype_v;
                      oattrs_class := class;
                      oattrs_extensible := extensible;
                      oattrs_prim_value := primval_v;
                      oattrs_code := code_v 
                    |};
                    object_properties := \{}
                |} in
                eval_object_properties runs c st l obj (fun st obj =>
                  let (st, loc) := add_object st obj
                  in result_value st loc
          ))))))))
.

(* left[right].
* Evaluate left, then right.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, return it; and if it is an “accessor field”, call
* the getter. *)
Definition eval_get_field runs c st (left_expr right_expr  : expr) : result :=
  if_eval_return runs c st left_expr (fun st left_loc =>
    if_eval_return runs c st right_expr (fun st right_loc =>
      assert_get_object st left_loc (fun obj =>
        assert_get_string right_loc (fun name =>
          if_result_some (get_property st obj name) (fun ret =>
            match ret with
            | Some (attributes_data_of data) => result_value st (attributes_data_value data)
            | Some (attributes_accessor_of acc) =>
                apply runs c st (attributes_accessor_get acc) (left_loc :: nil)
            | None =>
                result_value st value_undefined
            end
  )))))
.

(* left[right] = new_val
* Evaluate left, then right, then the new_val.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, set it to the `new_val` and return the `new_val`;
* and if it is an “accessor field”, call the getter with the arguments. *)
Definition eval_set_field runs c st (left_expr right_expr new_val_expr : expr) : result :=
  if_eval_return runs c st left_expr (fun st left_loc =>
    if_eval_return runs c st right_expr (fun st right_loc =>
      if_eval_return runs c st new_val_expr (fun st new_val =>
        assert_get_object_ptr left_loc (fun left_ptr =>
          assert_get_string right_loc (fun name =>
            assert_get_object_from_ptr st left_ptr (fun object =>
              if_result_some (get_property st object name) (fun ret =>
                match ret with
                | Some (attributes_data_of data) =>
                  if attributes_data_writable data
                  then change_object_property_cont st left_ptr name (fun prop cont =>
                    match get_object_property object name with
                    | Some _ => 
                      let attrs := attributes_data_of (attributes_data_value_update data new_val) in
                      cont st (Some attrs) new_val
                    | None => 
                      if object_extensible object
                      then let attrs := attributes_data_of (attributes_data_intro new_val true true true) in
                        cont st (Some attrs) new_val
                      else result_exception st (value_string "unextensible-shadow")
                    end)
                  else result_exception st (value_string "unwritable-field")
                | Some (attributes_accessor_of acc) =>
                    apply runs c st (attributes_accessor_set acc) (left_loc :: new_val :: nil)
                | None => 
                  if object_extensible object 
                  then change_object_property st left_ptr name (fun prop =>
                    let attrs := attributes_data_of (attributes_data_intro new_val true true true) in
                    (st, Some attrs, new_val))
                  else result_exception st (value_string "unextensible-set")
                end)))))))
. (* get_object_property object name *)

Definition eval_delete_field runs c st (left_expr right_expr : expr) : result :=
  if_eval_return runs c st left_expr (fun st left_loc =>
    if_eval_return runs c st right_expr (fun st right_loc =>
      assert_get_object_ptr left_loc (fun left_ptr =>
        assert_get_string right_loc (fun name =>
          assert_get_object_from_ptr st left_ptr (fun obj =>
            match get_object_property obj name with
            | Some attr => 
              if attributes_configurable attr 
              then result_value (st \(left_ptr := delete_object_property obj name)) value_true
              else result_exception st (value_string "unconfigurable-delete")
            | None => result_value st value_false
            end
  )))))
.

(* let (id = expr) body
* Evaluate expr, set it to a fresh location in the store, and bind this
* location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_let runs c st (id : string) (value_expr body_expr : expr) : result :=
  if_eval_return runs c st value_expr (fun st val =>
    runs_type_eval runs (c \(id := val)) st body_expr
  )
.

(* rec (id = expr) body
* Evaluate expr with a reference to itself, set it to a fresh location in the store,
* and bind this location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_rec runs c st (id : string) (value_expr body_expr : expr) : result :=
  match value_expr with
  | expr_lambda args body =>
    let v := add_closure c  (Some id) args body in
    runs_type_eval runs (c \(id := v)) st body_expr
  | _ => result_fail "rec with no lambda"
  end
.

(* func (args) { body }
* Capture the environment's name-to-location heap and return a closure. *)
Definition eval_lambda runs c st (args : list id) (body : expr) : result :=
  result_value st (add_closure c None args body)
.

(* f (args)
* If f is a closure and there are as many arguments as the arity of f,
* call f's body with the current store, with the name-to-location map
* modified this way: for all `var`,
* * if `var` is the name of one of the arguments, then `var` maps to
*   the location of the value computed when evaluating this argument
* * else, if `var` is the name of one of the variable in f's closure,
*   then `var` maps to the location associated with in the closure.
* * else, `var` is left unchanged (ie. if it was mapped to a location,
*   it still maps to this location; and if it did not map to anything,
*   it still does not map to anything). *)
Definition eval_app runs c st (f : expr) (args_expr : list expr) : result :=
  if_eval_return runs c st f (fun st f_loc =>
    eval_arg_list runs c st args_expr (fun st args =>
      apply runs c st f_loc args
  ))
.

Definition get_object_pattr obj s (pa : pattr) : resultof value :=
  match get_object_property obj s with
  | None => result_fail "Accessing nonexistent attribute"
  | Some prop =>
    match pa, prop with
    | pattr_enum, _ => result_some (value_bool (attributes_enumerable prop))

    | pattr_config, _ => result_some (value_bool (attributes_configurable prop))

    | pattr_writable, attributes_data_of data =>
      result_some (value_bool (attributes_data_writable data))
    | pattr_writable, attributes_accessor_of _ =>
      result_fail "Access #writable of accessor."

    | pattr_value, attributes_data_of data =>
      result_some (attributes_data_value data)
    | pattr_value, attributes_accessor_of _ =>
      result_fail "Access #value of accessor."

    | pattr_getter, attributes_accessor_of acc =>
      result_some (attributes_accessor_get acc)
    | pattr_getter, attributes_data_of _ =>
      result_fail "Access #getter of data."

    | pattr_setter, attributes_accessor_of acc =>
      result_some (attributes_accessor_set acc)
    | pattr_setter, attributes_data_of _ =>
      result_fail "Access #setter of data."
    end
  end
.

(* left[right<attr>] *)
Definition eval_get_attr runs c st left_expr right_expr attr :=
  if_eval_return runs c st left_expr (fun st left_ =>
    if_eval_return runs c st right_expr (fun st right_ =>
      assert_get_object st left_ (fun obj =>
        assert_get_string right_ (fun fieldname =>
          if_result_some (get_object_pattr obj fieldname attr) (fun v =>
            result_value st v
  )))))
.

Definition set_object_pattr obj s (pa : pattr) v : resultof object :=
  match get_object_property obj s with
  | None =>
    if object_extensible obj then 
      let oattr :=
        match pa with
        | pattr_getter => Some (attributes_accessor_of (attributes_accessor_intro v value_undefined false false))
        | pattr_setter => Some (attributes_accessor_of (attributes_accessor_intro value_undefined v false false))
        | pattr_value => Some (attributes_data_of (attributes_data_intro v false false false))
        | pattr_writable => LibOption.map (fun b => attributes_data_of (attributes_data_intro value_undefined b false false)) (value_to_bool v)
        | pattr_enum => LibOption.map (fun b => attributes_data_of (attributes_data_intro value_undefined false b false)) (value_to_bool v)
        | pattr_config => LibOption.map (fun b => attributes_data_of (attributes_data_intro value_undefined false false b)) (value_to_bool v)
        end in
      match oattr with
      | Some attr => result_some (set_object_property obj s attr)
      | None => result_fail "Invalid operation."
      end
    else result_fail "Object inextensible."
  | Some prop =>
    ifb attributes_pattr_writable prop pa then
    let oattr :=
      match pa, prop with
      | pattr_getter, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        Some (attributes_accessor_of (attributes_accessor_intro v se en co))
      | pattr_setter, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        Some (attributes_accessor_of (attributes_accessor_intro ge v en co))
      | pattr_enum, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        LibOption.map (fun b => attributes_accessor_of (attributes_accessor_intro ge se b co)) (value_to_bool v)
      | pattr_config, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        LibOption.map (fun b => attributes_accessor_of (attributes_accessor_intro ge se en b)) (value_to_bool v)
      | pattr_value, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        Some (attributes_data_of (attributes_data_intro v false en co))
      | pattr_writable, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
        LibOption.map (fun b => attributes_data_of (attributes_data_intro value_undefined b en co)) (value_to_bool v)
      | pattr_value, attributes_data_of (attributes_data_intro va wr en co) =>
        Some (attributes_data_of (attributes_data_intro v wr en co))
      | pattr_writable, attributes_data_of (attributes_data_intro va wr en co) =>
        LibOption.map (fun b => attributes_data_of (attributes_data_intro va b en co)) (value_to_bool v)
      | pattr_enum, attributes_data_of (attributes_data_intro va wr en co) =>
        LibOption.map (fun b => attributes_data_of (attributes_data_intro va wr b co)) (value_to_bool v)
      | pattr_config, attributes_data_of (attributes_data_intro va wr en co) =>
        LibOption.map (fun b => attributes_data_of (attributes_data_intro va wr en b)) (value_to_bool v)
      | pattr_getter, attributes_data_of (attributes_data_intro va wr en co) =>
        Some (attributes_accessor_of (attributes_accessor_intro v value_undefined en co))
      | pattr_setter, attributes_data_of (attributes_data_intro va wr en co) =>
        Some (attributes_accessor_of (attributes_accessor_intro value_undefined v en co))
      end in
      match oattr with
      | Some attr => result_some (set_object_property obj s attr)
      | None => result_fail "Invalid operation."
      end
    else result_fail "Attribute update not permitted"
  end
.

(* left[right<attr> = new_val] *)
Definition eval_set_attr runs c st left_expr right_expr attr new_val_expr :=
  if_eval_return runs c st left_expr (fun st left_ =>
    if_eval_return runs c st right_expr (fun st right_ =>
      if_eval_return runs c st new_val_expr (fun st new_val =>
        assert_get_object_ptr left_ (fun obj_ptr =>
          assert_get_string right_ (fun fieldname =>
            change_object_cont st obj_ptr (fun obj cont =>
              if_result_some (set_object_pattr obj fieldname attr new_val) (fun obj' =>
                cont st obj' new_val
  )))))))
.

Definition eval_get_obj_attr runs c st obj_expr oattr :=
  if_eval_return runs c st obj_expr (fun st obj_loc =>
    assert_get_object st obj_loc (fun obj =>
      result_value st (get_object_oattr obj oattr)))
.

Definition set_object_oattr_check obj oa v : resultof object :=
  let 'object_intro (oattrs_intro pr cl ex pv co) pp := obj in
  match oa with
  | oattr_proto =>
    ifb object_extensible obj then
    match v with
    | value_null
    | value_object _ => result_some (object_intro (oattrs_intro v cl ex pv co) pp)
    | _ => result_fail "Update proto failed"
    end
    else result_fail "Update proto on unextensible object"
  | oattr_extensible => 
    ifb object_extensible obj then
    match v with
    | value_bool b => result_some (object_intro (oattrs_intro pr cl b pv co) pp)
    | _ => result_fail "Update extensible failed"
    end
    else result_fail "Update extensible on unextensible object"
  | oattr_code => result_fail "Can't update code"
  | oattr_primval => result_some (object_intro (oattrs_intro pr cl ex v co) pp)
  | oattr_class => result_fail "Can't update klass"
  end
.

Definition eval_set_obj_attr runs c st obj_expr oattr attr :=
  if_eval_return runs c st obj_expr (fun st obj_loc =>
    if_eval_return runs c st attr (fun st v =>
      assert_get_object_ptr obj_loc (fun obj_ptr =>
        change_object_cont st obj_ptr (fun obj cont =>
          if_result_some (set_object_oattr_check obj oattr v) (fun obj' =>
            cont st obj' v))))).

Definition eval_own_field_names runs c st obj_expr : result :=
  if_eval_return runs c st obj_expr (fun st obj_loc =>
    assert_get_object st obj_loc (fun obj =>
      let (st, loc) := add_object st (make_prop_list obj)
      in result_value st loc
  ))
.

Definition eval_label runs c st (label : string) body : result :=
  if_eval_ter runs c st body (fun st res =>
    match res with
    | res_value ret => result_value st ret
    | res_exception exc => result_exception st exc
    | res_break b v =>
      if (decide(b = label)) then
        result_value st v
      else
        result_break st b v
    end
  )
.
Definition eval_break runs c st (label : string) body : result :=
  if_eval_return runs c st body (fun st ret =>
    result_break st label ret
  )
.
        
Definition eval_throw runs c st expr : result :=
  if_eval_return runs c st expr (fun st loc =>
    result_exception st loc
  )
.

Definition eval_trycatch runs c st body catch : result :=
  if_eval_ter runs c st body (fun st res =>
    match res with
    | res_exception exc =>
      if_eval_return runs c st catch (fun st catch =>
        apply runs c st catch (exc :: nil)
      )
    | r => result_res st r
    end
  )
.

Definition eval_tryfinally runs c st body fin : result :=
  if_eval_ter runs c st body (fun st res =>
    if_eval_return runs c st fin (fun st catch =>
      result_res st res
    ))
.

Definition eval_eval runs c st estr bindings :=
  if_eval_return runs c st estr (fun st v_estr =>
    if_eval_return runs c st bindings (fun st v_bindings =>
      assert_get_string v_estr (fun s =>
        assert_get_object st v_bindings (fun obj => 
          match desugar_expr s, ctx_of_obj obj with
          | Some e, Some c' => runs_type_eval runs c' st e          
          | None, _ => result_fail "Parse error"
          | _, None => result_fail "Invalid eval environment"
          end 
  ))))
.

Definition eval_op1 runs c st op e :=
    if_eval_return runs c st e (fun st v_loc =>
      if_result_some (unary_operator op st v_loc) (fun v_res => result_value st v_res)
    )
.

Definition eval_op2 runs c st op e1 e2 :=
    if_eval_return runs c st e1 (fun st v1_loc =>
      if_eval_return runs c st e2 (fun st v2_loc =>
        if_result_some (binary_operator op st v1_loc v2_loc) (fun v_res => result_value st v_res)
    ))
. 

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval runs c st (e : expr) : result :=
  let return_value := result_value st in
  match e with
  | expr_empty => return_value value_empty
  | expr_undefined => return_value value_undefined
  | expr_null => return_value value_null
  | expr_string s => return_value (value_string s)
  | expr_number n => return_value (value_number n)
  | expr_bool b => return_value (value_bool b)
  | expr_id s => eval_id runs c st s
  | expr_if e_cond e_true e_false => eval_if runs c st e_cond e_true e_false
  | expr_seq e1 e2 => eval_seq runs c st e1 e2
  | expr_jseq e1 e2 => eval_jseq runs c st e1 e2
  | expr_object attrs l => eval_object_decl runs c st attrs l
  | expr_get_field left_ right_ => eval_get_field runs c st left_ right_ 
  | expr_set_field left_ right_ new_val => eval_set_field runs c st left_ right_ new_val
  | expr_delete_field left_ right_ => eval_delete_field runs c st left_ right_
  | expr_let id value body => eval_let runs c st id value body
  | expr_recc id value body => eval_rec runs c st id value body
  | expr_lambda args body => eval_lambda runs c st args body
  | expr_app f args => eval_app runs c st f args
  | expr_get_attr attr left_ right_ => eval_get_attr runs c st left_ right_ attr
  | expr_set_attr attr left_ right_ newval => eval_set_attr runs c st left_ right_ attr newval
  | expr_get_obj_attr oattr obj => eval_get_obj_attr runs c st obj oattr
  | expr_set_obj_attr oattr obj attr => eval_set_obj_attr runs c st obj oattr attr
  | expr_own_field_names e => eval_own_field_names runs c st e
  | expr_op1 op e => eval_op1 runs c st op e
  | expr_op2 op e1 e2 => eval_op2 runs c st op e1 e2
  | expr_label l e => eval_label runs c st l e
  | expr_break l e => eval_break runs c st l e
  | expr_try_catch body catch => eval_trycatch runs c st body catch
  | expr_try_finally body fin => eval_tryfinally runs c st body fin
  | expr_throw e => eval_throw runs c st e
  | expr_eval e bindings => eval_eval runs c st e bindings
  | expr_hint _ e => runs_type_eval runs c st e
  | expr_dump => result_dump c st
  end
.

Definition runs_0 := {|
    runs_type_eval := fun c st _ => result_bottom
  |}
.

Definition runs_S runs := 
  let wrap {A : Type} (f : runs_type -> ctx -> store -> A) c st : A :=
    f runs c st
  in {|
    runs_type_eval := wrap eval
  |}
.

Definition suspend_runs fruns :=  {|
    runs_type_eval := fun c st e => runs_type_eval (fruns tt) c st e  
  |}  
.

Fixpoint runs max_step : runs_type :=
  match max_step with
  | 0 => runs_0
  | S max_step' => runs_S (runs max_step')
  end
.

Fixpoint lazy_runs max_step : runs_type :=
  match max_step with
  | 0 => runs_0
  | S max_step' => runs_S (suspend_runs (fun _ => lazy_runs max_step'))
  end
.

Definition runs_eval n := runs_type_eval (lazy_runs n).
