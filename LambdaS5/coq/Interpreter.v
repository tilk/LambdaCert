Require Import List.
Require Import Coq.Strings.String.
Require Import Syntax.
Require Import Values.
Require Import Context.
Require Import Monads.
Require Import Store.
Require Import Utils.
Require Import Operators.
Require Import LibHeap.
Require Import LibStream.
Require Import JsNumber.
Open Scope list_scope.
Open Scope string_scope.

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


Implicit Type runs : runs_type.
Implicit Type store : store. (* TODO search and destroy *)
Implicit Type st : store.
Implicit Type c : ctx.

(* Monadic operations for interpreting *)

(* Evaluate an expression, and calls the continuation with
* the new store and the Context.result of the evaluation. *)
Definition eval_cont {A : Type} runs c st e (cont : result -> resultof A) : resultof A :=
  cont (Context.runs_type_eval runs c st e).

(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate runs c st e : result :=
  eval_cont runs c st e (fun res => res)
.

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
Definition eval_arg_list_aux runs c (arg_expr : expr) (cont : Store.store -> list value -> result) st (l : list value) : result :=
  if_eval_return runs c st arg_expr (fun st arg => cont st (arg::l)) 
.

Definition eval_arg_list runs c st (args_expr : list expr) (cont : Store.store -> list value -> result) : result :=
  List.fold_right (eval_arg_list_aux runs c) (fun st args => cont st (rev args)) args_expr st nil
.

Definition apply runs c st (f_loc : value) (args : list value) : result :=
  let res := get_closure st f_loc in
  if_result_some res (fun f =>
      match f with
      | value_closure _id env args_names body =>
        let (st, args_locs) := Store.add_values st args in
        let res := add_parameters env args_names args_locs in
        if_result_some res (fun vh =>
          eval_cont_terminate runs vh st body)
      | _ => result_fail "Expected Closure but did not get one."
      end
  )
.


(********* Evaluators ********)

(* a lonely identifier.
* Fetch the associated value location and return it. *)
Definition eval_id runs c st (name : string) : result :=
  assert_get_loc c name (fun loc =>
    assert_deref st loc (fun v => result_value st v))
.


(* if e_cond e_true else e_false.
* Evaluate the condition and get the associated value, then evaluate
* e_true or e_false depending on the value. *)
Definition eval_if runs c store (e_cond e_true e_false : expr) : result :=
  if_eval_return runs c store e_cond (fun store v =>
    assert_get_bool v (fun b =>
      if b
      then eval_cont_terminate runs c store e_true
      else eval_cont_terminate runs c store e_false
  ))
.

(* e1 ; e2.
* Evaluate e1, then e2, and return the value location returned by e2. *)
Definition eval_seq runs c st (e1 e2 : expr) : result :=
  if_eval_return runs c st e1 (fun st v => eval_cont_terminate runs c st e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux runs c store (l : list (string * property)) (acc : object_properties) (cont : Store.store -> object_properties -> result) {struct l} : result :=
  match l with
  | nil => cont store acc
  | (name, property_data (data_intro value_expr writable_expr enumerable_expr configurable_expr)) :: tail =>
    if_eval_return runs c store configurable_expr (fun store configurable_v =>
      if_eval_return runs c store enumerable_expr (fun store enumerable_v =>
        if_eval_return runs c store value_expr (fun store value_v =>
          if_eval_return runs c store writable_expr (fun store writable_v =>
            assert_get_bool configurable_v (fun configurable =>
              assert_get_bool enumerable_v (fun enumerable => 
                assert_get_bool writable_v (fun writable => 
                  eval_object_properties_aux runs c store tail (Heap.write acc name (
                    attributes_data_of {|
                      attributes_data_value := value_v;
                      attributes_data_writable := writable;
                      attributes_data_enumerable := enumerable;
                      attributes_data_configurable := configurable |}
                    )) cont))))))) 
  | (name, property_accessor (accessor_intro getter_expr setter_expr enumerable_expr configurable_expr)) :: tail =>
    if_eval_return runs c store configurable_expr (fun store configurable_v =>
      if_eval_return runs c store enumerable_expr (fun store enumerable_v =>
        if_eval_return runs c store getter_expr (fun store getter_v =>
          if_eval_return runs c store setter_expr (fun store setter_v =>
            assert_get_bool configurable_v (fun configurable =>
              assert_get_bool enumerable_v (fun enumerable => 
                eval_object_properties_aux runs c store tail (Heap.write acc name (
                  attributes_accessor_of {|
                    attributes_accessor_get := getter_v;
                    attributes_accessor_set := setter_v;
                    attributes_accessor_enumerable := enumerable;
                    attributes_accessor_configurable := configurable |}
                  )) cont))))))
  end
.
(* Reads a list of syntax trees of properties and converts it to a heap
* bindable to an object. *)
Definition eval_object_properties runs c store (l : list (string * property)) (cont : Store.store -> object_properties -> result) : result :=
  eval_object_properties_aux runs c store l Heap.empty cont
.

(* { [ attrs ] props }
* Evaluate the primval attribute (if any), then the proto attribute (defaults
* to Undefined), then properties. Finally, allocate a new object with the
* computed values. *)
Definition eval_object_decl runs c store (attrs : objattrs) (l : list (string * property)) : result :=
  let 'objattrs_intro class_expr extensible_expr prototype_expr code_expr primval_expr := attrs in
    (* Order of evaluation as in the paper: *)
    if_eval_return runs c store class_expr (fun store class_v =>
      if_eval_return runs c store extensible_expr (fun store extensible_v =>
        if_eval_return runs c store prototype_expr (fun store prototype_v =>
          if_eval_return runs c store code_expr (fun store code_v =>
            if_eval_return runs c store primval_expr (fun store primval_v =>
              assert_get_string class_v (fun class => assert_get_bool extensible_v (fun extensible =>
                eval_object_properties runs c store l (fun store props =>
                  let (store, loc) := Store.add_object store {|
                    object_proto := prototype_v;
                    object_class := class;
                    object_extensible := extensible;
                    object_prim_value := primval_v;
                    object_properties_ := props;
                    object_code := code_v |}
                  in result_value store loc
          ))))))))
.

(* left[right, arg].
* Evaluate left, then right, then the arguments.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, return it; and if it is an “accessor field”, call
* the getter with the arguments.
* Note the arguments are evaluated even if they are not passed to any
* function. *)
Definition eval_get_field runs c store (left_expr right_expr arg_expr : expr) : result :=
  if_eval_return runs c store left_expr (fun store left_loc =>
    if_eval_return runs c store right_expr (fun store right_loc =>
      if_eval_return runs c store arg_expr (fun store arg_loc =>
        assert_get_object_ptr left_loc (fun ptr =>
          assert_get_string right_loc (fun name =>
            let res := get_property store ptr name in
            if_result_some res (fun ret =>
              match ret with
              | Some (attributes_data_of data) => result_value store (attributes_data_value data)
              | Some (attributes_accessor_of (attributes_accessor_intro getter _ _ _)) =>
                  apply runs c store getter (left_loc :: (arg_loc :: nil))
              | None =>
                  result_value store value_undefined
              end
  ))))))
.

(* left[right, arg] = new_val
* Evaluate left, then right, then the arguments, then the new_val.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, set it to the `new_val` and return the `new_val`;
* and if it is an “accessor field”, call the getter with the arguments,
* with the `new_val` prepended to the list.
* Note the arguments are evaluated even if they are not passed to any
* function. *)
Definition eval_set_field runs c store (left_expr right_expr new_val_expr arg_expr : expr) : result :=
  if_eval_return runs c store left_expr (fun store left_loc =>
    if_eval_return runs c store right_expr (fun store right_loc =>
      if_eval_return runs c store new_val_expr (fun store new_val =>
        if_eval_return runs c store arg_expr (fun store arg_loc =>
          assert_get_object_ptr left_loc (fun left_ptr =>
            assert_get_string right_loc (fun name =>
              if_result_some (get_property store left_ptr name) (fun ret =>
                match ret with
                | Some (attributes_data_of data) =>
                  if attributes_data_writable data
                  then change_object_property_cont store left_ptr name (fun prop cont =>
                    assert_get_object_from_ptr store left_ptr (fun object =>
                      match get_object_property object name with
                      | Some _ => 
                        let attrs := attributes_data_of (attributes_data_value_update data new_val) in
                        cont store (Some attrs) new_val
                      | None => 
                        let attrs := attributes_data_of (attributes_data_intro new_val true true true) in
                        cont store (Some attrs) new_val
                      end))
                  else result_exception store (value_string "unwritable-field")
                | Some (attributes_accessor_of (attributes_accessor_intro _ setter _ _)) =>
                    (* Note: pattr_setters don't get the new value. See https://github.com/brownplt/LambdaS5/issues/45 *)
                    apply runs c store setter (left_loc :: arg_loc :: nil)
                | None => 
                  assert_get_object_from_ptr store left_ptr (fun object =>
                    if object_extensible object 
                    then change_object_property store left_ptr name (fun prop =>
                      let attrs := attributes_data_of (attributes_data_intro new_val true true true) in
                      (store, Some attrs, new_val))
                    else result_value store value_undefined)
                end)))))))
. (* get_object_property object name *)

Definition eval_deletefield runs c store (left_expr right_expr : expr) : result :=
  if_eval_return runs c store left_expr (fun store left_loc =>
    if_eval_return runs c store right_expr (fun store right_loc =>
      assert_get_object_ptr left_loc (fun left_ptr =>
        assert_get_string right_loc (fun name =>
          change_object_cont store left_ptr (fun obj cont =>
            match get_object_property obj name with
            | Some attr => 
              if attributes_configurable attr 
              then cont store (delete_object_property obj name) value_true
              else result_exception store (value_string "unconfigurable-delete")
            | None => cont store obj value_false
            end
  )))))
.

(* let (id = expr) body
* Evaluate expr, set it to a fresh location in the store, and bind this
* location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_let runs c st (id : string) (value_expr body_expr : expr) : result :=
  if_eval_return runs c st value_expr (fun st value =>
      let (c, st) := Store.add_named_value c st id value in
        eval_cont_terminate runs c st body_expr
  )
.

(* rec (id = expr) body
* Evaluate expr with a reference to itself, set it to a fresh location in the store,
* and bind this location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_rec runs c store (id : string) (value_expr body_expr : expr) : result :=
  match Store.add_named_value_loc c store id value_undefined with
  | (c, store, self_loc) =>
    if_eval_return runs c store value_expr (fun store value =>
      let store := Store.add_value_at_location store self_loc value in
        eval_cont_terminate runs c store body_expr
    )
  end
.

(* name := expr
* Evaluate expr, and set it at the location bound to `name`. Fail if `name`
* is not associated with a location in the store. *)
Definition eval_setbang runs c store (name : string) (expr : expr) : result :=
  if_eval_return runs c store expr (fun store value =>
    assert_get_loc c name (fun loc =>
      result_value (Store.add_value_at_location store loc value) value
  ))
.

(* func (args) { body }
* Capture the environment's name-to-location heap and return a closure. *)
Definition eval_lambda runs c st (args : list id) (body : expr) : result :=
  let (store, loc) := Store.add_closure c st args body in
  result_value store loc
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
Definition eval_app runs c store (f : expr) (args_expr : list expr) : result :=
  if_eval_return runs c store f (fun store f_loc =>
    eval_arg_list runs c store args_expr (fun store args =>
      apply runs c store f_loc args
  ))
.


(* left[right<attr>] *)
Definition eval_getattr runs c store left_expr right_expr attr :=
  if_eval_return runs c store left_expr (fun store left_ =>
    if_eval_return runs c store right_expr (fun store right_ =>
      assert_get_object store left_ (fun obj =>
        assert_get_string right_ (fun fieldname =>
          if_result_some (get_object_pattr obj fieldname attr) (fun v =>
            result_value store v
  )))))
.

(* left[right<attr> = new_val] *)
Definition eval_setattr runs c store left_expr right_expr attr new_val_expr :=
  if_eval_return runs c store left_expr (fun store left_ =>
    if_eval_return runs c store right_expr (fun store right_ =>
      if_eval_return runs c store new_val_expr (fun store new_val =>
        assert_get_object_ptr left_ (fun obj_ptr =>
          assert_get_string right_ (fun fieldname =>
            change_object_cont store obj_ptr (fun obj cont =>
              if_result_some (set_object_pattr obj fieldname attr new_val) (fun obj' =>
                cont store obj' new_val
  )))))))
.

Definition eval_getobjattr runs c store obj_expr oattr :=
  if_eval_return runs c store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      result_value store (get_object_oattr obj oattr)))
.

Definition eval_setobjattr runs c store obj_expr oattr attr :=
  if_eval_return runs c store obj_expr (fun store obj_loc =>
    if_eval_return runs c store attr (fun store v =>
      assert_get_object_ptr obj_loc (fun obj_ptr =>
        change_object_cont store obj_ptr (fun obj cont =>
          if_result_some (set_object_oattr obj oattr v) (fun obj' =>
            cont store obj' v)))))
.

Definition eval_ownfieldnames runs c store obj_expr : result :=
  if_eval_return runs c store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      let (store, loc) := Store.add_object store (make_prop_list obj)
      in result_value store loc
  ))
.

Definition eval_label runs c store (label : string) body : result :=
  if_eval_ter runs c store body (fun store res =>
    match res with
    | res_value ret => result_value store ret
    | res_exception exc => result_exception store exc
    | res_break b v =>
      if (decide(b = label)) then
        result_value store v
      else
        result_break store b v
    end
  )
.
Definition eval_break runs c store (label : string) body : result :=
  if_eval_return runs c store body (fun store ret =>
    result_break store label ret
  )
.
        
Definition eval_throw runs c store expr : result :=
  if_eval_return runs c store expr (fun store loc =>
    result_exception store loc
  )
.

Definition eval_trycatch runs c store body catch : result :=
  if_eval_ter runs c store body (fun store res =>
    match res with
    | res_exception exc =>
      if_eval_return runs c store catch (fun store catch =>
        apply runs c store catch (exc :: nil)
      )
    | r => result_res store r
    end
  )
.

Definition eval_tryfinally runs c store body fin : result :=
  if_eval_ter runs c store body (fun store res =>
    match res with
    | res_value x => eval_cont_terminate runs c store fin
    | r =>
      if_eval_return runs c store fin (fun store catch =>
        result_res store r
      )
    end
  )
.

Definition eval_eval runs c store estr bindings :=
  if_eval_return runs c store estr (fun store v_estr =>
    if_eval_return runs c store bindings (fun store v_bindings =>
      assert_get_string v_estr (fun s =>
        assert_get_object store v_bindings (fun obj => 
          match desugar_expr s, Store.envstore_of_obj store obj with
          | Some e, Some (c', store) => runs_type_eval runs c' store e          
          | None, _ => result_fail "Parse error"
          | _, None => result_fail "Invalid eval environment"
          end 
  ))))
.

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval runs c store (e : expr) : result :=
  let return_value := result_value store in
  match e with
  | expr_undefined => return_value value_undefined
  | expr_null => return_value value_null
  | expr_string s => return_value (value_string s)
  | expr_number n => return_value (value_number n)
  | expr_true => return_value value_true
  | expr_false => return_value value_false
  | expr_id s => eval_id runs c store s
  | expr_if e_cond e_true e_false => eval_if runs c store e_cond e_true e_false
  | expr_seq e1 e2 => eval_seq runs c store e1 e2
  | expr_object attrs l => eval_object_decl runs c store attrs l
  | expr_get_field left_ right_ attributes => eval_get_field runs c store left_ right_ attributes
  | expr_set_field left_ right_ new_val attributes => eval_set_field runs c store left_ right_ new_val attributes
  | expr_delete_field left_ right_ => eval_deletefield runs c store left_ right_
  | expr_let id value body => eval_let runs c store id value body
  | expr_recc id value body => eval_rec runs c store id value body
  | expr_set_bang id expr => eval_setbang runs c store id expr
  | expr_lambda args body => eval_lambda runs c store args body
  | expr_app f args => eval_app runs c store f args
  | expr_get_attr attr left_ right_ => eval_getattr runs c store left_ right_ attr
  | expr_set_attr attr left_ right_ newval => eval_setattr runs c store left_ right_ attr newval
  | expr_get_obj_attr oattr obj => eval_getobjattr runs c store obj oattr
  | expr_set_obj_attr oattr obj attr => eval_setobjattr runs c store obj oattr attr
  | expr_own_field_names e => eval_ownfieldnames runs c store e
  | expr_op1 op e =>
    if_eval_return runs c store e (fun store v_loc =>
      if_result_some (Operators.unary op store v_loc) (fun v_res => result_value store v_res)
    )
  | expr_op2 op e1 e2 =>
    if_eval_return runs c store e1 (fun store v1_loc =>
      if_eval_return runs c store e2 (fun store v2_loc =>
        if_result_some (Operators.binary op store v1_loc v2_loc) (fun v_res => result_value store v_res)
    ))
  | expr_label l e => eval_label runs c store l e
  | expr_break l e => eval_break runs c store l e
  | expr_try_catch body catch => eval_trycatch runs c store body catch
  | expr_try_finally body fin => eval_tryfinally runs c store body fin
  | expr_throw e => eval_throw runs c store e
  | expr_eval e bindings => eval_eval runs c store e bindings
  | expr_hint _ e => eval_cont_terminate runs c store e
  | expr_dump => result_dump c store
  end
.

Definition runs_0 := {|
    runs_type_eval := fun c store _ => result_bottom
  |}
.

Definition runs_S runs := 
  let wrap {A : Type} (f : runs_type -> ctx -> Store.store -> A) c st : A :=
    f runs c st
  in {|
    runs_type_eval := wrap eval
  |}
.

Fixpoint runs max_step : runs_type :=
  match max_step with
  | 0 => runs_0
  | S max_step' => runs_S (runs max_step')
  end.

Definition runs_eval n := runs_type_eval (runs n).
