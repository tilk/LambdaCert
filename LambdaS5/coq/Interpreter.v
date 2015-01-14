Require Import List.
Require Import Coq.Strings.String.
Require Import Syntax.
Require Import Values.
Require Import Context.
Require Import Monads.
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
Implicit Type store : Store.store.


(****** Closures handling ******)

(* Evaluates all arguments, passing the store from one to the next. *)
Definition eval_arg_list_aux runs (arg_expr : expr) (cont : Store.store -> list value -> result) store (l : list value) : result :=
  if_eval_return runs store arg_expr (fun store arg => cont store (arg::l)) 
.

Definition eval_arg_list runs store (args_expr : list expr) (cont : Store.store -> list value -> result) : result :=
  List.fold_right (eval_arg_list_aux runs) (fun store args => cont store (rev args)) args_expr store nil
.

(* TODO: simplify these definitions *)

Definition make_app_loc_heap (closure_env : loc_heap_type) (args_name : list id) (args : list value_loc) : option loc_heap_type :=
  match Utils.zip_left args_name args with
  | Some args_heap =>
    Some (Utils.concat_list_heap
      args_heap
      closure_env
    )
  | None => None
  end
.

Definition make_app_store runs store (closure_env : loc_heap_type) (args_name : list id) (args : list value_loc) : resultof Store.store :=
  match (make_app_loc_heap closure_env args_name args) with
  | Some new_loc_heap =>
    result_some (Store.replace_loc_heap store new_loc_heap) 
  | None => result_fail "Arity mismatch"
  end
.

Definition apply runs st (f_loc : value) (args : list value) : result :=
  let res := get_closure st f_loc in
  if_result_some res (fun f =>
      match f with
      | value_closure id env args_names body =>
        let (store, args_locs) := Store.add_values st args in
        let res := make_app_store runs store env args_names args_locs in
        if_result_some res (fun inner_store =>
          eval_cont runs inner_store body (fun res =>
            if_out_ter res (fun inner_store res =>
              result_some (out_ter (Store.replace_loc_heap inner_store (Store.loc_heap store)) res)
        )))
      | _ => result_fail "Expected Closure but did not get one."
      end
  )
.


(********* Evaluators ********)

(* a lonely identifier.
* Fetch the associated value location and return it. *)
Definition eval_id runs store (name : string) : result :=
  match (Store.get_loc store name) with
  | Some loc => assert_deref store loc (fun v => result_value store v)
  | None => result_fail "ReferenceError"
  end
.


(* if e_cond e_true else e_false.
* Evaluate the condition and get the associated value, then evaluate
* e_true or e_false depending on the value. *)
Definition eval_if runs store (e_cond e_true e_false : expr) : result :=
  if_eval_return runs store e_cond (fun store v =>
    match v with
    | value_true => eval_cont_terminate runs store e_true
    | value_false => eval_cont_terminate runs store e_false
    | _ => result_fail "If on non-boolean value" (* as in the semantics *)
    end
  )
.

(* e1 ; e2.
* Evaluate e1, then e2, and return the value location returned by e2. *)
Definition eval_seq runs store (e1 e2 : expr) : result :=
  if_eval_return runs store e1 (fun store v => eval_cont_terminate runs store e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux runs store (l : list (string * property)) (acc : object_properties) (cont : Store.store -> object_properties -> result) : result :=
  match l with
  | nil => cont store acc
  | (name, property_data (data_intro value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store value_expr (fun store value_loc =>
      eval_object_properties_aux runs store tail (Heap.write acc name (
        attributes_data_of {|
            attributes_data_value := value_loc;
            attributes_data_writable := writable;
            attributes_data_enumerable := enumerable;
            attributes_data_configurable := configurable |}
      )) cont) 
  | (name, property_accessor (accessor_intro getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store getter_expr (fun store getter_loc =>
      if_eval_return runs store setter_expr (fun store setter_loc =>
        eval_object_properties_aux runs store tail (Heap.write acc name (
           attributes_accessor_of {|
              attributes_accessor_get := getter_loc;
              attributes_accessor_set := setter_loc;
              attributes_accessor_enumerable := enumerable;
              attributes_accessor_configurable := configurable |}
    )) cont))
  end
.
(* Reads a list of syntax trees of properties and converts it to a heap
* bindable to an object. *)
Definition eval_object_properties runs store (l : list (string * property)) (cont : Store.store -> object_properties -> result) : result :=
  eval_object_properties_aux runs store l Heap.empty cont
.

(* { [ attrs ] props }
* Evaluate the primval attribute (if any), then the proto attribute (defaults
* to Undefined), then properties. Finally, allocate a new object with the
* computed values. *)
Definition eval_object_decl runs store (attrs : objattrs) (l : list (string * property)) : result :=

  match attrs with
  | objattrs_intro primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_some_eval_return_else_none runs store primval_expr (fun store primval_loc =>
      if_some_eval_else_default runs store prototype_expr value_undefined (fun store prototype_loc =>
        if_some_eval_return_else_none runs store code_expr (fun store code =>
          eval_object_properties runs store l (fun store props =>
            let (store, loc) := Store.add_object store {|
                object_proto := prototype_loc;
                object_class := class;
                object_extensible := extensible;
                object_prim_value := primval_loc;
                object_properties_ := props;
                object_code := code |}
            in result_value store loc
          ))))
  end
.

(* left[right, arg].
* Evaluate left, then right, then the arguments.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, return it; and if it is an “accessor field”, call
* the getter with the arguments.
* Note the arguments are evaluated even if they are not passed to any
* function. *)
Definition eval_get_field runs store (left_expr right_expr arg_expr : expr) : result :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      if_eval_return runs store arg_expr (fun store arg_loc =>
        assert_get_object store left_loc (fun object =>
          assert_get_string right_loc (fun name =>
            let res := get_property store left_loc name in
            if_result_some res (fun ret =>
              match ret with
              | Some (attributes_data_of data) => result_value store (attributes_data_value data)
              | Some (attributes_accessor_of (attributes_accessor_intro getter _ _ _)) =>
                  apply runs store getter (left_loc :: (arg_loc :: nil))
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
Definition eval_set_field runs store (left_expr right_expr new_val_expr arg_expr : expr) : result :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      if_eval_return runs store new_val_expr (fun store new_val =>
        if_eval_return runs store arg_expr (fun store arg_loc =>
          assert_get_object_ptr left_loc (fun left_ptr =>
            assert_get_object_from_ptr store left_ptr (fun object =>
              assert_get_string right_loc (fun name =>
                match (get_object_property object name) with
                | Some (attributes_data_of (attributes_data_intro _ w e c)) =>
                  update_object_property store left_ptr name (fun prop =>
                    let attrs := attributes_data_of (attributes_data_intro new_val w e c) in
                    (store, Some attrs, new_val)
                  )
                | Some (attributes_accessor_of (attributes_accessor_intro _ setter _ _)) =>
                    (* Note: pattr_setters don't get the new value. See https://github.com/brownplt/LambdaS5/issues/45 *)
                    apply runs store setter (left_loc :: (arg_loc :: nil))
                | None => 
                  update_object_property store left_ptr name (fun prop =>
                    let attrs := attributes_data_of (attributes_data_intro new_val true true true) in
                    (store, Some attrs, new_val)
                  )
                end)))))))
.

Definition eval_deletefield runs store (left_expr right_expr : expr) : result :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      assert_get_object_ptr left_loc (fun left_ptr =>
        assert_get_string right_loc (fun name =>
          update_object store left_ptr (fun obj =>
            match obj with
            | object_intro v c e p props code =>
              (store, object_intro v c e p (Heap.rem props name) code, value_true)
            end
  )))))
.

(* let (id = expr) body
* Evaluate expr, set it to a fresh location in the store, and bind this
* location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_let runs store (id : string) (value_expr body_expr : expr) : result :=
  if_eval_return runs store value_expr (fun store value =>
      let store := Store.add_named_value store id value in
        eval_cont_terminate runs store body_expr
  )
.

(* rec (id = expr) body
* Evaluate expr with a reference to itself, set it to a fresh location in the store,
* and bind this location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_rec runs store (id : string) (value_expr body_expr : expr) : result :=
  let (store, self_loc) := Store.add_named_value_loc store id value_undefined in
  if_eval_return runs store value_expr (fun store value =>
      let store := Store.add_value_at_location store self_loc value in
        eval_cont_terminate runs store body_expr
  )
.

(* name := expr
* Evaluate expr, and set it at the location bound to `name`. Fail if `name`
* is not associated with a location in the store. *)
Definition eval_setbang runs store (name : string) (expr : expr) : result :=
  if_eval_return runs store expr (fun store value =>
      match (Store.get_loc store name) with
      | Some loc => result_value (Store.add_value_at_location store loc value) value
      | None => raise_exception store "ReferenceError"
      end
  )
.

(* func (args) { body }
* Capture the environment's name-to-location heap and return a closure. *)
Definition eval_lambda runs store (args : list id) (body : expr) : result :=
  let env := Store.loc_heap store in
  let (store, loc) := (Store.add_closure store env args body) in
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
(* TODO: fix context handling so variables are actually local. *)
Definition eval_app runs store (f : expr) (args_expr : list expr) : result :=
  if_eval_return runs store f (fun store f_loc =>
    eval_arg_list runs store args_expr (fun store args =>
      apply runs store f_loc args
  ))
.

Definition get_property_attribute store (oprop : option attributes) (attr : pattr) : result :=
  match oprop with
  | None => result_value store value_undefined
  | Some prop =>
    match (attr, prop) with
    | (pattr_config,     attributes_data_of (attributes_data_intro      _ _ _ config))
    | (pattr_config, attributes_accessor_of (attributes_accessor_intro _ _ _ config)) =>
      return_bool store config

    | (pattr_enum,     attributes_data_of (attributes_data_intro     _ _ enum _))
    | (pattr_enum, attributes_accessor_of (attributes_accessor_intro _ _ enum _)) =>
      return_bool store enum

    | (pattr_writable, attributes_data_of (attributes_data_intro _ writable _ _)) =>
      return_bool store writable
    | (pattr_writable, attributes_accessor_of _) =>
      result_fail "Access #writable of accessor."

    | (pattr_value, attributes_data_of (attributes_data_intro value _ _ _)) =>
      result_value store value
    | (pattr_value, attributes_accessor_of _) =>
      result_fail "Access #value of accessor."

    | (pattr_getter, attributes_accessor_of (attributes_accessor_intro getter _ _ _)) =>
      result_value store getter
    | (pattr_getter, attributes_data_of _) =>
      result_fail "Access #getter of data."

    | (pattr_setter, attributes_accessor_of (attributes_accessor_intro _ setter _ _)) =>
      result_value store setter
    | (pattr_setter, attributes_data_of _) =>
      result_fail "Access #setter of data."
    end
  end
.

(* left[right<attr>] *)
Definition eval_getattr runs store left_expr right_expr attr :=
  if_eval_return runs store left_expr (fun store left_ =>
    if_eval_return runs store right_expr (fun store right_ =>
      assert_get_object store left_ (fun obj =>
        assert_get_string right_ (fun fieldname =>
          get_property_attribute store (get_object_property obj fieldname) attr 
  ))))
.

Definition set_property_attribute store (oprop : option attributes) (attr : pattr) (new_val : value) (cont : Store.store -> option attributes -> value -> result) : result :=
  (* Some abbreviations: *)
  let aai := attributes_accessor_intro in
  let adi := attributes_data_intro in
  let aao := attributes_accessor_of in
  let ado := attributes_data_of in
  let raao := fun x => cont store (Some (aao x)) value_true in
  let rado := fun x => cont store (Some (ado x)) value_true in
  let getbool := assert_get_bool new_val in
  match oprop with
  | None =>
    match attr with
    | pattr_getter => raao (aai new_val value_undefined false false)
    | pattr_setter => raao (aai value_undefined new_val false false)
    | pattr_value => rado (adi new_val false false false)
    | pattr_writable => getbool (fun b => rado (adi value_undefined b false false))
    | pattr_enum => getbool (fun b => rado (adi value_undefined false b true))
    | pattr_config => getbool (fun b => rado (adi value_undefined false true b))
    end
  | Some prop =>
    match (attr, prop) with
    (* Set #writable of data when #writable is true *)
    | (pattr_writable, attributes_data_of (attributes_data_intro val true enum config)) =>
        getbool (fun b =>      rado (attributes_data_intro val b    enum config))
    (* Set #writable of data when #configurable is true *)
    | (pattr_writable, attributes_data_of (attributes_data_intro val writ enum true)) =>
        getbool (fun b =>      rado (attributes_data_intro val b    enum true))
    (* Set #value of data when #writable is true *)
    | (pattr_value, attributes_data_of (attributes_data_intro _       true enum config)) =>
                            rado (attributes_data_intro new_val true enum config)
    (* Set #setter when #configurable is true *)
    | (pattr_setter,     attributes_data_of (attributes_data_intro     _      _       enum true)) =>
                                 raao (attributes_accessor_intro value_undefined  new_val enum true)
    | (pattr_setter, attributes_accessor_of (attributes_accessor_intro get _       enum true)) =>
                                 raao (attributes_accessor_intro get new_val enum true)
    (* Set #getter when #configurable is true *)
    | (pattr_getter,     attributes_data_of (attributes_data_intro     _       _     enum true)) =>
                                 raao (attributes_accessor_intro new_val value_undefined enum true)
    | (pattr_getter, attributes_accessor_of (attributes_accessor_intro _       set enum true)) =>
                                 raao (attributes_accessor_intro new_val set enum true)
    (* Set #value of accessor when #configurable is true *)
    | (pattr_value,  attributes_accessor_of (attributes_accessor_intro _       _     enum true)) =>
                                 rado (attributes_data_intro     new_val false enum true)
    (* Set #writable of accessor when #configurable is true *)
    | (pattr_writable, attributes_accessor_of (attributes_accessor_intro _     _ enum true)) =>
        getbool (fun b =>          rado (attributes_data_intro     value_undefined b enum true))
    (* Set #enumerable when #configurable is true *)
    | (pattr_enum,     attributes_data_of (attributes_data_intro     val writ _ true)) =>
        getbool (fun b =>      rado (attributes_data_intro     val writ b true))
    | (pattr_enum, attributes_accessor_of (attributes_accessor_intro get set  _ true)) =>
        getbool (fun b =>      raao (attributes_accessor_intro get set  b true))
    (* Set #configurable when #configurable is true *)
    | (pattr_config,     attributes_data_of (attributes_data_intro     val writ enum true)) =>
        getbool (fun b =>        rado (attributes_data_intro     val writ enum b   ))
    | (pattr_config, attributes_accessor_of (attributes_accessor_intro get set  enum true)) =>
        getbool (fun b =>        raao (attributes_accessor_intro get set  enum b   ))
    (* Set #configurable to false when #configurable is false *)
    | (pattr_config,     attributes_data_of (attributes_data_intro     _ _ _ false))
    | (pattr_config, attributes_accessor_of (attributes_accessor_intro _ _ _ false)) =>
      getbool (fun b =>
        if b then result_fail "Set #configurable to true while #configurable is false"
        else cont store oprop value_true (* unchanged *)
      )
    | (pattr_value, _) => result_fail "Invalid #value set."
    | (pattr_writable, _) => result_fail "Invalid #writable set."
    | (pattr_getter, _) => result_fail "Invalid #getter set."
    | (pattr_setter, _) => result_fail "Invalid #setter set."
    | (pattr_enum,     attributes_data_of (attributes_data_intro     _ _ _ false)) =>
        result_fail "Invalid #enum set for data property."
    | (pattr_enum, attributes_accessor_of (attributes_accessor_intro _ _ _ false)) =>
        result_fail "Invalid #enum set for accessor property."
    end
  end
.

(* left[right<attr> = new_val] *)
Definition eval_setattr runs store left_expr right_expr attr new_val_expr :=
  if_eval_return runs store left_expr (fun store left_ =>
    if_eval_return runs store right_expr (fun store right_ =>
      if_eval_return runs store new_val_expr (fun store new_val =>
        assert_get_object_ptr left_ (fun obj_ptr =>
          assert_get_string right_ (fun fieldname =>
            update_object_property_cont store obj_ptr fieldname (fun oprop =>
              set_property_attribute store oprop attr new_val
  ))))))
.

Definition eval_getobjattr runs store obj_expr oattr :=
  if_eval_return runs store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      match oattr with
      | oattr_proto => result_value store (object_proto obj)
      | oattr_extensible => return_bool store (object_extensible obj)
      | oattr_code =>
        match (object_code obj) with
        | Some code => result_value store code
        | None => result_value store value_null
        end
      | oattr_primval =>
        match (object_prim_value obj) with
        | Some v => result_value store v
        | None => result_fail "primval attribute is None."
        end
      | oattr_class => result_value store (value_string (object_class obj))
      end
  ))
.

Definition make_prop_list_aux (left : nat * Store.store * object_properties) (val : value) : nat * Store.store * object_properties :=
  match left with
  | (nb_entries, store, attrs) =>
    let attr := attributes_data_of (attributes_data_intro val false false false) in
    (S nb_entries, store, Heap.write attrs (Utils.string_of_nat nb_entries) attr)
  end
.
Definition make_prop_heap runs store (vals : list value) : Store.store * object_properties :=
  match List.fold_left make_prop_list_aux vals (0, store, Heap.empty) with
  | (nb_entries, store, attrs) =>
    let length := value_number (Utils.make_number nb_entries) in
    let length_attr := attributes_data_of (attributes_data_intro length false false false) in
    (store, Heap.write attrs "length" length_attr)
  end
.
Definition left_to_string {X : Type} (x : (string * X)) : value :=
  let (k, v) := x in value_string k
.
Definition eval_ownfieldnames runs store obj_expr : result :=
  if_eval_return runs store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      let props := (Heap.to_list (object_properties_ obj)) in
      let props := (List.map left_to_string props) in
      match (make_prop_heap runs store props) with
      | (store, props) =>
        match default_objattrs with
        | objattrs_intro primval_expr code_expr prototype_expr class extensible =>
          (* Following the order in the original implementation: *)
          if_some_eval_return_else_none runs store primval_expr (fun store primval_loc =>
            let proto_default := value_undefined in
            if_some_eval_else_default runs store prototype_expr proto_default (fun store prototype_loc =>
              if_some_eval_return_else_none runs store code_expr (fun store code =>
                let (store, loc) := Store.add_object store {|
                    object_proto := prototype_loc;
                    object_class := class;
                    object_extensible := extensible;
                    object_prim_value := primval_loc;
                    object_properties_ := props;
                    object_code := code |}
                in result_value store loc
                )))
        end
      end

  ))
.

Definition eval_label runs store (label : string) body : result :=
  if_eval_ter runs store body (fun store res =>
    match res with
    | res_value ret => result_value store ret
    | res_exception exc => result_value store exc
    | res_break b v =>
      if (decide(b = label)) then
        result_value store v
      else
        result_break store b v
    end
  )
.
Definition eval_break runs store (label : string) body : result :=
  if_eval_return runs store body (fun store ret =>
    result_break store label ret
  )
.
        
Definition eval_throw runs store expr : result :=
  if_eval_return runs store expr (fun store loc =>
    result_exception store loc
  )
.

Definition eval_trycatch runs store body catch : result :=
  if_eval_ter runs store body (fun store res =>
    match res with
    | res_exception exc =>
      if_eval_return runs store catch (fun store catch =>
        apply runs store catch (exc :: nil)
      )
    | r => result_res store r
    end
  )
.

Definition eval_tryfinally runs store body fin : result :=
  if_eval_ter runs store body (fun store res =>
    match res with
    | res_value x => eval_cont_terminate runs store fin
    | r =>
      if_eval_return runs store fin (fun store catch =>
        result_res store r
      )
    end
  )
.

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval runs store (e : expr) : result :=
  let return_value := result_value store in
  match e with
  | expr_undefined => return_value value_undefined
  | expr_null => return_value value_null
  | expr_string s => return_value (value_string s)
  | expr_number n => return_value (value_number n)
  | expr_true => return_value value_true
  | expr_false => return_value value_false
  | expr_id s => eval_id runs store s
  | expr_if e_cond e_true e_false => eval_if runs store e_cond e_true e_false
  | expr_seq e1 e2 => eval_seq runs store e1 e2
  | expr_object attrs l => eval_object_decl runs store attrs l
  | expr_get_field left_ right_ attributes => eval_get_field runs store left_ right_ attributes
  | expr_set_field left_ right_ new_val attributes => eval_set_field runs store left_ right_ new_val attributes
  | expr_delete_field left_ right_ => eval_deletefield runs store left_ right_
  | expr_let id value body => eval_let runs store id value body
  | expr_recc id value body => eval_rec runs store id value body
  | expr_set_bang id expr => eval_setbang runs store id expr
  | expr_lambda args body => eval_lambda runs store args body
  | expr_app f args => eval_app runs store f args
  | expr_get_attr attr left_ right_ => eval_getattr runs store left_ right_ attr
  | expr_set_attr attr left_ right_ newval => eval_setattr runs store left_ right_ attr newval
  | expr_get_obj_attr oattr obj => eval_getobjattr runs store obj oattr
  | expr_set_obj_attr oattr obj attr => result_fail "expr_set_obj_attr not implemented."
  | expr_own_field_names e => eval_ownfieldnames runs store e
  | expr_op1 op e =>
    if_eval_return runs store e (fun store v_loc =>
      if_result_some (Operators.unary op store v_loc) (fun v_res => result_value store v_res)
    )
  | expr_op2 op e1 e2 =>
    if_eval_return runs store e1 (fun store v1_loc =>
      if_eval_return runs store e2 (fun store v2_loc =>
        if_result_some (Operators.binary op store v1_loc v2_loc) (fun v_res => result_value store v_res)
    ))
  | expr_label l e => eval_label runs store l e
  | expr_break l e => eval_break runs store l e
  | expr_try_catch body catch => eval_trycatch runs store body catch
  | expr_try_finally body fin => eval_tryfinally runs store body fin
  | expr_throw e => eval_throw runs store e
  | expr_eval e bindings => result_fail "Eval not implemented."
  | expr_hint _ e => eval_cont_terminate runs store e
  end
.

Fixpoint runs max_step : runs_type :=
  match max_step with
  | 0 => {|
      runs_type_eval := fun store _ => result_bottom
    |}
  | S max_step' =>
    let wrap {A : Type} (f : runs_type -> Store.store -> A) S : A :=
      let runs' := runs max_step' in f runs' S
    in {|
      runs_type_eval := wrap eval
    |}
  end.

Definition runs_eval n := runs_type_eval (runs n).
