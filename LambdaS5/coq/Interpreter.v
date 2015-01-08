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
*   There is one evaluator per node constructor (defined in coq/Syntax.v),
*   with eventually helper functions.
* * The “looping” functions, which call the evaluators. The “runs”
*   function calls eval at every iteration, with a reference to itself
*   applied to a strictly decreasing integer, to make Coq accept the
*   code.
*)


Implicit Type runs : Context.runs_type.
Implicit Type store : Store.store.


(****** Closures handling ******)

(* Evaluates all arguments, passing the store from one to the next. *)
Definition eval_arg_list_aux runs (left : (Store.store * @Context.result (list Values.value_loc))) (arg_expr : Syntax.expr) : (Store.store * @Context.result (list Values.value_loc)) :=
  let (store, res) := left in
  if_return store res (fun left_args =>
    if_eval_return runs store arg_expr (fun store arg_loc =>
      (store, Return (list Values.value_loc) (arg_loc :: left_args))))
.


Definition eval_reversed_arg_list runs store (args_expr : list Syntax.expr) : (Store.store * Context.result (list Values.value_loc)) :=
  List.fold_left (eval_arg_list_aux runs) args_expr (store, Return (list Values.value_loc) nil)
.

Definition make_app_loc_heap (closure_env : Values.loc_heap_type) (args_name : list Values.id) (args : list Values.value_loc) : option Values.loc_heap_type :=
  match (Utils.zip_left args_name args) with
  | Some args_heap =>
    Some (Utils.concat_list_heap
      args_heap
      closure_env
    )
  | None => None
  end
.

Definition make_app_store runs store (closure_env : Values.loc_heap_type) (args_name : list Values.id) (args : list Values.value_loc) : (Store.store * Context.result Values.value_loc) :=
  match (make_app_loc_heap closure_env args_name args) with
  | Some new_loc_heap =>
    (Store.replace_loc_heap store new_loc_heap, Context.Return nat 0) (* We have to return something... *)
  | None => (store, Fail Values.value_loc "Arity mismatch")
  end
.

Definition apply runs store (f_loc : Values.value_loc) (args : list Values.value_loc) : (Store.store * Context.result Values.value_loc) :=
  let (store, res) := ((Context.runs_type_get_closure runs) store f_loc) in
  if_return store res (fun f_loc =>
    assert_deref store f_loc (fun f =>
      match f with
      | Values.Closure id env args_names body =>
        let (inner_store, res) := make_app_store runs store env args_names args in
        if_return inner_store res (fun _ =>
          eval_cont runs inner_store body (fun inner_store res =>
            (Store.replace_loc_heap inner_store (Store.loc_heap store), res)
        ))
      | _ => (store, Fail Values.value_loc "Expected Closure but did not get one.")
      end
  ))
.


(********* Evaluators ********)

(* a lonely identifier.
* Fetch the associated value location and return it. *)
Definition eval_id runs store (name : string) : (Store.store * Context.result Values.value_loc) :=
  match (Store.get_loc store name) with
  | Some v => (store, Return Values.value_loc v)
  | None => (store, Fail Values.value_loc "ReferenceError")
  end
.


(* if e_cond e_true else e_false.
* Evaluate the condition and get the associated value, then evaluate
* e_true or e_false depending on the value. *)
Definition eval_if runs store (e_cond e_true e_false : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store e_cond (fun store v =>
    match (Store.get_value store v) with
    | Some Values.True => eval_cont_terminate runs store e_true
    | Some _ => eval_cont_terminate runs store e_false
    | None => (store, Impossible Values.value_loc "Location of non-existing value.")
    end
  )
.

(* e1 ; e2.
* Evaluate e1, then e2, and return the value location returned by e2. *)
Definition eval_seq runs store (e1 e2 : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store e1 (fun store v => eval_cont_terminate runs store e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux runs store (l : list (string * Syntax.property)) (acc : Values.object_properties) : (Store.store * (@Context.result Values.object_properties)) :=
  match l with
  | nil => (store, Return Values.object_properties acc)
  | (name, Syntax.property_data (Syntax.data_intro value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store value_expr (fun store value_loc =>
      eval_object_properties_aux runs store tail (Heap.write acc name (
        Values.attributes_data_of {|
            Values.attributes_data_value := value_loc;
            Values.attributes_data_writable := writable;
            Values.attributes_data_enumerable := enumerable;
            Values.attributes_data_configurable := configurable |}
      )))
  | (name, Syntax.property_accessor (Syntax.accessor_intro getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store getter_expr (fun store getter_loc =>
      if_eval_return runs store setter_expr (fun store setter_loc =>
        eval_object_properties_aux runs store tail (Heap.write acc name (
           Values.attributes_accessor_of {|
              Values.attributes_accessor_get := getter_loc;
              Values.attributes_accessor_set := setter_loc;
              Values.attributes_accessor_enumerable := enumerable;
              Values.attributes_accessor_configurable := configurable |}
    ))))
  end
.
(* Reads a list of syntax trees of properties and converts it to a heap
* bindable to an object. *)
Definition eval_object_properties runs store (l : list (string * Syntax.property)) : (Store.store * (@Context.result Values.object_properties)) :=
  eval_object_properties_aux runs store l Heap.empty
.

(* { [ attrs ] props }
* Evaluate the primval attribute (if any), then the proto attribute (defaults
* to Undefined), then properties. Finally, allocate a new object with the
* computed values. *)
Definition eval_object_decl runs store (attrs : Syntax.objattrs) (l : list (string * Syntax.property)) : (Store.store * Context.result Values.value_loc) :=

  match attrs with
  | Syntax.objattrs_intro primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_some_eval_return_else_none runs store primval_expr (fun store primval_loc =>
      let (store, proto_default) := Store.add_value store Values.Undefined in
      if_some_eval_else_default runs store prototype_expr proto_default (fun store prototype_loc =>
        if_some_eval_return_else_none runs store code_expr (fun store code =>
          let (store, props) := (eval_object_properties runs store l)
          in if_return store props (fun props =>
            let (store, loc) := Store.add_object store {|
                Values.object_proto := prototype_loc;
                Values.object_class := class;
                Values.object_extensible := extensible;
                Values.object_prim_value := primval_loc;
                Values.object_properties_ := props;
                Values.object_code := code |}
            in (store, Context.Return Values.value_loc loc)
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
Definition eval_get_field runs store (left_expr right_expr arg_expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      if_eval_return runs store arg_expr (fun store arg_loc =>
        assert_get_object store left_loc (fun object =>
          assert_get_string store right_loc (fun name =>
            let (store, res) := Context.runs_type_get_property runs store (left_loc, name) in
            if_return store res (fun ret =>
              match ret with
              | Some (attributes_data_of data) => (store, Return Values.value_loc (Values.attributes_data_value data))
              | Some (attributes_accessor_of (attributes_accessor_intro getter _ _ _)) =>
                  apply runs store getter (left_loc :: (arg_loc :: nil))
              | None =>
                  Context.add_value_return store Values.Undefined
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
Definition eval_set_field runs store (left_expr right_expr new_val_expr arg_expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      if_eval_return runs store new_val_expr (fun store new_val =>
        if_eval_return runs store arg_expr (fun store arg_loc =>
          assert_get_object_ptr store left_loc (fun left_ptr =>
            assert_get_object_from_ptr store left_ptr (fun object =>
              assert_get_string store right_loc (fun name =>
                match (Values.get_object_property object name) with
                | Some (attributes_data_of (Values.attributes_data_intro _ w e c)) =>
                  Context.update_object_property store left_ptr name (fun prop =>
                    let attrs := Values.attributes_data_of (attributes_data_intro new_val w e c) in
                    (store, Some attrs, Context.Return Values.value_loc new_val)
                  )
                | Some (attributes_accessor_of (attributes_accessor_intro _ setter _ _)) =>
                    (* Note: pattr_setters don't get the new value. See https://github.com/brownplt/LambdaS5/issues/45 *)
                    apply runs store setter (left_loc :: (arg_loc :: nil))
                | None => 
                  Context.update_object_property store left_ptr name (fun prop =>
                    let attrs := Values.attributes_data_of (attributes_data_intro new_val true true true) in
                    (store, Some attrs, Context.Return Values.value_loc new_val)
                  )
                end)))))))
.

Definition eval_deletefield runs store (left_expr right_expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right_loc =>
      assert_get_object_ptr store left_loc (fun left_ptr =>
        assert_get_string store right_loc (fun name =>
          update_object store left_ptr (fun obj =>
            match obj with
            | object_intro v c e p props code =>
              let (store, true_loc) := Store.add_value store True in
              (store, object_intro v c e p (Heap.rem props name) code, Return Values.value_loc true_loc)
            end
  )))))
.

(* let (id = expr) body
* Evaluate expr, set it to a fresh location in the store, and bind this
* location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_let runs store (id : string) (value_expr body_expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store value_expr (fun store value_loc =>
    assert_deref store value_loc (fun value =>
      let (store, loc) := Store.add_named_value store id value in
        eval_cont_terminate runs store body_expr
  ))
.

(* rec (id = expr) body
* Evaluate expr with a reference to itself, set it to a fresh location in the store,
* and bind this location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_rec runs store (id : string) (value_expr body_expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  let (store, self_loc) := Store.add_named_value store id Values.Undefined in
  if_eval_return runs store value_expr (fun store value_loc =>
    assert_deref store value_loc (fun value =>
      let store := Store.add_value_at_location store self_loc value in
        eval_cont_terminate runs store body_expr
  ))
.

(* name := expr
* Evaluate expr, and set it at the location bound to `name`. Fail if `name`
* is not associated with a location in the store. *)
Definition eval_setbang runs store (name : string) (expr : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store expr (fun store loc =>
    assert_deref store loc (fun value =>
      match (Store.get_loc store name) with
      | Some loc => (Store.add_value_at_location store loc value, Context.Return Values.value_loc loc)
      | None => Context.raise_exception store "ReferenceError"
      end
  ))
.

(* func (args) { body }
* Capture the environment's name-to-location heap and return a closure. *)
Definition eval_lambda runs store (args : list id) (body : Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  let env := Store.loc_heap store in
  let (store, loc) := (Store.add_closure store env args body) in
  (store, Context.Return Values.value_loc loc)
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
Definition eval_app runs store (f : Syntax.expr) (args_expr : list Syntax.expr) : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store f (fun store f_loc =>
    let (store, res) := eval_reversed_arg_list runs store (List.rev args_expr) in
    if_return store res (fun args =>
      apply runs store f_loc args
  ))
.
Definition get_property_attribute store (oprop : option Values.attributes) (attr : Syntax.pattr) : (Store.store * Context.result Values.value_loc) :=
  match oprop with
  | None => Context.add_value_return store Values.Undefined
  | Some prop =>
    match (attr, prop) with
    | (pattr_config,     attributes_data_of (attributes_data_intro      _ _ _ config))
    | (pattr_config, attributes_accessor_of (attributes_accessor_intro _ _ _ config)) =>
      Context.return_bool store config

    | (pattr_enum,     attributes_data_of (attributes_data_intro     _ _ enum _))
    | (pattr_enum, attributes_accessor_of (attributes_accessor_intro _ _ enum _)) =>
      Context.return_bool store enum

    | (pattr_writable, attributes_data_of (attributes_data_intro _ writable _ _)) =>
      Context.return_bool store writable
    | (pattr_writable, attributes_accessor_of _) =>
      (store, Fail Values.value_loc "Access #writable of accessor.")

    | (pattr_value, attributes_data_of (attributes_data_intro value _ _ _)) =>
      (store, Return value_loc value)
    | (pattr_value, attributes_accessor_of _) =>
      (store, Fail Values.value_loc "Access #value of accessor.")

    | (pattr_getter, attributes_accessor_of (attributes_accessor_intro getter _ _ _)) =>
      (store, Return value_loc getter)
    | (pattr_getter, attributes_data_of _) =>
      (store, Fail Values.value_loc "Access #getter of data.")

    | (pattr_setter, attributes_accessor_of (attributes_accessor_intro _ setter _ _)) =>
      (store, Return value_loc setter)
    | (pattr_setter, attributes_data_of _) =>
      (store, Fail Values.value_loc "Access #setter of data.")
    end
  end
.

(* left[right<attr>] *)
Definition eval_getattr runs store left_expr right_expr attr :=
  if_eval_return runs store left_expr (fun store left_ =>
    if_eval_return runs store right_expr (fun store right_ =>
      assert_get_object store left_ (fun obj =>
        assert_get_string store right_ (fun fieldname =>
          get_property_attribute store (get_object_property obj fieldname) attr 
  ))))
.


Definition set_property_attribute store (oprop : option Values.attributes) (attr : Syntax.pattr) (new_val : Values.value_loc) : (Store.store * (option Values.attributes) * Context.result Values.value_loc) :=
  let (store, undef) := Store.add_value store Values.Undefined in
  let (store, true_ret) := Context.add_value_return store Values.True in
  (* Some abbreviations: *)
  let aai := Values.attributes_accessor_intro in
  let adi := Values.attributes_data_intro in
  let aao := Values.attributes_accessor_of in
  let ado := Values.attributes_data_of in
  let raao := (fun x => (store, Some (aao x), true_ret)) in
  let rado := (fun x => (store, Some (ado x), true_ret)) in
  let getbool := assert_get_bool_3 store new_val oprop in
  match oprop with
  | None =>
    match attr with
    | Syntax.pattr_getter => raao (aai new_val undef false false)
    | Syntax.pattr_setter => raao (aai undef new_val false false)
    | Syntax.pattr_value => rado (adi new_val false false false)
    | Syntax.pattr_writable => getbool (fun b => rado (adi undef b false false))
    | Syntax.pattr_enum => getbool (fun b => rado (adi undef false b true))
    | Syntax.pattr_config => getbool (fun b => rado (adi undef false true b))
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
                                 raao (attributes_accessor_intro undef  new_val enum true)
    | (pattr_setter, attributes_accessor_of (attributes_accessor_intro get _       enum true)) =>
                                 raao (attributes_accessor_intro get new_val enum true)
    (* Set #getter when #configurable is true *)
    | (pattr_getter,     attributes_data_of (attributes_data_intro     _       _     enum true)) =>
                                 raao (attributes_accessor_intro new_val undef enum true)
    | (pattr_getter, attributes_accessor_of (attributes_accessor_intro _       set enum true)) =>
                                 raao (attributes_accessor_intro new_val set enum true)
    (* Set #value of accessor when #configurable is true *)
    | (pattr_value,  attributes_accessor_of (attributes_accessor_intro _       _     enum true)) =>
                                 rado (attributes_data_intro     new_val false enum true)
    (* Set #writable of accessor when #configurable is true *)
    | (pattr_writable, attributes_accessor_of (attributes_accessor_intro _     _ enum true)) =>
        getbool (fun b =>          rado (attributes_data_intro     undef b enum true))
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
        if b then (store, oprop, Fail Values.value_loc "Set #configurable to true while #configurable is false")
        else (store, oprop, true_ret) (* unchanged *)
      )
    | (pattr_value, _) => (store, oprop, Fail Values.value_loc "Invalid #value set.")
    | (pattr_writable, _) => (store, oprop, Fail Values.value_loc "Invalid #writable set.")
    | (pattr_getter, _) => (store, oprop, Fail Values.value_loc "Invalid #getter set.")
    | (pattr_setter, _) => (store, oprop, Fail Values.value_loc "Invalid #setter set.")
    | (pattr_enum,     attributes_data_of (attributes_data_intro     _ _ _ false)) =>
        (store, oprop, Fail Values.value_loc "Invalid #enum set for data property.")
    | (pattr_enum, attributes_accessor_of (attributes_accessor_intro _ _ _ false)) =>
        (store, oprop, Fail Values.value_loc "Invalid #enum set for accessor property.")
    end
  end
.

(* left[right<attr> = new_val] *)
Definition eval_setattr runs store left_expr right_expr attr new_val_expr :=
  if_eval_return runs store left_expr (fun store left_ =>
    if_eval_return runs store right_expr (fun store right_ =>
      if_eval_return runs store new_val_expr (fun store new_val =>
        assert_get_object_ptr store left_ (fun obj_ptr =>
          assert_get_string store right_ (fun fieldname =>
            Context.update_object_property store obj_ptr fieldname (fun oprop =>
              set_property_attribute store oprop attr new_val
  ))))))
.

Definition eval_getobjattr runs store obj_expr oattr :=
  if_eval_return runs store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      match oattr with
      | Syntax.oattr_proto => (store, Return Values.value_loc (Values.object_proto obj))
      | Syntax.oattr_extensible => Context.return_bool store (Values.object_extensible obj)
      | Syntax.oattr_code =>
        match (Values.object_code obj) with
        | Some code => (store, Return Values.value_loc code)
        | None => Context.add_value_return store Values.Null
        end
      | Syntax.oattr_primval =>
        match (Values.object_prim_value obj) with
        | Some v => (store, Return Values.value_loc v)
        | None => (store, Fail Values.value_loc "primval attribute is None.")
        end
      | Syntax.oattr_class => Context.add_value_return store (Values.String (Values.object_class obj))
      end
  ))
.

Definition make_prop_list_aux (fuel : nat) (left : option (nat * Store.store * object_properties)) (val : Values.value) : option (nat * Store.store * object_properties) :=
  match left with
  | Some (nb_entries, store, attrs) =>
    let (store, val_loc) := Store.add_value store val in
    let attr := Values.attributes_data_of (attributes_data_intro val_loc false false false) in
    match (Utils.string_of_nat fuel nb_entries) with
    | Some str_nb => Some (S nb_entries, store, Heap.write attrs str_nb attr)
    | None => None
    end
  | None => None
  end
.
Definition make_prop_heap runs store (vals : list Values.value) : option (Store.store * Values.object_properties) :=
  match (List.fold_left (make_prop_list_aux (Context.runs_type_nat_fuel runs)) vals (Some (0, store, Heap.empty))) with
  | Some (nb_entries, store, attrs) =>
    let (store, length_loc) := Store.add_value store (Values.Number (Utils.make_number nb_entries)) in
    let length_attr := attributes_data_of (attributes_data_intro length_loc false false false) in
    Some (store, Heap.write attrs "length" length_attr)
  | None => None
  end
.
Definition left_to_string {X : Type} (x : (string * X)) : Values.value :=
  let (k, v) := x in Values.String k
.
Definition eval_ownfieldnames runs store obj_expr : (Store.store * Context.result Values.value_loc) :=
  if_eval_return runs store obj_expr (fun store obj_loc =>
    assert_get_object store obj_loc (fun obj =>
      let props := (Heap.to_list (Values.object_properties_ obj)) in
      let props := (List.map left_to_string props) in
      match (make_prop_heap runs store props) with
      | Some (store, props) =>
        match (Syntax.default_objattrs) with
        | Syntax.objattrs_intro primval_expr code_expr prototype_expr class extensible =>
          (* Following the order in the original implementation: *)
          if_some_eval_return_else_none runs store primval_expr (fun store primval_loc =>
            let (store, proto_default) := Store.add_value store Values.Undefined in
            if_some_eval_else_default runs store prototype_expr proto_default (fun store prototype_loc =>
              if_some_eval_return_else_none runs store code_expr (fun store code =>
                let (store, loc) := Store.add_object store {|
                    Values.object_proto := prototype_loc;
                    Values.object_class := class;
                    Values.object_extensible := extensible;
                    Values.object_prim_value := primval_loc;
                    Values.object_properties_ := props;
                    Values.object_code := code |}
                in (store, Context.Return Values.value_loc loc)
                )))
        end
      | None => (store, Fail Values.value_loc "Could not convert nat to string (Coq is not Turing-complete).")
      end

  ))
.

Definition eval_label runs store (label : string) body : (Store.store * (@Context.result Values.value_loc)) :=
  eval_cont runs store body (fun store res =>
    match res with
    | Return ret => (store, Return Values.value_loc ret)
    | Exception exc => (store, Exception Values.value_loc exc)
    | Break b v =>
      if (decide(b = label)) then
        (store, Return Values.value_loc v)
      else
        (store, Break Values.value_loc b v)
    | Fail f => (store, Fail Values.value_loc f)
    | Impossible f => (store, Impossible Values.value_loc f)
    end
  )
.
Definition eval_break runs store (label : string) body : (Store.store * (@Context.result Values.value_loc)) :=
  if_eval_return runs store body (fun store ret =>
    (store, Break Values.value_loc label ret)
  )
.
        

Definition eval_throw runs store expr : (Store.store * (@Context.result Values.value_loc)) :=
  if_eval_return runs store expr (fun store loc =>
    (store, Context.Exception Values.value_loc loc)
  )
.

Definition eval_trycatch runs store body catch : (Store.store * (@Context.result Values.value_loc)) :=
  eval_cont runs store body (fun store res =>
    match res with
    | Return x => (store, Return Values.value_loc x)
    | Exception exc =>
      if_eval_return runs store catch (fun store catch =>
        apply runs store catch (exc :: nil)
      )
    | Break b v => (store, Break Values.value_loc b v)
    | Fail f => (store, Fail Values.value_loc f)
    | Impossible f => (store, Impossible Values.value_loc f)
    end
  )
.

Definition eval_tryfinally runs store body fin : (Store.store * (@Context.result Values.value_loc)) :=
  eval_cont runs store body (fun store res =>
    match res with
    | Return x => eval_cont_terminate runs store fin
    | Exception exc =>
      if_eval_return runs store fin (fun store catch =>
        (store, Exception Values.value_loc exc)
      )
    | Break b v => (store, Break Values.value_loc b v)
    | Fail f => (store, Fail Values.value_loc f)
    | Impossible f => (store, Impossible Values.value_loc f)
    end
  )
.

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval runs store (e : Syntax.expr) : (Store.store * (@Context.result Values.value_loc)) :=
  let return_value := Context.add_value_return store in
  match e with
  | Syntax.expr_undefined => return_value Values.Undefined
  | Syntax.expr_null => return_value Values.Null
  | Syntax.expr_string s => return_value (Values.String s)
  | Syntax.expr_number n => return_value (Values.Number n)
  | Syntax.expr_true => return_value Values.True
  | Syntax.expr_false => return_value Values.False
  | Syntax.expr_id s => eval_id runs store s
  | Syntax.expr_if e_cond e_true e_false => eval_if runs store e_cond e_true e_false
  | Syntax.expr_seq e1 e2 => eval_seq runs store e1 e2
  | Syntax.expr_object attrs l => eval_object_decl runs store attrs l
  | Syntax.expr_get_field left_ right_ attributes => eval_get_field runs store left_ right_ attributes
  | Syntax.expr_set_field left_ right_ new_val attributes => eval_set_field runs store left_ right_ new_val attributes
  | Syntax.expr_delete_field left_ right_ => eval_deletefield runs store left_ right_
  | Syntax.expr_let id value body => eval_let runs store id value body
  | Syntax.expr_recc id value body => eval_rec runs store id value body
  | Syntax.expr_set_bang id expr => eval_setbang runs store id expr
  | Syntax.expr_lambda args body => eval_lambda runs store args body
  | Syntax.expr_app f args => eval_app runs store f args
  | Syntax.expr_get_attr attr left_ right_ => eval_getattr runs store left_ right_ attr
  | Syntax.expr_set_attr attr left_ right_ newval => eval_setattr runs store left_ right_ attr newval
  | Syntax.expr_get_obj_attr oattr obj => eval_getobjattr runs store obj oattr
  | Syntax.expr_set_obj_attr oattr obj attr => (store, Fail Values.value_loc "expr_set_obj_attr not implemented.")
  | Syntax.expr_own_field_names e => eval_ownfieldnames runs store e
  | Syntax.expr_op1 op e =>
    if_eval_return runs store e (fun store v_loc =>
      Operators.unary op runs store v_loc
    )
  | Syntax.expr_op2 op e1 e2 =>
    if_eval_return runs store e1 (fun store v1_loc =>
      if_eval_return runs store e2 (fun store v2_loc =>
        Operators.binary op runs store v1_loc v2_loc
    ))
  | Syntax.expr_label l e => eval_label runs store l e
  | Syntax.expr_break l e => eval_break runs store l e
  | Syntax.expr_try_catch body catch => eval_trycatch runs store body catch
  | Syntax.expr_try_finally body fin => eval_tryfinally runs store body fin
  | Syntax.expr_throw e => eval_throw runs store e
  | Syntax.expr_eval e bindings => (store, Fail Values.value_loc "Eval not implemented.")
  | Syntax.expr_hint _ e => eval_cont_terminate runs store e
  end
.

(* Calls a value (hopefully a function or a callable object) *)
Definition get_closure runs store (loc : Values.value_loc) : (Store.store * (@Context.result Values.value_loc)) :=
  assert_get store loc (fun v =>
    match v with
    | Values.Closure _ _ _ _ => (store, Context.Return Values.value_loc loc)
    | Values.Object ptr =>
      assert_get_object_from_ptr store ptr (fun obj =>
        match (Values.object_code obj) with
        | None => (store, Fail Values.value_loc "Applied an object without a code attribute")
        | Some loc =>
          (Context.runs_type_get_closure runs) store loc
        end
      )
    | _ => (store, Fail Values.value_loc "Applied non-function.")
    end
  )
.

(* Gets a property recursively. *)
Definition get_property runs store (arg : Values.value_loc * Values.prop_name) : (Store.store * (@Context.result (option Values.attributes))) :=
  let (loc, name) := arg in
  assert_get store loc (fun val =>
    match val with
    | Object ptr =>
      assert_get_object_from_ptr store ptr (fun obj =>
        match (Values.get_object_property obj name, Values.object_proto obj) with
        | (Some prop, _) => (store, Return (option Values.attributes) (Some prop))
        | (None, proto) => (Context.runs_type_get_property runs) store (proto, name)
        end
      )
    | _ => (store, Return (option Values.attributes) None)
    end
  )
.


Fixpoint runs {X Y : Type} (runner : Context.runs_type -> Context.runner_type X Y) (max_steps : nat) (store : Store.store) (e : X) : (Store.store * (@Context.result Y)) :=
  match (max_steps) with
  | 0 => (store, Fail Y "Coq is not Turing-complete")
  | S max_steps' =>
    let runners := {|
        Context.runs_type_nat_fuel := max_steps';
        Context.runs_type_eval := runs eval max_steps';
        Context.runs_type_get_closure := runs get_closure max_steps';
        Context.runs_type_get_property := runs get_property max_steps'
        |} in
    runner runners store e
  end
.

Definition runs_eval := runs eval.
Definition runs_get_closure := runs get_closure.
Definition runs_get_property := runs get_property.
