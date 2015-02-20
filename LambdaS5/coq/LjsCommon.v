Set Implicit Arguments.
Require Import LjsSyntax.
Require Import Utils.
Require Import String.
Require Import LjsValues.
Require Import LjsStore.
Require Import LjsMonads.

(* Utility functions useful for both the interpreter and the semantics. *)

(* Get object attribute *)

Definition get_object_oattr obj (oa : oattr) : value :=
  match oa with
  | oattr_proto => object_proto obj
  | oattr_extensible => bool_to_value (object_extensible obj)
  | oattr_code => object_code obj
  | oattr_primval => object_prim_value obj
  | oattr_class => value_string (object_class obj)
  end
.

(* Set object attribute *)
(* May fail because of wrong type. *)

Definition set_object_oattr obj oa v : resultof object :=
  let 'object_intro (oattrs_intro pr cl ex pv co) pp := obj in
  match oa with
  | oattr_proto => 
    match v with
    | value_null 
    | value_object _ => result_some (object_intro (oattrs_intro v cl ex pv co) pp)
    | _ => result_fail "Update proto failed"
    end
  | oattr_extensible =>
    match value_to_bool v with
    | Some b => result_some (object_intro (oattrs_intro pr cl b pv co) pp)
    | None => result_fail "Update extensible failed"
    end
  | oattr_code => result_fail "Can't update code"
  | oattr_primval => result_some (object_intro (oattrs_intro pr cl ex v co) pp)
  | oattr_class => result_fail "Can't update klass"
  end
.

(* Get property attribute *)
(* May fail if the attribute does not exist, or if the property is of the wrong kind. *)

Definition get_object_pattr obj s (pa : pattr) : resultof value :=
  match get_object_property obj s with
  | None => result_some value_undefined
  | Some prop =>
    match pa, prop with
    | pattr_enum, _ => result_some (bool_to_value (attributes_enumerable prop))

    | pattr_config, _ => result_some (bool_to_value (attributes_configurable prop))

    | pattr_writable, attributes_data_of data =>
      result_some (bool_to_value (attributes_data_writable data))
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

(* Set object attribute *)
(* May fail because of permission issues *)

Definition pattr_okupdate (attr : attributes) (pa : pattr) (v : value) : bool := 
  match attr, pa with
  | attributes_accessor_of {| attributes_accessor_configurable := true |}, _ => true
  | attributes_data_of {| attributes_data_configurable := true |}, _ => true
  | attributes_data_of {| attributes_data_writable := true |}, pattr_value => true
  | attributes_data_of {| attributes_data_writable := true |}, pattr_writable => true
  | _, _ => false
  end
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
    if pattr_okupdate prop pa v then
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

(* Desugaring function *)

Parameter desugar_expr : string -> option expr.

(* Gets a property recursively (the recursion limit is the size of the store) *)

Fixpoint get_property_aux limit store (ptr : object_ptr) (name : prop_name) : resultof (option attributes) :=
  match limit with
  | 0 => result_bottom
  | S limit' =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match get_object_property obj name with
      | Some prop => result_some (Some prop)
      | None => 
        match object_proto obj with
        | value_object ptr =>
          get_property_aux limit' store ptr name
        | _ => result_some None
        end
      end
    )
  end
.

Definition get_property store (ptr : object_ptr) (name : prop_name) : resultof (option attributes) :=
  get_property_aux (num_objects store) store ptr name. 

(* Finds a closure for a function call *)

Fixpoint get_closure_aux limit store (v : value) : resultof closure :=
  match v with
  | value_closure clo => result_some clo
  | value_object ptr =>
    match limit with
    | 0 => result_bottom
    | S limit' =>
      assert_get_object_from_ptr store ptr (fun obj =>
        get_closure_aux limit' store (object_code obj)
      )
    end
  | _ => result_fail "Applied non-function."
  end
.

Definition get_closure store (v : value) : resultof closure :=
  get_closure_aux (num_objects store) store v.
