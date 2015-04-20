Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import Utils.
Require Import LjsValues.
Require Import LjsStore.
Require Import LjsMonads.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

(* Utility functions useful for both the interpreter and the semantics. *)

(* Overwriting empty *)

Definition overwrite_value_if_empty v1 v2 :=
  match v2 with
  | value_empty => v1
  | _ => v2
  end
.

(* For operators *)

Definition typeof v :=
  match v with
  | value_undefined => "undefined"
  | value_null => "null"
  | value_string _ => "string"
  | value_number _ => "number"
  | value_bool _ => "boolean"
  | value_object ptr => "object"
  | value_closure _ => "closure"
  | value_empty => "empty"
  end
.

Definition prim_to_bool v :=
  match v with
  | value_bool b => b
  | value_undefined => false
  | value_null => false
  | value_number n => 
      !decide (n = JsNumber.zero \/ n = JsNumber.neg_zero \/ n = JsNumber.nan)
  | value_string s => !decide (s = "")
  | value_empty => false
  | _ => true
  end
.

Inductive is_primitive : value -> Prop :=
| is_primitive_undefined : is_primitive value_undefined
| is_primitive_null : is_primitive value_null
| is_primitive_bool : forall b, is_primitive (value_bool b)
| is_primitive_number : forall n, is_primitive (value_number n)
| is_primitive_string : forall s, is_primitive (value_string s).

Inductive is_closure : value -> Prop :=
| is_closure_closure : forall cl, is_closure (value_closure cl).

Inductive is_object : value -> Prop :=
| is_object_object : forall ptr, is_object (value_object ptr).

Definition eq_number n1 n2 := 
    n1 <> nan /\ n2 <> nan /\ 
    (n1 = zero /\ n2 = neg_zero \/ n1 = neg_zero /\ n2 = zero \/ n1 = n2).

Definition eq_number_decidable n1 n2 := decide (eq_number n1 n2).

Inductive stx_eq : value -> value -> Prop :=
| stx_eq_empty : stx_eq value_empty value_empty
| stx_eq_string : forall s, stx_eq (value_string s) (value_string s)
| stx_eq_null : stx_eq value_null value_null
| stx_eq_undefined : stx_eq value_undefined value_undefined
| stx_eq_bool : forall b, stx_eq (value_bool b) (value_bool b)
| stx_eq_number : forall n1 n2, eq_number n1 n2 -> stx_eq (value_number n1) (value_number n2)
| stx_eq_object : forall ptr, stx_eq (value_object ptr) (value_object ptr)
.

Definition is_primitive_decide v :=
  match v with
  | value_undefined | value_null | value_string _ | value_number _ | value_bool _ => true
  | _ => false
  end
.

Definition is_closure_decide v :=
  match v with
  | value_closure _ => true  
  | _ => false
  end
.

Definition is_object_decide v :=
  match v with
  | value_object _ => true
  | _ => false
  end
.

Definition stx_eq_decide v1 v2 :=
  match v1, v2 with
  | value_empty, value_empty => true
  | value_string s1, value_string s2 => decide (s1 = s2)
  | value_null, value_null => true
  | value_undefined, value_undefined => true
  | value_bool true, value_bool true => true
  | value_bool false, value_bool false => true
  | value_number n1, value_number n2 => eq_number_decidable n1 n2
  | value_object ptr1, value_object ptr2 => decide (ptr1 = ptr2)
  | _, _ => false
  end
.

Section Instances.

Local Hint Constructors is_primitive is_closure is_object stx_eq.

Global Instance is_primitive_decidable : forall v, Decidable (is_primitive v).
Proof.
    introv. applys decidable_make (is_primitive_decide v).
    destruct v; simpl; fold_bool; rew_refl; eauto.
Defined.

Global Instance is_closure_decidable : forall v, Decidable (is_closure v).
Proof.
    introv. applys decidable_make (is_closure_decide v).
    destruct v; simpl; fold_bool; rew_refl; eauto.
Defined.

Global Instance is_object_decidable : forall v, Decidable (is_object v).
Proof.
    introv. applys decidable_make (is_object_decide v).
    destruct v; simpl; fold_bool; rew_refl; auto.
Defined.

Global Instance stx_eq_decidable : forall v1 v2, Decidable (stx_eq v1 v2).
Proof.
    introv. applys decidable_make (stx_eq_decide v1 v2).
    destruct v1; destruct v2; simpl; try unfold eq_number_decidable;
    repeat cases_decide; repeat cases_if; fold_bool; rew_reflect; auto;
    intro Hx; inverts Hx; auto.
Defined.

End Instances.

(* Get object attribute *)

Definition get_object_oattr obj (oa : oattr) : value :=
  match oa with
  | oattr_proto => object_proto obj
  | oattr_extensible => value_bool (object_extensible obj)
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

(* Set object attribute *)
(* May fail because of permission issues *)

Definition pattr_okupdate (attr : attributes) (pa : pattr) v : bool := 
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

Fixpoint get_property_aux limit st obj (name : prop_name) : resultof (option attributes) :=
  match get_object_property obj name with
  | Some prop => result_some (Some prop)
  | None => 
    match object_proto obj with
    | value_object ptr =>
      match limit with
      | 0 => result_bottom
      | S limit' =>
        assert_get_object_from_ptr st ptr (fun obj =>
          get_property_aux limit' st obj name
        )
      end
    | value_null => result_some None
    | _ => result_fail "Invalid prototype chain."
    end
  end
.

Definition get_property store obj (name : prop_name) : resultof (option attributes) :=
  get_property_aux (card store) store obj name. 

(* Finds a closure for a function call *)

Fixpoint get_closure_aux limit st v : resultof closure :=
  match v with
  | value_closure clo => result_some clo
  | value_object ptr =>
    match limit with
    | 0 => result_bottom
    | S limit' =>
      assert_get_object_from_ptr st ptr (fun obj =>
        get_closure_aux limit' st (object_code obj)
      )
    end
  | _ => result_fail "Applied non-function."
  end
.

Definition get_closure st v : resultof closure :=
  get_closure_aux (card st) st v.
