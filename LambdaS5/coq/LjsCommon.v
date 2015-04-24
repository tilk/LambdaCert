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
Implicit Type b : bool.
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

Definition value_to_bool_cast v :=
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

Definition value_to_str_cast v :=
  match v with
  | value_undefined => "undefined"
  | value_null => "null"
  | value_string s => s
  | value_number n => JsNumber.to_string n
  | value_bool b => ifb b then "true" else "false"
  | value_empty => "empty"
  | value_object ptr => "object"
  | value_closure clo => "closure"
  end
.

Definition value_to_num_cast v :=
  match v with
  | value_undefined => JsNumber.nan
  | value_null => JsNumber.zero
  | value_bool b => ifb b then JsNumber.one else JsNumber.zero
  | value_number n => n
  | value_string "" => JsNumber.zero
  | value_string s => JsNumber.from_string s
  | value_empty => JsNumber.nan
  | value_object ptr => JsNumber.nan
  | value_closure clo => JsNumber.nan
  end
.

Definition num_comparison_op (op : number -> number -> bool) b1 b2 n1 n2 : bool :=
  let '(n1', n2') := ifb b1 then (n2, n1) else (n1, n2) in
  let b := op n1' n2' in
  if b2 then !b else b.

Definition num_lt := num_comparison_op JsNumber.lt_bool false false.
Definition num_gt := num_comparison_op JsNumber.lt_bool true false.
Definition num_le := num_comparison_op JsNumber.lt_bool true true.
Definition num_ge := num_comparison_op JsNumber.lt_bool false true.

Fixpoint string_lt s1 s2 :=
    match s1, s2 with
    | EmptyString, _ => true
    | _, EmptyString => false
    | String ch1 s1', String ch2 s2' => 
        ifb ch1 = ch2 then string_lt s1' s2' else decide (int_of_char ch1 < int_of_char ch2)
    end.

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

Inductive is_accessor : attributes -> Prop :=
| is_accessor_accessor : forall acc, is_accessor (attributes_accessor_of acc).

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

Inductive same_value : value -> value -> Prop :=
| same_value_empty : same_value value_empty value_empty
| same_value_string : forall s, same_value (value_string s) (value_string s)
| same_value_null : same_value value_null value_null
| same_value_undefined : same_value value_undefined value_undefined
| same_value_bool : forall b, same_value (value_bool b) (value_bool b)
| same_value_number : forall n, same_value (value_number n) (value_number n)
| same_value_object : forall ptr, same_value (value_object ptr) (value_object ptr)
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

Definition is_accessor_decide attrs :=
  match attrs with
  | attributes_accessor_of _ => true
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

Definition same_value_decide v1 v2 :=
  match v1, v2 with
  | value_empty, value_empty => true
  | value_string s1, value_string s2 => decide (s1 = s2)
  | value_null, value_null => true
  | value_undefined, value_undefined => true
  | value_bool true, value_bool true => true
  | value_bool false, value_bool false => true
  | value_number n1, value_number n2 => decide (n1 = n2)
  | value_object ptr1, value_object ptr2 => decide (ptr1 = ptr2)
  | _, _ => false
  end
.

Section Instances.

Local Hint Constructors is_primitive is_closure is_object is_accessor stx_eq same_value.

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

Global Instance is_accessor_decidable : forall attrs, Decidable (is_accessor attrs).
Proof.
    introv. applys decidable_make (is_accessor_decide attrs).
    destruct attrs; simpl; fold_bool; rew_refl; auto.
Defined.

Global Instance stx_eq_decidable : forall v1 v2, Decidable (stx_eq v1 v2).
Proof.
    introv. applys decidable_make (stx_eq_decide v1 v2).
    destruct v1; destruct v2; simpl; try unfold eq_number_decidable;
    repeat cases_decide; repeat cases_if; fold_bool; rew_reflect; auto;
    intro Hx; inverts Hx; auto.
Defined.

Global Instance same_value_decidable : forall v1 v2, Decidable (same_value v1 v2).
Proof.
    introv. applys decidable_make (same_value_decide v1 v2).
    destruct v1; destruct v2; simpl; try unfold eq_number_decidable;
    repeat cases_decide; repeat cases_if; fold_bool; rew_reflect; auto;
    intro Hx; inverts Hx; auto.
Defined.

End Instances.

(* Get object attribute *)

Definition get_oattrs_oattr oas (oa : oattr) : value :=
  match oa with
  | oattr_proto => oattrs_proto oas
  | oattr_extensible => value_bool (oattrs_extensible oas)
  | oattr_code => oattrs_code oas
  | oattr_primval => oattrs_prim_value oas
  | oattr_class => value_string (oattrs_class oas)
  end
.

Definition get_object_oattr obj (oa : oattr) : value :=
  get_oattrs_oattr (object_attrs obj) oa. 

(* Set object attribute *)
(* May fail because of wrong type. *)

Inductive object_oattr_valid : oattr -> value -> Prop :=
| object_oattr_valid_proto_null : 
    object_oattr_valid oattr_proto value_null
| object_oattr_valid_proto_object : forall ptr,
    object_oattr_valid oattr_proto (value_object ptr)
| object_oattr_valid_extensible_bool : forall b,
    object_oattr_valid oattr_extensible (value_bool b)
| object_oattr_valid_primval : forall v,
    object_oattr_valid oattr_primval v
.

Inductive oattrs_oattr_modifiable oas : oattr -> Prop :=
| oattrs_oattr_modifiable_proto : 
    oattrs_extensible oas ->
    oattrs_oattr_modifiable oas oattr_proto
| oattrs_oattr_modifiable_extensible : 
    oattrs_extensible oas ->
    oattrs_oattr_modifiable oas oattr_extensible
| oattrs_oattr_modifiable_primval : 
    oattrs_oattr_modifiable oas oattr_primval
.

Definition object_oattr_modifiable obj oa := oattrs_oattr_modifiable (object_attrs obj) oa.

Definition object_oattr_valid_decide oa v :=
    match oa with
    | oattr_proto => 
        match v with value_null | value_object _ => true | _ => false end
    | oattr_extensible =>
        match v with value_bool _ => true | _ => false end
    | oattr_primval => true
    | _ => false
    end.

Definition oattrs_oattr_modifiable_decide oas oa :=
    match oa with
    | oattr_proto | oattr_extensible => oattrs_extensible oas
    | oattr_primval => true
    | _ => false
    end.

Local Hint Constructors object_oattr_valid oattrs_oattr_modifiable.

Instance object_oattr_valid_decidable : forall oa v, Decidable (object_oattr_valid oa v).
Proof.
    introv. applys decidable_make (object_oattr_valid_decide oa v).
    destruct oa; destruct v; simpl; fold_bool; rew_refl; auto.
Qed.

Instance object_oattr_modifiable_decidable : forall oas oa, Decidable (oattrs_oattr_modifiable oas oa).
Proof.
    introv. applys decidable_make (oattrs_oattr_modifiable_decide oas oa).
    destruct oa; simpl; fold_bool; rew_refl; auto; 
    sets_eq beq : (oattrs_extensible oas); symmetry in EQbeq; destruct beq;
    fold_bool; rew_reflect in *; auto; intro H; inverts H; auto.
Qed.

Definition modify_object_oattrs obj f : object :=
  let 'object_intro oattrs pp := obj in object_intro (f oattrs) pp.

Definition set_oattrs_oattr oas oa v :=
  let 'oattrs_intro pr cl ex pv co := oas in
  match oa with
  | oattr_proto => oattrs_intro v cl ex pv co
  | oattr_extensible => oattrs_intro pr cl (unsome (value_to_bool v)) pv co
  | oattr_code => oattrs_intro pr cl ex pv v
  | oattr_primval => oattrs_intro pr cl ex v co
  | oattr_class => oattrs_intro pr (unsome (value_to_string v)) ex pv co
  end.

Definition set_object_oattr obj oa v : object :=
  modify_object_oattrs obj (fun oas => set_oattrs_oattr oas oa v).

(* Get property attribute *)
(* May fail if the attribute does not exist, or if the property is of the wrong kind. *)

Inductive attributes_pattr_readable : attributes -> pattr -> Prop :=
| attributes_pattr_readable_enum : forall attrs, attributes_pattr_readable attrs pattr_enum
| attributes_pattr_readable_config : forall attrs, attributes_pattr_readable attrs pattr_config
| attributes_pattr_readable_value : forall data, attributes_pattr_readable (attributes_data_of data) pattr_value
| attributes_pattr_readable_writable : forall data, attributes_pattr_readable (attributes_data_of data) pattr_writable
| attributes_pattr_readable_getter : forall acc, attributes_pattr_readable (attributes_accessor_of acc) pattr_getter
| attributes_pattr_readable_setter : forall acc, attributes_pattr_readable (attributes_accessor_of acc) pattr_setter
.

Definition attributes_pattr_readable_decide attrs pa :=
  match pa with
  | pattr_enum | pattr_config => true
  | pattr_value | pattr_writable => !decide (is_accessor attrs)
  | pattr_getter | pattr_setter => decide (is_accessor attrs)
  end.

Local Hint Constructors attributes_pattr_readable.

Instance attributes_pattr_readable_decidable : forall attrs pa, Decidable (attributes_pattr_readable attrs pa).
Proof.
    introv. applys decidable_make (attributes_pattr_readable_decide attrs pa).
    destruct attrs; destruct pa; simpl; fold_bool; rew_reflect; auto.
Defined.

Definition get_attributes_pattr attrs pa :=
    match pa, attrs with
    | pattr_enum, _ => value_bool (attributes_enumerable attrs)
    | pattr_config, _ => value_bool (attributes_configurable attrs)
    | pattr_writable, attributes_data_of data => value_bool (attributes_data_writable data)
    | pattr_value, attributes_data_of data => attributes_data_value data
    | pattr_getter, attributes_accessor_of acc => attributes_accessor_get acc
    | pattr_setter, attributes_accessor_of acc => attributes_accessor_set acc
    | _, _ => arbitrary
    end.

(* Set object attribute *)
(* May fail because of permission issues *)

Inductive attributes_pattr_valid : pattr -> value -> Prop :=
| attributes_pattr_valid_value : forall v, attributes_pattr_valid pattr_value v
| attritubes_pattr_valid_writable : forall b, attributes_pattr_valid pattr_writable (value_bool b)
| attributes_pattr_valid_getter : forall v, attributes_pattr_valid pattr_getter v
| attributes_pattr_valid_setter : forall v, attributes_pattr_valid pattr_setter v
| attritubes_pattr_valid_enum : forall b, attributes_pattr_valid pattr_enum (value_bool b)
| attritubes_pattr_valid_config : forall b, attributes_pattr_valid pattr_config (value_bool b)
.

Inductive attributes_pattr_writable : attributes -> pattr -> Prop :=
| attributes_pattr_writable_configurable : forall attr pa,
    attributes_configurable attr ->
    attributes_pattr_writable attr pa
| attributes_pattr_writable_value : forall data,
    attributes_data_writable data ->
    attributes_pattr_writable (attributes_data_of data) pattr_value
| attributes_pattr_writable_writable : forall data,
    attributes_data_writable data ->
    attributes_pattr_writable (attributes_data_of data) pattr_writable
.

Definition attributes_pattr_valid_decide pa v : bool :=
  match pa, v with
  | pattr_value, _ => true
  | pattr_writable, value_bool _ => true
  | pattr_getter, _ => true
  | pattr_setter, _ => true
  | pattr_enum, value_bool _ => true
  | pattr_config, value_bool _ => true
  | _, _ => false
  end.

Definition attributes_pattr_writable_decide (attr : attributes) (pa : pattr) : bool := 
  match attr, pa with
  | attributes_accessor_of {| attributes_accessor_configurable := true |}, _ => true
  | attributes_data_of {| attributes_data_configurable := true |}, _ => true
  | attributes_data_of {| attributes_data_writable := true |}, pattr_value => true
  | attributes_data_of {| attributes_data_writable := true |}, pattr_writable => true
  | _, _ => false
  end
.

Local Hint Constructors attributes_pattr_valid attributes_pattr_writable.

Instance attributes_pattr_valid_decidable : forall pa v, Decidable (attributes_pattr_valid pa v).
Proof.
    introv. applys decidable_make (attributes_pattr_valid_decide pa v).
    destruct pa; destruct v; simpl; fold_bool; rew_refl; auto.
Defined.

Instance attributes_pattr_writable_decidable : forall attrs pa, Decidable (attributes_pattr_writable attrs pa).
Proof.
    introv. applys decidable_make (attributes_pattr_writable_decide attrs pa).
    destruct attrs as [aa|aa]; destruct aa; destruct pa; simpl; repeat cases_if; substs;
    fold_bool; rew_refl; auto; introv Hw; inverts Hw; tryfalse.
Defined.

Definition new_attributes_pattr pa v :=
  match pa with
  | pattr_getter => attributes_accessor_of (attributes_accessor_intro v value_undefined false false)
  | pattr_setter => attributes_accessor_of (attributes_accessor_intro value_undefined v false false)
  | pattr_value => attributes_data_of (attributes_data_intro v false false false)
  | pattr_writable => 
    attributes_data_of (attributes_data_intro value_undefined (unsome (value_to_bool v)) false false)
  | pattr_enum => 
    attributes_data_of (attributes_data_intro value_undefined false (unsome (value_to_bool v)) false)
  | pattr_config => 
    attributes_data_of (attributes_data_intro value_undefined false false (unsome (value_to_bool v)))
  end.

Definition set_attributes_pattr attrs pa v :=
  match pa, attrs with
  | pattr_getter, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_accessor_of (attributes_accessor_intro v se en co)
  | pattr_setter, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_accessor_of (attributes_accessor_intro ge v en co)
  | pattr_enum, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_accessor_of (attributes_accessor_intro ge se (unsome (value_to_bool v)) co)
  | pattr_config, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_accessor_of (attributes_accessor_intro ge se en (unsome (value_to_bool v)))
  | pattr_value, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_data_of (attributes_data_intro v false en co)
  | pattr_writable, attributes_accessor_of (attributes_accessor_intro ge se en co) =>
    attributes_data_of (attributes_data_intro value_undefined (unsome (value_to_bool v)) en co) 
  | pattr_value, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_data_of (attributes_data_intro v wr en co)
  | pattr_writable, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_data_of (attributes_data_intro va (unsome (value_to_bool v)) en co)
  | pattr_enum, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_data_of (attributes_data_intro va wr (unsome (value_to_bool v)) co) 
  | pattr_config, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_data_of (attributes_data_intro va wr en (unsome (value_to_bool v)))
  | pattr_getter, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_accessor_of (attributes_accessor_intro v value_undefined en co)
  | pattr_setter, attributes_data_of (attributes_data_intro va wr en co) =>
    attributes_accessor_of (attributes_accessor_intro value_undefined v en co)
  end.

(* Desugaring function *)

Parameter desugar_expr : string -> option expr.

Definition _ascii_of_int (i : int) : Ascii.ascii := Ascii.ascii_of_N (Z.to_N i).

Definition _int_of_ascii (c : Ascii.ascii) : int := Z.of_N (Ascii.N_of_ascii c).

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
