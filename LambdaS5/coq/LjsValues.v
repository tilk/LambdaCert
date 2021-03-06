Require Import Utils.
Require Import String.
Require Import JsNumber.
Require Import LjsShared.
Require Import LjsSyntax.
Open Scope list_scope.
Open Scope string_scope.

(* LambdaJS values and objects *)

Definition value_to_bool (v : value) : option bool :=
  match v with
  | value_bool b => Some b
  | _ => None
  end
.

Definition value_to_string v : option string :=
  match v with
  | value_string s => Some s
  | _ => None
  end
.

Definition attributes_data_value_update data v :=
  let 'attributes_data_intro _v w e c := data in attributes_data_intro v w e c
.

Definition attributes_enumerable attr :=
  match attr with
  | attributes_data_of data => attributes_data_enumerable data
  | attributes_accessor_of acc => attributes_accessor_enumerable acc
  end
.

Definition attributes_configurable attr :=
  match attr with
  | attributes_data_of data => attributes_data_configurable data
  | attributes_accessor_of acc => attributes_accessor_configurable acc
  end
.

Fixpoint name_in_list (name : prop_name) (names : list prop_name) : bool :=
  match names with
  | nil => false
  | hd :: tl =>
    if (decide(name = hd)) then
      true
    else
      name_in_list name tl
  end
.

Definition get_object_property (object : object) (name : prop_name) : option attributes :=
  object_properties object \( name ?)
.
Definition set_object_property (obj : object) (name : prop_name) (attrs : attributes) : object :=
  let 'object_intro ps props iprops := obj in object_intro ps (props \( name :=  attrs)) iprops
.
Definition delete_object_property (obj : object) (name : prop_name) : object :=
  let 'object_intro ps props iprops := obj in object_intro ps (props \-- name) iprops
.
Definition set_object_internal obj s v :=
  let 'object_intro ps props iprops := obj in object_intro ps props (iprops \(s := v))
.

Definition make_prop_list_aux (left : nat * object_props) (val : string) : nat * object_props :=
  match left with
  | (nb_entries, attrs) =>
    let attr := attributes_data_of (attributes_data_intro (value_string val) false false false) in
    (S nb_entries, attrs \(Utils.string_of_nat nb_entries := attr))
  end
.
Definition make_prop_list obj : object :=
  match List.fold_left make_prop_list_aux (List.map fst (to_list (object_properties obj))) (0, \{}) with
  | (nb_entries, attrs) =>
    let length := value_number (JsNumber.of_int nb_entries) in
    let length_attr := attributes_data_of (attributes_data_intro length false false false) in
    let props := attrs \( "length" := length_attr ) in
    {| 
      object_attrs := {|
        oattrs_proto := value_null;
        oattrs_class := "Internal"; 
        oattrs_extensible := false;
        oattrs_code := value_null 
      |};
      object_properties := props;
      object_internal := \{}
    |}
  end
.

