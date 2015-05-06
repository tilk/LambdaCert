Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import String.
Require Import Coq.Strings.String.
Require LibStream.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope container_scope.

(* Basic stuff *)

Definition id : Type := string.
Definition object_ptr := nat.

(* Syntax of S5 *)

Inductive unary_op : Type :=
| unary_op_print
| unary_op_pretty
| unary_op_strlen
| unary_op_typeof
| unary_op_is_primitive
| unary_op_is_closure 
| unary_op_is_object
| unary_op_abs
| unary_op_floor
| unary_op_prim_to_str
| unary_op_prim_to_num
| unary_op_prim_to_bool
| unary_op_not
| unary_op_bnot
| unary_op_to_int32
| unary_op_ascii_ntoc
| unary_op_ascii_cton
(* not yet implemeted *)
| unary_op_object_to_string
| unary_op_ceil
| unary_op_log
| unary_op_to_lower
| unary_op_to_upper
| unary_op_sin
| unary_op_current_utc_millis
.

Inductive binary_op : Type :=
| binary_op_add
| binary_op_sub
| binary_op_mul
| binary_op_div
| binary_op_mod
| binary_op_lt
| binary_op_le
| binary_op_gt 
| binary_op_ge
| binary_op_stx_eq
| binary_op_same_value
| binary_op_has_property
| binary_op_has_own_property
| binary_op_has_internal
| binary_op_string_plus
| binary_op_char_at
| binary_op_is_accessor
| binary_op_band
| binary_op_bor
| binary_op_bxor
| binary_op_shiftl
| binary_op_shiftr
| binary_op_zfshiftr
| binary_op_string_lt
| binary_op_locale_compare
(* not yet implemented *)
| binary_op_base
| binary_op_pow
| binary_op_to_fixed
.

Inductive oattr : Type := (* object attribute name *)
| oattr_proto
| oattr_class
| oattr_extensible
| oattr_code
.

Inductive pattr : Type := (* property attribute name *)
| pattr_value
| pattr_getter
| pattr_setter
| pattr_config
| pattr_writable
| pattr_enum
.

Inductive expr : Type :=
| expr_empty
| expr_null
| expr_undefined
| expr_string : string -> expr
| expr_number : number -> expr
| expr_bool : bool -> expr
| expr_id : id -> expr
| expr_object : objattrs -> list (string * expr) -> list (string * property) -> expr
| expr_get_attr : pattr -> expr -> expr -> expr (* property -> object -> field_name -> expr *)
| expr_set_attr : pattr -> expr -> expr -> expr -> expr (* property -> object -> field_name -> new_value -> expr *)
| expr_get_obj_attr : oattr -> expr -> expr
| expr_set_obj_attr : oattr -> expr -> expr -> expr
| expr_get_field : expr -> expr -> expr (* object -> field -> expr *)
| expr_set_field : expr -> expr -> expr -> expr (* object -> field -> new_val -> expr *)
| expr_delete_field : expr -> expr -> expr (* object -> field -> expr *)
| expr_get_internal : string -> expr -> expr
| expr_set_internal : string -> expr -> expr -> expr
| expr_own_field_names : expr -> expr
| expr_op1 : unary_op -> expr -> expr
| expr_op2 : binary_op -> expr -> expr -> expr
| expr_if : expr -> expr -> expr -> expr
| expr_app : expr -> list expr -> expr
| expr_seq : expr -> expr -> expr
| expr_jseq : expr -> expr -> expr (* JS-like sequence operator *)
| expr_let : id -> expr -> expr -> expr
| expr_recc : id -> expr -> expr -> expr (* Value bound must be lambda *)
| expr_label : id -> expr -> expr
| expr_break : id -> expr -> expr
| expr_try_catch : expr -> expr -> expr (* Catch block must be a lambda *)
| expr_try_finally : expr -> expr -> expr
| expr_throw : expr -> expr
| expr_lambda : list id -> expr -> expr
| expr_eval : expr -> expr -> expr (* string -> env_object -> expr *)
| expr_hint : string -> expr -> expr
| expr_fail : string -> expr (* used for asserts *)
| expr_dump : expr (* special - for dumping the context in the interpreter *)
with data : Type :=
| data_intro : expr -> expr -> expr -> expr -> data (* expr -> writable -> enumerable -> configurable -> data *)
with accessor : Type :=
| accessor_intro : expr -> expr -> expr -> expr -> accessor (* getter -> setter -> enumerable -> configurable -> accessor *)
with property : Type := 
| property_data : data -> property 
| property_accessor : accessor -> property
with objattrs : Type :=
| objattrs_intro : expr -> expr -> expr -> expr -> objattrs (* class -> extensible -> prototype -> code -> objattrs *)
.

Fixpoint expr_fv e : finset id := match e with
| expr_empty
| expr_null
| expr_undefined
| expr_string _  
| expr_number _ 
| expr_bool _ 
| expr_fail _
| expr_dump => \{}
| expr_id i => \{i}
| expr_object oa ips ps => 
    objattrs_fv oa \u 
    List.fold_left (fun x y => x \u y) 
        (List.map (fun (x : string * expr) => let (_, e) := x in expr_fv e) ips) \{} \u
    List.fold_left (fun x y => x \u y) 
        (List.map (fun (x : string * property) => let (_, p) := x in property_fv p) ps) \{} 
| expr_get_attr _ e1 e2 => expr_fv e1 \u expr_fv e2
| expr_set_attr _ e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_get_obj_attr _ e1 => expr_fv e1 
| expr_set_obj_attr _ e1 e2 => expr_fv e1 \u expr_fv e2 
| expr_get_field e1 e2 => expr_fv e1 \u expr_fv e2
| expr_set_field e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_delete_field e1 e2 => expr_fv e1 \u expr_fv e2
| expr_get_internal _ e1 => expr_fv e1
| expr_set_internal _ e1 e2 => expr_fv e1 \u expr_fv e2
| expr_own_field_names e => expr_fv e
| expr_op1 _ e => expr_fv e
| expr_op2 _ e1 e2 => expr_fv e1 \u expr_fv e2
| expr_if e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_app e es => expr_fv e \u List.fold_left (fun x y => x \u y) (List.map expr_fv es) \{} 
| expr_seq e1 e2 => expr_fv e1 \u expr_fv e2
| expr_jseq e1 e2 => expr_fv e1 \u expr_fv e2
| expr_let i e1 e2 => expr_fv e1 \u (expr_fv e2 \-- i)
| expr_recc i e1 e2 => (expr_fv e1 \u expr_fv e2) \-- i
| expr_label _ e => expr_fv e
| expr_break _ e => expr_fv e
| expr_try_catch e1 e2 => expr_fv e1 \u expr_fv e2
| expr_try_finally e1 e2 => expr_fv e1 \u expr_fv e2
| expr_throw e => expr_fv e
| expr_lambda is e => expr_fv e \- from_list is
| expr_eval e1 e2 => expr_fv e1 \u expr_fv e2
| expr_hint _ e => expr_fv e
end
with objattrs_fv oa := match oa with
| objattrs_intro e1 e2 e3 e4 => expr_fv e1 \u expr_fv e2 \u expr_fv e3 \u expr_fv e4 
end
with property_fv p := match p with
| property_data (data_intro e1 e2 e3 e4) => expr_fv e1 \u expr_fv e2 \u expr_fv e3 \u expr_fv e4
| property_accessor (accessor_intro e1 e2 e3 e4) => expr_fv e1 \u expr_fv e2 \u expr_fv e3 \u expr_fv e4
end
.

Fixpoint expr_seqs es :=
    match es with
    | nil => expr_undefined
    | [e] => e
    | e :: es' => expr_seq e (expr_seqs es')
    end.

Definition expr_true := expr_bool true.
Definition expr_false := expr_bool false.

Definition default_objattrs := objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined.

Definition objattrs_with_proto p oa := let 'objattrs_intro cl ex pr co := oa in objattrs_intro cl ex p co.

(* Values *)

Inductive value : Type :=
| value_empty
| value_null
| value_undefined
| value_number : number -> value
| value_string : string -> value
| value_bool : bool -> value
| value_object : object_ptr -> value
| value_closure : closure -> value 
with closure := 
| closure_intro : list (id * value) -> option id -> list id -> expr -> closure
.

Definition value_true := value_bool true.
Definition value_false := value_bool false.

Definition closure_body clo :=
  let 'closure_intro _ _ _ body := clo in body.

(* Lexical environments *)

Definition ctx := finmap id value.

(* Named data property attributes *)
Record attributes_data := attributes_data_intro {
   attributes_data_value : value;
   attributes_data_writable : bool;
   attributes_data_enumerable : bool;
   attributes_data_configurable : bool }.

(* Named accessor property attributes *)
Record attributes_accessor := attributes_accessor_intro {
   attributes_accessor_get : value;
   attributes_accessor_set : value;
   attributes_accessor_enumerable : bool;
   attributes_accessor_configurable : bool }.

(* Property attributes *)
Inductive attributes :=
  | attributes_data_of : attributes_data -> attributes
  | attributes_accessor_of : attributes_accessor -> attributes.

Definition prop_name := string.
Definition class_name := string.
Definition object_props := finmap prop_name attributes.

Record oattrs := oattrs_intro {
   oattrs_proto : value;
   oattrs_class : class_name;
   oattrs_extensible : bool;
   oattrs_code : value 
}.

Record object := object_intro {
   object_attrs : oattrs;
   object_properties : object_props;
   object_internal : finmap string value
}.

Definition object_proto obj := oattrs_proto (object_attrs obj).
Definition object_class obj := oattrs_class (object_attrs obj).
Definition object_extensible obj := oattrs_extensible (object_attrs obj).
Definition object_code obj := oattrs_code (object_attrs obj).

Definition default_oattrs : oattrs := {|
  oattrs_proto := value_null;
  oattrs_class := "Object";
  oattrs_extensible := true;
  oattrs_code := value_null
|}.

Definition default_object : object := {|
  object_attrs := default_oattrs;
  object_properties := \{};
  object_internal := \{}
|}.

Definition object_with_properties props obj :=
  let 'object_intro x1 x2 x3:= obj in
  object_intro x1 props x3.

(* Representation of the store *)

Definition store := finmap object_ptr object.

Definition create_store : store := \{}.

Definition create_ctx : ctx := \{}.

(* Definitions of outcomes *)

Inductive res := 
| res_value : value -> res
| res_exception : value -> res
| res_break : string -> value -> res
.

Inductive out :=
| out_div : out
| out_ter : store -> res -> out
.

(* Type of interpreter results *)
(* Interpreter functions can either succeed or fail in several ways.
 * The result type is usually out, the type of outcomes. *)
 
Inductive resultof (T : Type) : Type :=
| result_some : T -> resultof T
| result_fail : string -> resultof T        (* program error *)
| result_impossible : string -> resultof T  (* inconsistency *)
| result_bottom : resultof T                (* out of fuel *)
| result_dump : ctx -> store -> resultof T  (* dump state *)
.
Implicit Arguments result_some [[T]].
Implicit Arguments result_fail [[T]].
Implicit Arguments result_impossible [[T]].
Implicit Arguments result_bottom [[T]].
Implicit Arguments result_dump [[T]].

Definition result := resultof out.

Definition result_res st (r : res) : result := result_some (out_ter st r).
Definition result_value st (v : value) : result := result_res st (res_value v).
Definition result_exception st (v : value) : result := result_res st (res_exception v).
Definition result_break st (l : string) (v : value) : result := result_res st (res_break l v).

Definition return_bool store (b : bool) :=
  result_value store (value_bool b).


