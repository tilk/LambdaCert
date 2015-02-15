Require Import Utils.
Require Import String.
Require Import JsNumber.
Require Import Coq.Strings.String.
Require LibStream.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* Basic stuff *)

Definition id : Type := string.
Definition closure_id := nat.
Definition value_loc := nat.
Definition object_ptr := nat.

(* Syntax of S5 *)

Inductive unary_op : Type :=
| unary_op_print
| unary_op_pretty
| unary_op_strlen
| unary_op_typeof
| unary_op_is_primitive
| unary_op_is_closure 
| unary_op_is_array
| unary_op_abs
| unary_op_void
| unary_op_floor
| unary_op_prim_to_str
| unary_op_prim_to_num
| unary_op_prim_to_bool
| unary_op_not
| unary_op_bnot
| unary_op_numstr_to_num
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
| binary_op_abs_eq
| binary_op_same_value
| binary_op_has_property
| binary_op_has_own_property
| binary_op_string_plus
| binary_op_char_at
| binary_op_is_accessor
| binary_op_prop_to_obj
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
| oattr_primval
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
| expr_null
| expr_undefined
| expr_string : string -> expr
| expr_number : number -> expr
| expr_true
| expr_false
| expr_id : id -> expr
| expr_object : objattrs -> list (string * property) -> expr
| expr_get_attr : pattr -> expr -> expr -> expr (* property -> object -> field_name -> expr *)
| expr_set_attr : pattr -> expr -> expr -> expr -> expr (* property -> object -> field_name -> new_value -> expr *)
| expr_get_obj_attr : oattr -> expr -> expr
| expr_set_obj_attr : oattr -> expr -> expr -> expr
| expr_get_field : expr -> expr -> expr -> expr (* left -> right -> args_object -> expr *)
| expr_set_field : expr -> expr -> expr -> expr -> expr (* object -> field -> new_val -> args -> expr *)
| expr_delete_field : expr -> expr -> expr (* object -> field -> expr *)
| expr_own_field_names : expr -> expr
| expr_set_bang : id -> expr -> expr
| expr_op1 : unary_op -> expr -> expr
| expr_op2 : binary_op -> expr -> expr -> expr
| expr_if : expr -> expr -> expr -> expr
| expr_app : expr -> list expr -> expr
| expr_seq : expr -> expr -> expr
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
| expr_dump : expr (* special - for dumping the context in the interpreter *)
with data : Type :=
| data_intro : expr -> expr -> expr -> expr -> data (* expr -> writable -> enumerable -> configurable -> data *)
with accessor : Type :=
| accessor_intro : expr -> expr -> expr -> expr -> accessor (* getter -> setter -> enumerable -> configurable -> accessor *)
with property : Type := 
| property_data : data -> property 
| property_accessor : accessor -> property
with objattrs : Type :=
| objattrs_intro : expr -> expr -> expr -> expr -> expr -> objattrs (* class -> extensible -> prototype -> code -> primval -> objattrs *)
.

Fixpoint expr_fv e : Fset.fset id := match e with
| expr_null
| expr_undefined
| expr_string _  
| expr_number _ 
| expr_true
| expr_false 
| expr_dump => \{}
| expr_id i => \{i}
| expr_object oa ps => 
    objattrs_fv oa \u 
    List.fold_left (fun x y => x \u y) 
        (List.map (fun (x : string * property) => let (_, p) := x in property_fv p) ps) \{} 
| expr_get_attr _ e1 e2 => expr_fv e1 \u expr_fv e2
| expr_set_attr _ e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_get_obj_attr _ e1 => expr_fv e1 
| expr_set_obj_attr _ e1 e2 => expr_fv e1 \u expr_fv e2 
| expr_get_field e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_set_field e1 e2 e3 e4 => expr_fv e1 \u expr_fv e2 \u expr_fv e3 \u expr_fv e4
| expr_delete_field e1 e2 => expr_fv e1 \u expr_fv e2
| expr_own_field_names e => expr_fv e
| expr_set_bang i e => \{i} \u expr_fv e
| expr_op1 _ e => expr_fv e
| expr_op2 _ e1 e2 => expr_fv e1 \u expr_fv e2
| expr_if e1 e2 e3 => expr_fv e1 \u expr_fv e2 \u expr_fv e3
| expr_app e es => expr_fv e \u List.fold_left (fun x y => x \u y) (List.map expr_fv es) \{} 
| expr_seq e1 e2 => expr_fv e1 \u expr_fv e2
| expr_let i e1 e2 => expr_fv e1 \u (expr_fv e2 \-- i)
| expr_recc i e1 e2 => (expr_fv e1 \u expr_fv e2) \-- i
| expr_label _ e => expr_fv e
| expr_break _ e => expr_fv e
| expr_try_catch e1 e2 => expr_fv e1 \u expr_fv e2
| expr_try_finally e1 e2 => expr_fv e1 \u expr_fv e2
| expr_throw e => expr_fv e
| expr_lambda is e => expr_fv e \- Fset.from_list is
| expr_eval e1 e2 => expr_fv e1 \u expr_fv e2
| expr_hint _ e => expr_fv e
end
with objattrs_fv oa := match oa with
| objattrs_intro e1 e2 e3 e4 e5 => expr_fv e1 \u expr_fv e2 \u expr_fv e3 \u expr_fv e4 \u expr_fv e5
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

Definition expr_bool (b : bool) := if b then expr_true else expr_false.

Definition default_objattrs := objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined expr_undefined.

Definition objattrs_with_proto p oa := let 'objattrs_intro cl ex pr co pv := oa in objattrs_intro cl ex p co pv.

(* Lexical environments *)

Definition loc_heap_type := Heap.heap id value_loc.

Record ctx := ctx_intro {
  loc_heap : loc_heap_type (* maps names to locations *)
}.

(* Values *)

Inductive value : Type :=
| value_null
| value_undefined
| value_number : number -> value
| value_string : string -> value
| value_true
| value_false
| value_object : object_ptr -> value
| value_closure : closure_id -> ctx -> list id -> expr -> value (* closure_id is for making closures comparable with stx= *)
.

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
Definition object_properties := Heap.heap prop_name attributes.

Record object := object_intro {
   object_proto : value;
   object_class : class_name;
   object_extensible : bool;
   object_prim_value : value;
   object_properties_ : object_properties;
   object_code : value }.

Definition default_object : object := {|
  object_proto := value_null;
  object_class := "Object";
  object_extensible := true;
  object_prim_value := value_undefined;
  object_properties_ := Heap.empty;
  object_code := value_null
|}.

(* Representation of the store *)

Definition value_heap_type := Heap.heap value_loc value.
Definition object_heap_type := Heap.heap object_ptr object.

Record store := store_intro {
  object_heap : object_heap_type; (* simulates mutability of objects *)
  value_heap : value_heap_type; (* maps locations to values *)
  fresh_locations : LibStream.stream nat 
}.

Definition dummy_fresh_locations := nat_stream_from 1%nat.

Definition object_heap_initial : Heap.heap object_ptr object :=
  Heap.empty.
Definition value_heap_initial : Heap.heap value_loc value :=
  Heap.empty.
Definition loc_heap_initial : Heap.heap id value_loc :=
  Heap.empty.

Definition create_store :=
  {| object_heap := object_heap_initial;
     value_heap := value_heap_initial;
     fresh_locations := dummy_fresh_locations |}.

Definition create_ctx :=
  {| loc_heap := loc_heap_initial |}.

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
  result_value store (if b then value_true else value_false).


