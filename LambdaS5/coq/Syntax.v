Require Import List.
Require Import Coq.Strings.String.
Require Import Fappli_IEEE Fappli_IEEE_bits.


(* Data structures, created by the parser (in caml/ljs/ljs_parser.mly *)

(* This is mostly a Coq translation of the data structures defined in the
* original LambdaJS interpreter. *)


Definition id : Type := string.

Definition number : Type := Fappli_IEEE_bits.binary64.

Inductive unary_op : Type :=
| unary_op_print
| unary_op_pretty
| unary_op_strlen
| unary_op_typeof
| unary_op_is_primitive
| unary_op_abs
| unary_op_void
| unary_op_floor
| unary_op_prim_to_str
| unary_op_prim_to_num
| unary_op_prim_to_bool
| unary_op_not
| unary_op_numstr_to_num
(* not yet implemeted *)
| unary_op_is_closure 
| unary_op_object_to_string
| unary_op_is_array
| unary_op_to_int32
| unary_op_ceil
| unary_op_log
| unary_op_ascii_ntoc
| unary_op_ascii_cton
| unary_op_to_lower
| unary_op_to_upper
| unary_op_bnot
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
| binary_op_string_plus
| binary_op_char_at
| binary_op_is_accessor
| binary_op_prop_to_obj
(* not yet implemented *)
| binary_op_band
| binary_op_bor
| binary_op_bxor
| binary_op_shiftl
| binary_op_shiftr
| binary_op_zfshiftr
| binary_op_abs_eq
| binary_op_string_lt
| binary_op_base
| binary_op_locale_compare
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
