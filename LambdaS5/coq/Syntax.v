Require Import List.
Require Import Coq.Strings.String.
Require Import Fappli_IEEE Fappli_IEEE_bits.


(* Data structures, created by the parser (in caml/ljs/ljs_parser.mly *)

(* This is mostly a Coq translation of the data structures defined in the
* original LambdaJS interpreter. *)


Definition id : Type := string.

Definition number : Type := Fappli_IEEE_bits.binary64.

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
| expr_op1 : string -> expr -> expr
| expr_op2 : string -> expr -> expr -> expr
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
with data : Type :=
| data_intro : expr -> bool -> data (* expr -> writable -> data *)
with accessor : Type :=
| accessor_intro : expr -> expr -> accessor (* getter -> setter -> accessor *)
with property : Type := 
| property_data : data -> bool -> bool -> property (* value -> enumerable -> configurable *)
| property_accessor : accessor -> bool -> bool -> property
with objattrs : Type :=
| objattrs_intro : option expr -> option expr -> option expr -> string -> bool -> objattrs (* primval -> code -> prototype -> class -> extensible -> objattrs *)
.

Definition default_objattrs := objattrs_intro None None None "Object" true.
