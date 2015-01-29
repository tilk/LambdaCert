Require Import String.
Require Import JsNumber.
Require Import Coq.Strings.String.

Definition id : Type := string.

Inductive expr : Type := 
| expr_null
| expr_undefined
| expr_string : string -> expr
| expr_number : number -> expr
| expr_true
| expr_false
| expr_id : id -> expr
| expr_array : list expr -> expr
| expr_object : list (string * property) -> expr
| expr_this : expr
| expr_bracket : expr -> expr -> expr
| expr_new : expr -> list expr -> expr
(* expr_prefix *)
(* expr_infix *)
| expr_if : expr -> expr -> expr -> expr
| expr_assign :  expr -> expr -> expr -> expr
| expr_app : expr -> list expr -> expr
| expr_func : list id -> expr -> expr
| expr_let : id -> expr -> expr
| expr_seq : expr -> expr -> expr
| expr_while : expr -> expr
| expr_label : id -> expr -> expr
| expr_break : id -> expr -> expr
| expr_for_in : id -> expr -> expr -> expr
| expr_try_catch : expr -> id -> expr -> expr
| expr_try_finally : expr -> expr -> expr
| expr_throw : expr -> expr
| expr_switch : expr -> list case -> expr
| expr_func_stmt : id -> list id -> expr
| expr_with : expr -> expr -> expr
| expr_strict : expr -> expr
| expr_nonstrict : expr -> expr
with property : Type :=
| property_data : expr -> property
| property_getter : id -> expr -> property
| property_setter : id -> expr -> property
with case : Type :=
| case_case : expr -> expr -> case
| case_default : expr -> case
.