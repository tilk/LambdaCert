Require Import String.
Require Import JsNumber.
Require Import Coq.Strings.String.
Require JsSyntax.
Import ListNotations.
Open Scope list_scope.

Module J := JsSyntax.

Definition id : Type := string.

Definition unary_op := J.unary_op.
Definition binary_op := J.binary_op.

Inductive expr : Type := 
| expr_empty
| expr_null
| expr_undefined
| expr_string : string -> expr
| expr_number : number -> expr
| expr_true
| expr_false
(* | expr_id : id -> expr *)
| expr_var_id : id -> expr
| expr_var_set : id -> expr -> expr
| expr_array : list (option expr) -> expr
| expr_object : list (string * property) -> expr
| expr_this : expr
| expr_get_field : expr -> expr -> expr
| expr_new : expr -> list expr -> expr
| expr_op1 : J.unary_op -> expr -> expr
| expr_op2 : J.binary_op -> expr -> expr -> expr
| expr_if : expr -> expr -> expr -> expr
| expr_set_field :  expr -> expr -> expr -> expr
| expr_app : expr -> list expr -> expr
| expr_func : option id -> list id -> prog -> string -> expr (* the string is program text *)
| expr_func_stmt : id -> list id -> prog -> string -> expr (* TODO find way to remove it *)
(* | expr_let : id -> expr -> expr -> expr *)
| expr_fseq : expr -> expr -> expr
| expr_seq : expr -> expr -> expr
| expr_do_while : expr -> expr -> expr 
| expr_while : expr -> expr -> expr -> expr (* test, body, after *) 
| expr_label : id -> expr -> expr
| expr_break : id -> expr -> expr
| expr_for_in : id -> expr -> expr -> expr
| expr_try_catch : expr -> id -> expr -> expr
| expr_try_finally : expr -> expr -> expr
| expr_throw : expr -> expr
| expr_switch : expr -> switchbody -> expr
| expr_with : expr -> expr -> expr
| expr_noop : expr -> expr
| expr_syntaxerror : expr
with prog : Type :=
| prog_intro : bool -> list id -> expr -> prog
with property : Type :=
| property_data : expr -> property
| property_getter : expr -> property
| property_setter : expr -> property
with switchbody : Type :=
| switchbody_nodefault : list (expr * expr) -> switchbody
| switchbody_withdefault : list (expr * expr) -> expr -> list (expr * expr) -> switchbody
.

Definition expr_seqs es := fold_left (fun e1 e2 => expr_seq e2 e1) expr_empty es.

Definition prog_strictness p := match p with prog_intro b _ _ => b end.
