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
| expr_null
| expr_undefined
| expr_string : string -> expr
| expr_number : number -> expr
| expr_true
| expr_false
(* | expr_id : id -> expr *)
| expr_var_id : id -> expr
| expr_var_decl : list id -> expr -> expr
| expr_var_set : id -> expr -> expr
| expr_array : list expr -> expr
| expr_object : list (string * property) -> expr
| expr_this : expr
| expr_get_field : expr -> expr -> expr
| expr_new : expr -> list expr -> expr
| expr_op1 : J.unary_op -> expr -> expr
| expr_op2 : J.binary_op -> expr -> expr -> expr
| expr_if : expr -> expr -> expr -> expr
| expr_set_field :  expr -> expr -> expr -> expr
| expr_app : expr -> list expr -> expr
| expr_func : list id -> expr -> expr
(* | expr_let : id -> expr -> expr -> expr *)
| expr_seq : expr -> expr -> expr
(*
| expr_do_while : expr -> expr -> expr 
*)
| expr_while : expr -> expr -> expr -> expr (* test, body, after *) 
| expr_label : id -> expr -> expr
| expr_break : id -> expr -> expr
| expr_for_in : id -> expr -> expr -> expr
| expr_try_catch : expr -> id -> expr -> expr
| expr_try_finally : expr -> expr -> expr
| expr_throw : expr -> expr
| expr_switch : expr -> list case -> expr
| expr_func_stmt : id -> list id -> expr -> expr
| expr_with : expr -> expr -> expr
| expr_strict : expr -> expr
| expr_nonstrict : expr -> expr
| expr_syntaxerror : expr
with property : Type :=
| property_data : expr -> property
| property_getter : expr -> property
| property_setter : expr -> property
with case : Type :=
| case_case : expr -> expr -> case
| case_default : expr -> case
.

Fixpoint expr_seqs es :=
    match es with
    | nil => expr_undefined
    | [e] => e
    | e :: es' => expr_seq e (expr_seqs es')
    end.
