Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Export LjsSyntax.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Global Instance value_inhab : Inhab value.
Proof.
    intros. apply (prove_Inhab value_undefined).
Qed.

Inductive pure_expr : ctx -> expr -> Prop :=
| pure_expr_empty : forall c, pure_expr c expr_empty
| pure_expr_null : forall c, pure_expr c expr_null
| pure_expr_undefined : forall c, pure_expr c expr_undefined
| pure_expr_string : forall c s, pure_expr c (expr_string s)
| pure_expr_number : forall c n, pure_expr c (expr_number n)
| pure_expr_true : forall c, pure_expr c expr_true
| pure_expr_false : forall c, pure_expr c expr_false
| pure_expr_id : forall c i, index c i -> pure_expr c (expr_id i)
| pure_expr_if : forall c e1 e2 e3, 
    pure_expr c e1 -> pure_expr c e2 -> pure_expr c e3 -> 
    pure_expr c (expr_if e1 e2 e3)
| pure_expr_seq : forall c e1 e2, 
    pure_expr c e1 -> pure_expr c e2 ->
    pure_expr c (expr_seq e1 e2)
.
