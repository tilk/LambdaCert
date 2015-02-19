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
