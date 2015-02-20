Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import JsNumber.
Require Import Coq.Strings.String.
Import List.ListNotations.

Open Scope list_scope.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Lemma out_red_ter : forall c st st' ee r o,
    red_expr c st ee (out_ter st' r) -> out_of_ext_expr ee = Some o -> exists st'' r', o = out_ter st'' r'.
Proof.
    introv Hred Hout.
    unfolds in Hout;
    inverts Hred; tryfalse; injects; jauto.
Qed.
 
Module Export Tactics.

Ltac ljs_out_red_ter Hred :=
    let H := fresh in
    forwards (?st&?r&H) : out_red_ter Hred; [reflexivity | ]; 
    match type of H with ?x = _ => is_var x end; 
    rewrite H in *; clear H.

Tactic Notation "ljs_out_red_ter" "in" hyp(Hred) := ljs_out_red_ter Hred.

Tactic Notation "ljs_out_red_ter" := match goal with 
    | H : red_expr _ _ _ (out_ter _ _) |- _ => ljs_out_red_ter in H
    end.

End Tactics.
