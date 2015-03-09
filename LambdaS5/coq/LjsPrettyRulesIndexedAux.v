Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesAux.
Require Import LjsPrettyRulesIndexed.
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

(* Induction on height helpers *)

Local Hint Constructors red_expr red_exprh.

Lemma red_expr_forget_h : forall k c st ee o, red_exprh k c st ee o -> red_expr c st ee o.
Proof.
    introv H. induction* H.
Qed.

Local Hint Extern 1 ((_ < _)%nat) => omega.

Lemma red_exprh_lt : forall k k' c st ee o, 
    red_exprh k c st ee o -> (k < k')%nat -> red_exprh k' c st ee o.
Proof.
    introv H. gen k'. induction H; introv L; (destruct k' as [|k']; [false; omega | auto*]).
Qed.

Lemma red_expr_add_h : forall c st e o, red_expr c st e o -> exists k, red_exprh k c st e o.
Proof.
    hint red_exprh_lt. introv H. induction H; induct_height. 
Qed.

(* Useful tactics and lemmas *)

Lemma red_exprh_general_abort : forall k c st ee o,
    out_of_ext_expr ee = Some o -> abort o -> ~abort_intercepted_expr ee ->
    red_exprh k c st ee o. 
Proof.
    introv Ho Ha Hi.
    destruct ee; (injects Ho || discriminate Ho); jauto; 
    (inverts Ha as Hc; [|inverts Hc]).
    eapply red_exprh_label_1; fequals.
    eapply red_exprh_label_1; fequals.
    destruct (classic (i = i0)). substs.
    specializes Hi abort_intercepted_expr_label_1; false.
    eapply red_exprh_label_1; fequals.
    eapply red_exprh_try_catch_1; fequals.
    specializes Hi abort_intercepted_expr_try_catch_1; false.
    eapply red_exprh_try_catch_1; fequals.
    eapply red_exprh_try_finally_1_div.
    specializes Hi abort_intercepted_expr_try_finally_1; false.
    specializes Hi abort_intercepted_expr_try_finally_1; false.
Qed.

Module Export Tactics.

Ltac ljs_abort_false := match goal with
    | H : abort (out_ter _ (res_value _)) |- _ => 
        let H1 := fresh "H" in 
        solve [invert H as H1; inverts H1]
    end.

Tactic Notation "ljs_out_redh_ter" "in" hyp(Hred) := ljs_out_red_ter in (red_expr_forget_h Hred).

Tactic Notation "ljs_out_redh_ter" := match goal with 
    | H : red_exprh _ _ _ _ (out_ter _ _) |- _ => ljs_out_redh_ter in H
    end.

End Tactics.

Local Ltac determine := 
    match goal with
    | H1 : ?a = _, H2 : ?a = _ |- _ => rewrite H1 in H2; injects H2
    | H1 : _ = ?a, H2 : _ = ?a |- _ => rewrite <- H1 in H2; injects H2
    end.

Local Ltac inst_hyps_det := 
    match goal with
    | H1 : red_exprh _ ?c ?st ?e ?o1, H2 : forall k o, red_exprh k ?c ?st ?e o -> ?o2 = o |- _ =>
        (not constr_eq o1 o2);
        let H := fresh "H" in forwards H : H2 H1; subst o2
    end.

Local Ltac binds_determine :=
    match goal with
    | H1 : binds ?m ?k ?v1, H2 : binds ?m ?k ?v2 |- _ =>
        (not constr_eq v1 v2); 
        let H := fresh "H" in asserts H : (v1 = v2); [skip | subst v1] (* TODO remove skip! *)
    end.

Lemma red_exprh_deterministic : forall k k' c st ee o o',
    red_exprh k c st ee o -> red_exprh k' c st ee o' -> o = o'.
Proof.
    introv Hr1. generalize k' o'.
    induction Hr1; introv Hr2;
    (inversions Hr2; repeat (determine || binds_determine || inst_hyps_det); eauto; try ljs_abort_false; tryfalse);
    false; jauto.
Qed.
