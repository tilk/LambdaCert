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

Lemma value_to_closure_deterministic : forall st v clo clo',
    value_to_closure st v clo -> value_to_closure st v clo' -> clo = clo'.
Proof.
    introv Hc1.
    induction Hc1; introv Hc2; inverts Hc2.
    reflexivity.
    binds_determine.
    substs.
    auto.
Qed.

Lemma closure_ctx_deterministic : forall clo lv c c',
    closure_ctx clo lv c -> closure_ctx clo lv c' -> c = c'.
Proof.
    introv Hc1.
    induction Hc1; introv Hc2; inverts Hc2;
    repeat match goal with H : Zip _ _ _ |- _ => apply Zip_zip in H end;
    rewrite H in *; injects; reflexivity.
Qed.

Module Export Tactics.

Ltac value_to_closure_determine :=
    match goal with
    | H1 : value_to_closure ?st ?v ?clo1, H2 : value_to_closure ?st ?v ?clo2 |- _ =>
        not constr_eq clo1 clo2; 
        not is_hyp (clo1 = clo2);
        let H := fresh "H" in asserts H : (clo1 = clo2); [eauto using value_to_closure_deterministic | idtac]
    end.

Ltac closure_ctx_determine :=
    match goal with
    | H1 : closure_ctx ?clo ?lv ?c1, H2 : closure_ctx ?clo ?lv ?c2 |- _ =>
        not constr_eq c1 c2; 
        not is_hyp (c1 = c2);
        let H := fresh "H" in asserts H : (c1 = c2); [eauto using closure_ctx_deterministic | idtac]
    end.

Ltac ljs_out_red_ter Hred :=
    let H := fresh in
    forwards (?st&?r&H) : out_red_ter Hred; [reflexivity | ]; 
    match type of H with ?x = _ => is_var x end; 
    rewrite H in *; clear H.

Tactic Notation "ljs_out_red_ter" "in" constr(Hred) := ljs_out_red_ter Hred.

Tactic Notation "ljs_out_red_ter" := match goal with 
    | H : red_expr _ _ _ (out_ter _ _) |- _ => ljs_out_red_ter in H
    end.

End Tactics.
