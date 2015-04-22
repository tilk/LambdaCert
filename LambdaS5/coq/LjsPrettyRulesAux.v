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

Lemma object_property_is_deterministic : forall st obj name oattr oattr',
    object_property_is st obj name oattr -> object_property_is st obj name oattr' -> oattr = oattr'.
Proof.
    introv Ho1.
    induction Ho1; introv Ho2; inverts Ho2; 
    repeat binds_determine; substs; tryfalse; try reflexivity; try (false; prove_bag). 
    rewrite H0 in H3.
    injects.
    binds_determine; substs.
    auto.
Qed.

Lemma value_is_closure_deterministic : forall st v clo clo',
    value_is_closure st v clo -> value_is_closure st v clo' -> clo = clo'.
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

Lemma eval_unary_op_deterministic : forall op st v0 v v',
    eval_unary_op op st v0 v -> eval_unary_op op st v0 v' -> v = v'.
Proof.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    reflexivity.
Qed.

Lemma eval_binary_op_deterministic : forall op st v1 v2 v v',
    eval_binary_op op st v1 v2 v -> eval_binary_op op st v1 v2 v' -> v = v'.
Proof.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    repeat binds_determine; try reflexivity.
    rewrite H1 in *. injects. reflexivity. 
    lets X : object_property_is_deterministic H1 H5. injects. reflexivity.
Qed.

Module Export Tactics.

Ltac object_property_is_determine_then :=
    match goal with
    | H1 : object_property_is ?st ?obj ?name ?oattr1, H2 : object_property_is ?st ?obj ?name ?oattr2 |- _ =>
        not constr_eq oattr1 oattr2; 
        not is_hyp (oattr1 = oattr2);
        let H := fresh "H" in asserts H : (oattr1 = oattr2); [eauto using object_property_is_deterministic | idtac];
        revert H
    end.

Ltac object_property_is_determine_eq := object_property_is_determine_then; intro.
Ltac object_property_is_determine := object_property_is_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac value_is_closure_determine_then :=
    match goal with
    | H1 : value_is_closure ?st ?v ?clo1, H2 : value_is_closure ?st ?v ?clo2 |- _ =>
        not constr_eq clo1 clo2; 
        not is_hyp (clo1 = clo2);
        let H := fresh "H" in asserts H : (clo1 = clo2); [eauto using value_is_closure_deterministic | idtac];
        revert H
    end.

Ltac value_is_closure_determine_eq := value_is_closure_determine_then; intro.
Ltac value_is_closure_determine := value_is_closure_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac closure_ctx_determine_then :=
    match goal with
    | H1 : closure_ctx ?clo ?lv ?c1, H2 : closure_ctx ?clo ?lv ?c2 |- _ =>
        not constr_eq c1 c2; 
        not is_hyp (c1 = c2);
        let H := fresh "H" in asserts H : (c1 = c2); [eauto using closure_ctx_deterministic | idtac];
        revert H
    end.

Ltac closure_ctx_determine_eq := closure_ctx_determine_then; intro.
Ltac closure_ctx_determine := closure_ctx_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac eval_unary_op_determine_then :=
    match goal with
    | H1 : eval_unary_op ?op ?st ?v0 ?v1, H2 : eval_unary_op ?op ?st ?v0 ?v2 |- _ =>
        not constr_eq v1 v2; 
        not is_hyp (v1 = v2);
        let H := fresh "H" in asserts H : (v1 = v2); [eauto using eval_unary_op_deterministic | idtac];
        revert H
    end.

Ltac eval_unary_op_determine_eq := eval_unary_op_determine_then; intro.
Ltac eval_unary_op_determine := eval_unary_op_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac eval_binary_op_determine_then :=
    match goal with
    | H1 : eval_binary_op ?op ?st ?v0 ?v0' ?v1, H2 : eval_binary_op ?op ?st ?v0 ?v0' ?v2 |- _ =>
        not constr_eq v1 v2; 
        not is_hyp (v1 = v2);
        let H := fresh "H" in asserts H : (v1 = v2); [eauto using eval_binary_op_deterministic | idtac];
        revert H
    end.

Ltac eval_binary_op_determine_eq := eval_binary_op_determine_then; intro.
Ltac eval_binary_op_determine := eval_binary_op_determine_then; let H := fresh in intro H; try subst_hyp H.

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
