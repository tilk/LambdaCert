Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Import LjsRulesCorrectSpecFuns.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Implicit Type A B : Type.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : L.id.
Implicit Type st : L.store.
Implicit Type e : L.expr.
Implicit Type v : L.value.
Implicit Type o : L.out.
Implicit Type c : L.ctx.
Implicit Type ptr : L.object_ptr.
Implicit Type obj : L.object.
Implicit Type re : L.result.
Implicit Type r : L.res.
Implicit Type props : L.object_props.

Implicit Type jst : J.state.
Implicit Type je : J.expr.
Implicit Type jt : J.stat.
Implicit Type jee : J.ext_expr.
Implicit Type jet : J.ext_stat.
Implicit Type jes : J.ext_spec.
Implicit Type jc : J.execution_ctx.
Implicit Type jo : J.out.
Implicit Type jr : J.res.
Implicit Type jv : J.value.
Implicit Type jptr : J.object_loc.
Implicit Type jobj : J.object.
Implicit Type jrv : J.resvalue.
Implicit Type jref : J.ref.
Implicit Type jl : J.label.
Implicit Type jer : J.env_record.
Implicit Type jeptr : J.env_loc.
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.
Implicit Type jlenv : J.lexical_env.

Definition afh k' k jvl := 
    map (fun k => nth_def (J.value_prim J.prim_undef) k jvl) (LibStream.take k (nat_stream_from k')).

Lemma afh_lemma_1 : forall jv jvl k k',
    afh (S k') k (jv :: jvl) = afh k' k jvl.
Proof.
    unfolds afh.
    induction k; introv; simpls; rew_map. reflexivity.
    rewrite IHk. reflexivity.
Qed.

Lemma afh_lemma_2 : forall k k',
    afh k' (S k) [] = J.value_prim J.prim_undef :: afh (S k') k [].
Proof.
    destruct k'; reflexivity.
Qed.

Lemma afh_lemma_3 : forall k jv jvl,
    afh 0 (S k) (jv :: jvl) = jv :: afh 1 k (jv :: jvl).
Proof.
    unfolds afh. introv. simpl. rew_map. reflexivity. 
Qed.

Lemma arguments_from_nil_lemma : forall k k',
    J.arguments_from [] (afh k' k []).
Proof.
    induction k; introv.
    + constructor.
    + rewrite afh_lemma_2. constructor. eauto. 
Qed.

Lemma arguments_from_lemma : forall jvl k,
    J.arguments_from jvl (afh 0 k jvl).
Proof.
    induction jvl; introv.
    + eapply arguments_from_nil_lemma.
    + destruct k.
      - constructor.
      - rewrite afh_lemma_3. rewrite afh_lemma_1. constructor. eauto.
Qed.

Ltac js_arguments_from := 
    match goal with
    | |- J.arguments_from ?jvl ?l =>
        let H := fresh in
        lets H : (arguments_from_lemma jvl (length l));
        cbv -[nth_def] in H; eapply H; clear H
    end.

Hint Extern 10 (J.arguments_from _ _) => js_arguments_from : js_ljs.

Opaque decide.

Lemma is_finite_lemma : forall k c st st' r n,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privIsFinite [L.value_number n]) (L.out_ter st' r) ->
    st = st' /\ r = L.res_value (L.value_bool 
        (!isTrue (n = JsNumber.nan \/ n = JsNumber.infinity \/ n = JsNumber.neg_infinity))).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    do 3 let Heq := fresh in
    cases_decide as Heq; rewrite same_value_number_eq_lemma in Heq; try subst_hyp Heq; repeat ljs_autoforward;
    [cases_isTrue as Hz; rew_logic in Hz; destruct_hyp Hz; rew_bool; eauto; tryfalse | idtac].
    cases_isTrue as Hz; rew_logic in Hz; destruct_hyp Hz; tryfalse.
    eauto.
Qed.

Lemma red_expr_call_global_is_finite_ok : forall k, ih_call k -> th_call_prealloc k J.prealloc_global_is_finite.
Proof.
    introv IHc Hcinv Hinv Hvrel Halo Hcrel Hvrels Hlred.
    inverts Hcrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort. 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : is_finite_lemma. destruct_hyp Hx.
    cases_isTrue;
    jauto_js.
Qed.

Lemma red_expr_call_global_is_nan_ok : forall k, ih_call k -> th_call_prealloc k J.prealloc_global_is_nan.
Proof.
    introv IHc Hcinv Hinv Hvrel Halo Hcrel Hvrels Hlred.
    inverts Hcrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort. 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite same_value_number_eq_lemma in Heq; try subst_hyp Heq;
    jauto_js.
Qed.

(* TODO move *)
Lemma of_int_zero_lemma : of_int 0 = JsNumber.zero.
Admitted.

Lemma red_expr_call_number_ok : forall k, ih_call k -> th_call_prealloc k J.prealloc_number.
Proof.
    introv IHc Hcinv Hinv Hvrel Halo Hcrel Hvrels Hlred.
    inverts Hcrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_empty_lemma; try eassumption.
    destruct_hyp Hx.
    cases_isTrue as Heq. {
        subst_hyp Heq.
        inverts Hvrels.
        repeat ljs_autoforward.
        rewrite of_int_zero_lemma.
        jauto_js.
    }
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js.
Qed.

Lemma red_expr_call_boolean_ok : forall k, th_call_prealloc k J.prealloc_bool.
Proof.
    introv Hcinv Hinv Hvrel Halo Hcrel Hvrels Hlred.
    inverts Hcrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_boolean_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js.
Qed.
