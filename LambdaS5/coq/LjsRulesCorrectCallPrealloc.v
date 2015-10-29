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

(* TODO move *)
Ltac value_related_invert :=
    match goal with
    | H : value_related _ _ _ |- _ => inverts H
    end.

Require Import LjsRulesCorrectDescriptors. (* TODO move heaps_bisim_bijective and stuff *)

Lemma heaps_bisim_bijective_from_state_invariant : forall BR jst st,
    state_invariant BR jst st ->
    heaps_bisim_bijective BR.
Proof.
    introv Hinv. destruct (state_invariant_heaps_bisim_consistent Hinv). constructor; eauto.
Qed.

Hint Resolve heaps_bisim_bijective_from_state_invariant : js_ljs.

(* TODO move *)
Lemma value_related_not_eq_lemma : forall BR jv jv' v v',
    heaps_bisim_bijective BR ->
    value_related BR jv' v' ->
    value_related BR jv v ->
    v <> v' -> jv <> jv'.
Proof.
    introv Hbij Hvrel1 Hvrel2 Hdiff Heq. subst.
    inverts Hvrel1 as Hf1; inverts Hvrel2 as Hf2; tryfalse.
    lets Heq : heaps_bisim_bijective_lfun_obj Hbij Hf1 Hf2.
    subst. tryfalse.
Qed.

Local Opaque nth_def.

Definition object_new proto class := {|
    L.object_attrs := {| 
        L.oattrs_proto := proto;
        L.oattrs_class := class;
        L.oattrs_extensible := true;
        L.oattrs_code := L.value_undefined
    |};
    L.object_properties := \{};
    L.object_internal := \{}
|}.

Lemma ljs_make_object_lemma : forall k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeObject []) (L.out_ter st' r) ->
    st' = st \(fresh st := object_new LjsInitEnv.privObjectProto "Object") /\
    r = L.res_value (L.value_object (fresh st)).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    eauto_js.
Qed.

Lemma object_related_new_lemma : forall BR jv v s,
    value_related BR jv v ->
    object_or_null v ->
    object_related BR (J.object_new jv s) (object_new v s).
Proof.
    introv Hvrel Hnull. unfolds object_new.
    constructor.
    constructor; eauto_js.
    eauto_js.
Qed.

Hint Resolve object_related_new_lemma : js_ljs.

Lemma red_expr_call_object_ok : forall k, th_call_prealloc k J.prealloc_object.
Proof.
    introv Hcinv Hinv Hvrel Halo Hcrel Hvrels Hlred.
    inverts Hcrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite stx_eq_null_eq_lemma in Heq. {
        rewrite Heq in *. value_related_invert.
        repeat ljs_autoforward.
        forwards_th Hx : ljs_make_object_lemma. destruct_hyp Hx.
        jauto_js 8.
    }
    lets Hjneq1 : value_related_not_eq_lemma Heq; eauto_js.
    repeat ljs_autoforward.
    cases_decide as Heq2; rewrite stx_eq_undefined_eq_lemma in Heq2. {
        rewrite Heq2 in *. value_related_invert.
        repeat ljs_autoforward.
        forwards_th Hx : ljs_make_object_lemma. destruct_hyp Hx.
        jauto_js 8.
    }
    lets Hjneq2 : value_related_not_eq_lemma Heq2; eauto_js.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_object_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js.
Qed.
