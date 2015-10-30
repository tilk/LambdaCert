Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Import LjsRulesCorrectDescriptors.
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

Lemma red_spec_construct_prealloc_bool_ok : forall k, ih_call k -> th_construct_prealloc k J.prealloc_bool.
Proof.
    introv IHc Hcinv Hinv Hvrels Halo Hcpre Hlred.
    inverts Hcpre.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_boolean_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert. 
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : make_boolean_lemma. destruct_hyp Hx.
    jauto_js 15.
Qed.

Lemma red_spec_construct_prealloc_number_ok : forall k, ih_call k -> th_construct_prealloc k J.prealloc_number.
Proof.
    introv IHc Hcinv Hinv Halo Hvrels Hcpre Hlred.
    inverts Hcpre.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_empty_lemma; try eassumption.
    destruct_hyp Hx.
    cases_isTrue as Heq. {
        subst_hyp Heq.
        inverts Hvrels.
        repeat ljs_autoforward.
        rewrite of_int_zero_lemma in *.
        forwards_th Hx : make_number_lemma. destruct_hyp Hx.
        jauto_js 15.
    }
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert. 
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : make_number_lemma. destruct_hyp Hx.
    jauto_js 15.
Qed.

Lemma red_spec_construct_error_ok : forall k, ih_call k -> th_construct_prealloc k J.prealloc_error.
Proof.
    introv IHc Hcinv Hinv Halo Hvrels Hcpre Hlred.
    inverts Hcpre.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : make_native_error_msg_lemma. eauto_js.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 8.
Qed.

Require Import LjsRulesCorrectInit. (* TODO move native_error_proto_val somewhere else *)

Lemma construct_prealloc_native_error_lemma : forall jne v,
    construct_prealloc_related (J.prealloc_native_error jne) v -> 
    v = L.value_closure (LjsSyntax.closure_intro
                  [("%ArrayIdx", LjsInitEnv.privArrayIdx);
                   ("%MakeNativeErrorMsg", LjsInitEnv.privMakeNativeErrorMsg);
                   ("proto", native_error_proto_val jne)] None
                   ["this"; "args"] LjsInitEnv.ex_privEvalErrorConstructor).
Proof.
    introv Hcpre. inverts Hcpre; reflexivity.
Qed.

Lemma red_spec_construct_native_error_ok : forall k jne, ih_call k -> 
    th_construct_prealloc k (J.prealloc_native_error jne).
Proof.
    introv IHc Hcinv Hinv Halo Hvrels Hcpre Hlred.
    lets Hcpre' : construct_prealloc_native_error_lemma Hcpre. subst_hyp Hcpre'.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : array_idx_eq_lemma; try eassumption. { rewrite <- string_of_nat_0_lemma. reflexivity. }
    destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th : make_native_error_msg_lemma. { eauto_js. } { constructor. destruct jne; eauto_js. }
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 8.
Qed.

Lemma red_spec_construct_prealloc_ok : forall k jpre, ih_call k -> th_construct_prealloc k jpre.
Proof.
    introv IHc Hcinv Hinv Halo Hvrels Hcpre Hlred.
    inverts keep Hcpre;
    generalize Hcinv Hinv Halo Hvrels Hcpre Hlred;
    clear Hcinv Hinv Halo Hvrels Hcpre Hlred.
    skip. (* object *)
    skip. (* function *)
    applys~ red_spec_construct_prealloc_bool_ok.
    applys~ red_spec_construct_prealloc_number_ok.
    skip. (* array *)
    skip. (* string *)
    applys~ red_spec_construct_error_ok.
    applys~ red_spec_construct_native_error_ok.
    applys~ red_spec_construct_native_error_ok.
    applys~ red_spec_construct_native_error_ok.
    applys~ red_spec_construct_native_error_ok.
    applys~ red_spec_construct_native_error_ok.
Qed.

Definition if_object_else v1 v2 := If L.is_object v1 then v1 else v2.

Lemma if_object_else_lemma : forall k c st st' r v1 v2,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privIfObjectElse [v1; v2]) (L.out_ter st' r) ->
    st' = st /\ r = L.res_value (if_object_else v1 v2).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    unfolds if_object_else.
    cases_decide as Hobj; repeat ljs_autoforward; eauto.
Qed.

Lemma value_related_if_object_else_lemma : forall BR jv1 jv2 v1 v2,
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    value_related BR (If (J.type_of jv1 = J.type_object) then jv1 else jv2) (if_object_else v1 v2).
Proof.
    introv Hvrel1 Hvrel2.
    unfolds if_object_else. 
    inverts Hvrel1; 
    cases_if as Hc1; simpl in Hc1; tryfalse;
    cases_if as Hc2; try inverts Hc2; try eauto_js.
    false. apply Hc2. constructor.
Qed.

Hint Resolve value_related_if_object_else_lemma : js_ljs.

Lemma object_or_null_if_object_lemma : forall v1 v2,
    object_or_null v2 ->
    object_or_null (if_object_else v1 v2).
Proof.
    introv Hnull.
    unfolds if_object_else.
    cases_if as Hio.
    + inverts Hio. constructor.
    + assumption.
Qed.

Hint Resolve object_or_null_if_object_lemma : js_ljs.

Lemma make_object_lemma : forall BR jst jv k c st st' r v,
    state_invariant BR jst st ->
    value_related BR jv v ->
    object_or_null v ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeObject [v]) (L.out_ter st' r) ->
    exists jst' BR',
    jst' = J.state_next_fresh (jst \(fresh jst := J.object_new jv "Object")) /\
    st' = st \(fresh st := object_new v "Object") /\
    BR' = \{fact_js_obj (fresh jst) (fresh st)} \u BR /\
    state_invariant BR' jst' st' /\
    r = L.res_value (L.value_object (fresh st)).
Proof.
    introv Hinv Hvrel Hnull Hlred.
    forwards_th Hx : ljs_make_object_lemma. destruct_hyp Hx.
    jauto_js 10.
Qed.

Lemma red_spec_default_construct_ok : forall BR k jst jc c st st' ptr ptr1 vs r jptr jvs,
    ih_call k ->
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privDefaultConstruct [L.value_object ptr; L.value_object ptr1]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_construct_default jptr jvs) (fun jv => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrels Halo Hbs.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : get_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    forwards_th Hx : if_object_else_lemma. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : make_object_lemma. eauto_js. destruct_hyp Hx.
    repeat ljs_autoforward.
    apply_ih_call.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    forwards_th Hx : if_object_else_lemma. destruct_hyp Hx.
    jauto_js 10.
Qed.

Lemma red_spec_construct_ok : forall BR k jst jc c st st' ptr ptr1 vs r jptr jvs,
    ih_call k ->
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privrunConstruct [L.value_object ptr; L.value_object ptr1]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_construct jptr jvs) (fun jv => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrels Halo Hbs.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards Hx : construct_related_lemma Hinv Hbs; try eassumption. 
    destruct Hx as (jcon&Hcrel).
    forwards Hmeth : object_method_construct_lemma; try eassumption. eauto_js 7.
    inverts Hcrel. { (* prealloc *)
        forwards_th Hx : red_spec_construct_prealloc_ok; try eassumption.
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* default *)
        forwards_th : red_spec_default_construct_ok; try eassumption.
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.
