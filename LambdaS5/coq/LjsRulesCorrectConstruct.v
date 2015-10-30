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
        lets Hx : red_spec_construct_prealloc_ok ___.
        specializes_th Hx; try eassumption.
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* default *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : get_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        skip. (* TODO *)
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.
