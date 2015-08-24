Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Import LjsRulesCorrectStatements.
Require Import LjsRulesCorrectExpressions.
Require Import LjsRulesCorrectCallPrealloc.
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
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.

Lemma main_lemma : forall k, 
    (forall jt, th_stat k jt) /\ (forall je, th_expr k je) /\ (forall jpre, th_call_prealloc k jpre).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    asserts IHt : (ih_stat k). unfolds. introv Hle. specializes IH Hle. jauto.
    asserts IHe : (ih_expr k). unfolds. introv Hle. specializes IH Hle. jauto.
    asserts IHp : (ih_call_prealloc k). unfolds. introv Hle. specializes IH Hle. jauto.
    clear IH.
    splits.
    {
    (* STATEMENTS *)
    destruct 0.
    (* stat_expr *)
    applys red_stat_expr_ok; eassumption.
    (* stat_label *)
    applys red_stat_label_ok; eassumption.
    (* stat_block *)
    applys red_stat_block_ok; eassumption.
    (* stat_var_decl *)
    applys red_stat_var_decl_ok; eassumption.
    (* stat_if *)
    applys red_stat_if_ok; eassumption.
    (* stat_do_while *)
    skip.
    (* stat_while *)
    applys red_stat_while_ok; eassumption.
    (* stat_with *)
    applys red_stat_with_ok; eassumption.
    (* stat_throw *)
    applys red_stat_throw_ok; eassumption.
    (* stat_return *)
    applys red_stat_return_ok; eassumption.
    (* stat_break *)
    applys red_stat_break_ok.
    (* stat_continue *)
    applys red_stat_continue_ok.
    (* stat_try *)
    skip.
    (* stat_for *)
    skip.
    (* stat_for_var *)
    skip.
    (* stat_for_in *)
    skip.
    (* stat_for_in_var *)
    skip.
    (* stat_debugger *)
    applys red_stat_debugger_ok.
    (* stat_switch *)
    applys red_stat_switch_ok; eassumption.
    } {
    (* EXPRESSIONS *)
    destruct 0.
    (* expr_this *)
    eapply red_expr_this_ok.
    (* expr_identifier *)
    eapply red_expr_identifier_ok. 
    (* expr_literal *)
    eapply red_expr_literal_ok.
    (* expr_object *)
    skip.
    (* expr_array *)
    skip.
    (* expr_function *)
    skip.
    (* expr_access *)
    skip.
    (* expr_member *)
    skip.
    (* expr_new *)
    applys red_expr_new_ok; eassumption.
    (* expr_call *)
    skip.
    (* expr_unary_op *)
    applys red_expr_unary_op_ok; eassumption.
    (* expr_binary_op *)
    applys red_expr_binary_op_ok; eassumption.
    (* expr_conditional *)
    applys red_expr_conditional_ok; eassumption.
    (* expr_assign *)
    skip.
    } {
    (* BUILT-IN FUNCTIONS *)
    destruct 0.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    }
Qed.

Require JsInit. (* TODO to J namespace *)

Lemma execution_ctx_related_set_prog_strictness_lemma : forall BR b c,
    execution_ctx_related BR (J.execution_ctx_initial b) c ->
    execution_ctx_related BR (J.execution_ctx_initial b) (c\("$strict" := L.value_bool b)).
Proof.
    introv Hrel.
    destruct Hrel.
    constructor; introv Hbinds; rew_binds_eq in Hbinds; destruct_hyp Hbinds; tryfalse; eauto.
Qed.

Lemma context_invariant_set_prog_strictness_lemma : forall BR b c,
    context_invariant BR (J.execution_ctx_initial b) c ->
    context_invariant BR (J.execution_ctx_initial b) (c\("$strict" := L.value_bool b)).
Proof.
    introv Hcinv.
    destruct Hcinv.
    apply execution_ctx_related_set_prog_strictness_lemma in context_invariant_execution_ctx_related.
    constructor; eauto_js 2.
Qed.

Hint Resolve context_invariant_set_prog_strictness_lemma : js_ljs.
Opaque E.init_bindings_prog.

Lemma javascript_correct_lemma : forall BR k c st st' r jp jp',
    jp' = JsSyntaxInfos.add_infos_prog false jp ->
    L.red_exprh k c st (L.expr_basic (E.ejs_prog_to_ljs (E.js_prog_to_ejs jp')))
        (L.out_ter st' r) -> (* TODO factorize in EjsFromJs *)
    context_invariant BR (J.execution_ctx_initial (J.prog_intro_strictness jp')) c ->
    state_invariant BR JsInit.state_initial st ->
    concl_javascript initBR st' r jp.
Proof.
    introv EQjp' Hlred Hcinv Hinv.
    destruct jp' as (b&jels).
    simpls.
    repeat ljs_autoforward.
Admitted. (* TODO *)

Lemma javascript_correct : forall st' jp jp' k r,
    jp' = JsSyntaxInfos.add_infos_prog false jp ->
    L.red_exprh k LjsInitEnv.init_ctx LjsInitEnv.init_store (L.expr_basic (E.ejs_prog_to_ljs (E.js_prog_to_ejs jp')))
        (L.out_ter st' r) -> (* TODO factorize in EjsFromJs *)
    concl_javascript initBR st' r jp.
Proof.
    introv EQjp' Hlred.
    forwards Hx : javascript_correct_lemma EQjp' Hlred.
    eapply init_context_invariant_ok.
    eapply init_state_invariant_ok.
    apply Hx.
Qed.
