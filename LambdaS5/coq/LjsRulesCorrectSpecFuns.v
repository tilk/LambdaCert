Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
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

(** ** Lemmas about operators *)

(* TODO *)

(** ** Lemmas about the environment *)

(* TODO *)

(** ** Lemmas about specification functions *)

Lemma make_native_error_lemma : forall BR k jst jc c st st' jv1 jv2 v1 v2 r,
    L.red_exprh k c st 
       (L.expr_app_2 LjsInitEnv.privMakeNativeError [v1; v2]) 
       (L.out_ter st' r) ->
    state_invariant BR jst jc c st ->
    (v2 = L.value_undefined \/ exists s, v2 = L.value_string s) ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_build_error jv1 jv2) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hinv Hv Hvrel1 Hvrel2. 
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    repeat ljs_autoforward.
    inverts Hvrel2.
    jauto_js 12.
    (* has message *)
    inv_ljs;
    binds_inv. (* TODO *) simpls. false. rewrite binds_empty_eq in H8. eauto.
    repeat ljs_autoforward.
    inv_ljs; binds_inv. 
    repeat ljs_autoforward.
    rew_bag_simpl. 
    simpls.
    binds_inv.
    inverts Hvrel2.
    unfold_concl. do 3 eexists. splits. 
    jauto_js 15.
    jauto_js.
    eapply state_invariant_next_fresh_commute_object_preserved.
    rew_bag_simpl.
    eapply state_invariant_new_object_preserved.
    eauto_js. eauto_js.
    eauto_js 15.
    eauto_js 7.
    jauto_js 8.
    simpls. false. prove_bag 7.
Qed.

Lemma priv_js_error_lemma : forall k c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privJSError [v]) (L.out_ter st' r) ->
    exists obj,
    r = L.res_value (L.value_object (fresh st)) /\
    st' = st \(fresh st := obj) /\
    js_exn_object obj v.
Proof.
    introv Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma native_error_lemma : forall BR k jst jc c st st' jne ptr v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privNativeError [L.value_object ptr; v]) 
        (L.out_ter st' r) ->
    state_invariant BR jst jc c st ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) -> (* TODO error messages in jscert *)
    fact_js_obj (J.object_loc_prealloc (J.prealloc_native_error_proto jne)) ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error jne) (fun _ => False).
Proof.
    introv Hlred Hinv Hv Hbr.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_state_invariant_after_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    forwards Hx : make_native_error_lemma H0; (destr_concl || jauto_js). (* TODO *)
    res_related_invert.
    repeat inv_fwd_ljs.
    forwards Hy : priv_js_error_lemma. eassumption. destruct_hyp Hy.
    repeat inv_fwd_ljs.
    resvalue_related_invert.
    (* debug *) unfold_concl. jauto_set. eauto_js. eauto_js. 
        debug eauto 8 with js_ljs bag typeclass_instances nocore xcore.
    jauto_js 8. 
    ljs_handle_abort.
    skip. (* TODO overspecification in jscert - https://github.com/resource-reasoning/jscert_dev/issues/14 *)
    skip.
Qed.

Lemma type_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privTypeError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    state_invariant BR jst jc c st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_type) (fun _ => False).
Proof.
    introv Hlred Hv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_state_invariant_after_apply.
    repeat ljs_autoforward.
    forwards Hx : native_error_lemma; try eassumption.
    eapply state_invariant_prealloc_in_ctx_lemma. eassumption. eassumption. 
        repeat (eapply Mem_here || eapply Mem_next). (* TODO *)
    destr_concl; tryfalse.
    ljs_handle_abort.
Qed.

(** *** spec_expr_get_value_conv spec_to_boolean 
    It corresponds to [to_bool] in the desugaring. *)

Lemma red_spec_to_boolean_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToBoolean J.spec_to_boolean 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.

    ljs_apply.

    repeat ljs_autoforward. 

    inverts Hvrel; try injects; jauto_js.
Qed.

Lemma red_spec_to_number_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToNumber J.spec_to_number
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_state_invariant_after_apply.
(* TODO *)
Admitted.

(* TODO move *)
Ltac decide_stx_eq := 
    match goal with
    | H : context[decide (L.stx_eq ?v1 ?v2)] |- _ => 
        let EQ := fresh "EQ" in
        case_if_on (decide (L.stx_eq v1 v2)) as EQ;
        [applys_to EQ eq_true_r; rew_refl in EQ; try solve [inverts EQ]
        |applys_to EQ eq_false_r; rew_refl in EQ; try solve [false; apply EQ; jauto_js]]
    end.

Ltac invert_stx_eq :=
    match goal with
    | H : L.stx_eq _ _  |- _ => inverts H
    end. 

Lemma red_spec_to_object_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToObject J.spec_to_object
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_state_invariant_after_apply.
    repeat (ljs_autoforward || decide_stx_eq).
    (* null *)
    destruct Hvrel; invert_stx_eq.
    forwards Hx : type_error_lemma. eassumption. iauto. eauto_js.
    destr_concl; tryfalse.
    jauto_js.
    (* undefined *)
    destruct Hvrel; invert_stx_eq.
    forwards Hx : type_error_lemma. eassumption. iauto. eauto_js.
    destr_concl; tryfalse.
    jauto_js.
    (* object *)
    destruct Hvrel; invert_stx_eq.
    jauto_js.
    (* string *)
    destruct Hvrel; invert_stx_eq.
    skip. (* TODO *)
    (* number *)
    destruct Hvrel; invert_stx_eq.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js 8.
    (* boolean *)
    destruct Hvrel; invert_stx_eq.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js 8.
    (* impossible *)
    destruct Hvrel; false; eauto_js.
Qed.

Lemma red_spec_to_boolean_ok : forall k je, 
    ih_expr k ->
    th_spec k (E.to_bool (js_expr_to_ljs je))
              (J.spec_expr_get_value_conv J.spec_to_boolean je) 
              (fun _ _ _ _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
                  r = L.res_value (L.value_bool b)).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.

    destr_concl; try ljs_handle_abort.

    repeat inv_internal_fwd_ljs.
    forwards_th red_spec_to_boolean_unary_ok.

    destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js.
    jauto_js. right. jauto_js.
Qed.

Lemma new_env_record_object_lemma : forall BR k c st jlenv v jptr ptr b st' r,
    lexical_env_related BR jlenv v ->
    value_related BR (J.value_object jptr) (L.value_object ptr) ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewObjEnvRec 
        [v; L.value_object ptr; L.value_bool b]) (L.out_ter st' r) ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    binds (L.object_internal obj) "parent" v /\
    env_record_related BR (J.env_record_object jptr b) obj.
Proof.
    introv Hlrel Hvrel Hlred.
    inverts Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    reflexivity.
    reflexivity.
    prove_bag.
    econstructor;
    prove_bag 8.
Qed.

Lemma state_invariant_new_env_record_object_lemma : forall BR k jst jc c st v jptr ptr b st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewObjEnvRec 
        [v; L.value_object ptr; L.value_bool b]) (L.out_ter st' r) ->
    binds c "$context" v ->
    value_related BR (J.value_object jptr) (L.value_object ptr) ->
    state_invariant BR jst jc c st ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    state_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR) 
        (J.state_next_fresh (jst \(fresh jst := J.env_record_object jptr b))) 
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hbinds Hvrel Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). 
        prove_bag 10.
    asserts Hlerel : (lexical_env_related BR (J.execution_ctx_lexical_env jc) v).
    solve [eauto using state_invariant_lexical_env_related].
    forwards Hx : new_env_record_object_lemma; try eauto.
    destruct_hyp Hx.
    eexists. splits; try reflexivity.
    eapply state_invariant_push_context_lemma.
    eapply lexical_env_related_cons; eauto_js 10. 
    eauto_js 10. eauto_js 10.
Qed. 

Lemma decl_env_record_related_empty : forall BR,
    decl_env_record_related BR \{} \{}.
Proof.
    introv. unfolds.
    intro s.
    left. splits; prove_bag.
Qed.

Hint Resolve decl_env_record_related_empty : js_ljs.

(* TODO move *)
Lemma new_env_record_decl_lemma : forall BR k c st jlenv v st' r,
    lexical_env_related BR jlenv v ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    binds (L.object_internal obj) "parent" v /\
    env_record_related BR (J.env_record_decl J.decl_env_record_empty) obj.
Proof.
    introv Hlrel Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    reflexivity.
    reflexivity.
    prove_bag.
    econstructor; jauto_js.
Qed.

Lemma state_invariant_new_env_record_decl_lemma : forall BR k jst jc c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    binds c "$context" v ->
    state_invariant BR jst jc c st ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    state_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR) 
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hbinds Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). jauto_js.
    asserts Hlerel : (lexical_env_related BR (J.execution_ctx_lexical_env jc) v).
    solve [eauto using state_invariant_lexical_env_related].
    forwards Hx : new_env_record_decl_lemma; try eauto.
    destruct_hyp Hx.
    eexists. splits; try reflexivity.
    eapply state_invariant_push_context_lemma.
    eapply lexical_env_related_cons; eauto_js 15.
    eauto_js 10. eauto_js 10.
Qed.

(* TODO 
Lemma decl_env_add_mutable_binding_lemma : forall BR k jst jc c st st' r jeptr ptr obj b jv v s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddMutableBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool b]) (L.out_ter st' r) -> 
    binds st ptr obj ->
    state_invariant BR jst jc c st ->
    value_related BR jv v ->
    (inr jeptr, ptr) \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of 
        (L.attributes_data_intro v true false b))) /\
    r = L.res_value L.value_undefined /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool b) jv) jc c st'.
Proof.
(*
    introv Hlred Hbinds Hinv.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide.
    repeat ljs_autoforward.
    solve [inv_ljs].
*)
(*
    repeat ljs_autoforward.
    inv_ljs.
    binds_determine. 
    false. prove_bag.
    repeat ljs_autoforward. 
    inv_ljs. 
    repeat ljs_autoforward.
    inv_ljs. 
    repeat ljs_autoforward.
    simpls.

    binds_inv. false. prove_bag 8.
*)
Admitted. (* TODO *)
*)