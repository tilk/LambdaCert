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

Lemma option_usercode_related_none_lemma : forall BR (m : finmap _ _) s,
     ~index m s ->
     option_usercode_related BR None None None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option_usercode_related_some_lemma : forall BR (m : finmap _ _) s jfb is jle v,
     binds m s v ->
     usercode_related BR jfb is jle v ->
     option_usercode_related BR (Some jfb) (Some is) (Some jle) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Resolve option_usercode_related_none_lemma option_usercode_related_some_lemma : js_ljs.

Lemma option2_none_lemma : forall T1 T2 (P : T1 -> T2 -> Prop) (m : finmap _ _) s,
     ~index m s ->
     Option2 P None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option2_some_lemma : forall T1 T2 (P : T1 -> T2 -> Prop) (m : finmap string T2) s x1 x2,
     binds m s x2 ->
     P x1 x2 ->
     Option2 P (Some x1) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Extern 2 (option_construct_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_construct_related _ _) => eapply option2_some_lemma : js_ljs.
Hint Extern 2 (option_codetxt_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_codetxt_related _ _) => eapply option2_some_lemma : js_ljs.
Hint Extern 2 (option_func_strict_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_func_strict_related _ _) => eapply option2_some_lemma : js_ljs.

Lemma nindex_update_diff : forall `{Index_update_diff_eq} M k k' x', 
    k <> k' -> ~index M k -> ~index (M \(k' := x')) k.
Proof.
    intros. rewrite index_update_diff_eq; eauto.
Qed.

Hint Resolve @nindex_update_diff : bag.

(* TODO move *)
Lemma state_invariant_bisim_obj_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    exists jobj,
    binds jst jptr jobj /\
    object_related BR jobj obj.
Proof.
    introv Hinv Hbs Hbinds.
    lets Hjbinds : heaps_bisim_consistent_lnoghost_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs.
    rewrite index_binds_eq in Hjbinds.
    destruct Hjbinds as (jobj&Hjbinds).
    lets Hrel : heaps_bisim_consistent_bisim_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs Hjbinds Hbinds.
    jauto.
Qed.

Lemma make_native_error_lemma : forall BR k jst jc c st st' jv1 jv2 v1 v2 r,
    L.red_exprh k c st 
       (L.expr_app_2 LjsInitEnv.privMakeNativeError [v1; v2]) 
       (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    object_or_null v1 ->
    (v2 = L.value_undefined \/ exists s, v2 = L.value_string s) ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_build_error jv1 jv2) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hcinv Hinv Hon Hv Hvrel1 Hvrel2. 
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    repeat ljs_autoforward. {
        inverts Hvrel2.
        jauto_js 25.
    }
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
    unfold_concl. jauto_set_slim. (* TODO automation? *)
    + eauto_js 15.
    + eauto_js.
    + eapply state_invariant_next_fresh_commute_object_preserved. rew_bag_simpl.
      eapply state_invariant_new_object_preserved; eauto_js 17.
    + eauto_js 7.
    + eauto_js 8.
    + simpls. false. prove_bag 8.
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
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) -> (* TODO error messages in jscert *)
    fact_js_obj (J.object_loc_prealloc (J.prealloc_native_error_proto jne)) ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error jne) (fun _ => False).
Proof.
    introv Hlred Hcinv Hinv Hv Hbr.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    (forwards_th : make_native_error_lemma; [eauto_js | eauto | idtac]);
    destr_concl; try ljs_handle_abort. { (* no error message *)
        res_related_invert.
        repeat inv_fwd_ljs.
        forwards_th Hy : priv_js_error_lemma. destruct_hyp Hy.
        repeat inv_fwd_ljs.
        resvalue_related_invert.
        jauto_js 8.
    }
    skip. (* TODO overspecification in jscert - https://github.com/resource-reasoning/jscert_dev/issues/14 *)
    skip.
Qed.

Lemma type_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privTypeError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_type) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma reference_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privReferenceError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_ref) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma syntax_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privSyntaxError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_syntax) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma unbound_id_lemma : forall BR k jst jc c st st' s r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privUnboundId [L.value_string s]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_ref) (fun _ => False).
Proof.
    introv Hlred Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : reference_error_lemma; try eassumption.
    jauto_js.
Qed.

Ltac invert_stx_eq :=
    match goal with
    | H : L.stx_eq _ _  |- _ => inverts H
    end. 

(* TODO move *)
Ltac decide_stx_eq := 
    match goal with
    | H : context[decide (L.stx_eq ?v1 ?v2)] |- _ => 
        let EQ := fresh "EQ" in
        case_if_on (decide (L.stx_eq v1 v2)) as EQ;
        [applys_to EQ eq_true_r; rew_refl in EQ; try solve [inverts EQ]
        |applys_to EQ eq_false_r; rew_refl in EQ; try solve [false; apply EQ; jauto_js]]
    end.

(* TODO move *)
Hint Extern 3 (object_or_null _) => eapply object_or_null_object : js_ljs.

Lemma red_spec_to_object_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToObject J.spec_to_object
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat (ljs_autoforward || decide_stx_eq). { (* null *)
        destruct Hvrel; invert_stx_eq.
        forwards_th Hx : type_error_lemma. iauto. 
        destr_concl; tryfalse.
        jauto_js.
    } { (* undefined *)
        destruct Hvrel; invert_stx_eq.
        forwards_th Hx : type_error_lemma. iauto. 
        destr_concl; tryfalse.
        jauto_js.
    } { (* object *)
        destruct Hvrel; invert_stx_eq.
        jauto_js.
    } { (* string *)
        destruct Hvrel; invert_stx_eq.
        skip. (* TODO *)
    } { (* number *)
        destruct Hvrel; invert_stx_eq.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply. 
        repeat ljs_autoforward.
        jauto_js 28.
    } { (* boolean *)
        destruct Hvrel; invert_stx_eq.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply. 
        repeat ljs_autoforward.
        jauto_js 28.
    } { (* impossible *)
        destruct Hvrel; false; eauto_js.
    }
Qed.

(* ** Handling contexts *)

(* TODO move *)
Lemma decl_env_record_related_empty : forall BR,
    decl_env_record_vars_related BR \{} \{}.
Proof.
    introv. unfolds.
    intro s.
    left. splits; prove_bag.
Qed.

Hint Resolve decl_env_record_related_empty : js_ljs.

(* *** Creating new environment records *)

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
    prove_bag 10.
    econstructor.
    econstructor;
    prove_bag 10.
Qed.

(* *** State invariant for new environment records *)

Lemma only_state_invariant_new_env_record_decl_lemma : forall BR k jst jlenv c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    lexical_env_related BR jlenv v ->
    state_invariant BR jst st ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hlerel Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). { jauto_js. }
    forwards_th Hx : new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists. splits; try reflexivity.
    + eauto_js.
    + eauto_js 8.
Qed.

Lemma state_invariant_new_env_record_decl_lemma : forall BR k jst jc c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    binds c "$context" v ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)) /\
    context_invariant BR'
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))).
Proof.
    introv Hlred Hbinds Hcinv Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). jauto_js.
    lets Hlerel : context_invariant_lexical_env_related Hcinv Hbinds.
    forwards_th Hx : only_state_invariant_new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists. splits; try reflexivity; try assumption.
    eapply context_invariant_push_context_lemma.
    + eapply lexical_env_related_cons; eauto_js 15.
    + eauto_js 10.
    + eauto_js 10.
Qed.

Lemma state_invariant_new_env_record_object_lemma : forall BR k jst jc c st v jptr ptr b st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewObjEnvRec 
        [v; L.value_object ptr; L.value_bool b]) (L.out_ter st' r) ->
    binds c "$context" v ->
    value_related BR (J.value_object jptr) (L.value_object ptr) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    state_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR) 
        (J.state_next_fresh (jst \(fresh jst := J.env_record_object jptr b))) 
        (st \(fresh st := obj)) /\
    context_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR)
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))).
Proof.
    introv Hlred Hbinds Hvrel Hcinv Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). 
        prove_bag 10.
    asserts Hlerel : (lexical_env_related BR (J.execution_ctx_lexical_env jc) v).
    solve [eauto using context_invariant_lexical_env_related].
    forwards_th Hx : new_env_record_object_lemma. eauto_js.
    destruct_hyp Hx.
    eexists. splits; try reflexivity. (* TODO *)
    jauto_js 7. 
    eapply context_invariant_push_context_lemma.
    eapply lexical_env_related_cons; eauto_js 10. eauto_js 10.
    eauto_js.
Qed. 

(* ** More environment record manipulations TODO doc *)

(* TODO move *)
Lemma env_record_related_lookup_lemma : forall BR jeptr ptr jst st obj,
     state_invariant BR jst st ->
     fact_js_env jeptr ptr \in BR ->
     binds st ptr obj ->
     exists jer,
     binds jst jeptr jer /\
     env_record_related BR jer obj.
Proof.
    introv Hinv Hbs Hbinds.
    lets Hjindex : heaps_bisim_consistent_lnoghost_env (state_invariant_heaps_bisim_consistent Hinv) Hbs.
    lets (jer&Hjbinds) : index_binds Hjindex.
    lets Herel : heaps_bisim_consistent_bisim_env (state_invariant_heaps_bisim_consistent Hinv) Hbs Hbinds.
        eassumption.
    jauto.
Qed.

(* TODO move *)
Lemma stx_eq_string_eq_lemma : forall s1 s2,
    L.stx_eq (L.value_string s1) (L.value_string s2) = (s1 = s2).
Proof.
    introv. rew_logic. splits; introv Hx. {
       inverts Hx. reflexivity.
    } {
       substs. eauto_js.
    }
Qed.

(* TODO move *)
Lemma stx_eq_object_eq_lemma : forall ptr1 ptr2,
    L.stx_eq (L.value_object ptr1) (L.value_object ptr2) = (ptr1 = ptr2).
Proof.
    introv. rew_logic. splits; introv Hx. {
       inverts Hx. reflexivity.
    } {
       substs. eauto_js.
    }
Qed.

(* TODO move *)
Lemma stx_eq_empty_eq_lemma : forall v, L.stx_eq v L.value_empty = (v = L.value_empty).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* TODO move *)
Lemma stx_eq_null_eq_lemma : forall v, L.stx_eq v L.value_null = (v = L.value_null).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* TODO move *)
Lemma stx_eq_undefined_eq_lemma : forall v, L.stx_eq v L.value_undefined = (v = L.value_undefined).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* ** Accessing properties *)

Lemma object_method_has_property_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_has_prop_ jst jptr J.builtin_has_prop_default.
Proof.
Admitted. (* TODO: ignoring exotic objects for now *)

Lemma object_method_get_property_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_get_prop_ jst jptr J.builtin_get_prop_default.
Proof.
Admitted. (* TODO: ignoring exotic objects for now *)

Lemma object_method_get_own_property_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default.
Proof.
Admitted. (* TODO: ignoring exotic objects for now *)

(* TODO move *)
Lemma object_property_not_index_lemma : forall BR jst st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_properties obj) s ->
    J.object_property jst jptr s None.
Proof.
    introv Hinv Hf Hbinds Hnindex.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hoprel : object_related_properties Horel s.
    destruct_hyp Hoprel; [idtac|false; prove_bag].
    exists (J.object_properties_ jobj). split. 
    + unfolds. jauto_js.
    + rew_heap_to_libbag. erewrite read_option_not_index_inv by eassumption. reflexivity.
Qed.

(* TODO move *)
Lemma object_property_index_lemma : forall BR jst st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    index (L.object_properties obj) s ->
    exists attrs jattrs,
    J.object_property jst jptr s (Some jattrs) /\
    binds (L.object_properties obj) s attrs /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hindex.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hoprel : object_related_properties Horel s.
    destruct_hyp Hoprel; [false; prove_bag|idtac].
    exists attrs jattrs.
    splits.
    + exists (J.object_properties_ jobj). split.
      - unfolds. jauto_js.
      - rew_heap_to_libbag. erewrite read_option_binds_inv by eassumption. reflexivity.
    + assumption.
    + assumption.
Qed.

(* TODO move *)
Lemma object_property_binds_lemma : forall BR jst st jptr ptr obj s attrs,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_properties obj) s attrs ->
    exists jattrs,
    J.object_property jst jptr s (Some jattrs) /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hbindsa.
    asserts Hindex : (index (L.object_properties obj) s). prove_bag.
    lets Hx : object_property_index_lemma Hinv Hf Hbinds Hindex.
    destruct_hyp Hx.
    binds_determine.
    jauto.
Qed.

Lemma object_method_get_own_property_default_not_index_lemma : forall BR jst jc st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_properties obj) s ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default ->
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) (J.ret jst J.full_descriptor_undef).
Proof.
    introv Hinv Hf Hbinds Hnindex Hmeth.
    lets Hx : object_property_not_index_lemma Hinv Hf Hbinds Hnindex.
    eauto_js.
Qed.

Lemma object_method_get_own_property_default_binds_lemma : forall BR jst jc st jptr ptr obj s attrs,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_properties obj) s attrs ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default ->
    exists jattrs,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) (J.ret jst (J.full_descriptor_some jattrs)) /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hbinds2 Hmeth.
    lets Hx : object_property_binds_lemma Hinv Hf Hbinds Hbinds2.
    destruct_hyp Hx.
    jauto_js.
Qed.

Lemma object_related_proto_null_lemma : forall BR jobj obj,
    object_related BR jobj obj ->
    L.object_proto obj = L.value_null ->
    J.object_proto_ jobj = J.value_prim J.prim_null.
Proof.
    introv Horel Heq.
    lets Hvrel : object_prim_related_prototype (object_related_prim Horel).
    rewrite Heq in Hvrel.
    inverts Hvrel. reflexivity.
Qed.

Lemma object_proto_null_lemma : forall BR jst st ptr obj jptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_proto obj = L.value_null ->
    J.object_proto jst jptr (J.value_prim J.prim_null).
Proof.
    introv Hinv Hf Hbinds Heq.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hjeq : object_related_proto_null_lemma Horel Heq.
    unfolds. jauto.
Qed.

Lemma object_related_proto_not_null_lemma : forall BR jobj obj,
    object_related BR jobj obj ->
    L.object_proto obj <> L.value_null ->
    exists jptr ptr,
    L.object_proto obj = L.value_object ptr /\
    J.object_proto_ jobj = J.value_object jptr /\
    fact_js_obj jptr ptr \in BR.
Proof.
    introv Horel Heq.
    lets Hvrel : object_prim_related_prototype (object_related_prim Horel).
    lets Hobj : object_prim_related_prototype_object_or_null (object_related_prim Horel).
    inverts Hobj as Heq1; tryfalse.
    rewrite <- Heq1 in Hvrel.
    inverts Hvrel. jauto.
Qed.

Lemma object_proto_not_null_lemma : forall BR jst st ptr obj jptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_proto obj <> L.value_null ->
    exists jptr' ptr',
    L.object_proto obj = L.value_object ptr' /\
    J.object_proto jst jptr (J.value_object jptr') /\
    fact_js_obj jptr' ptr' \in BR.
Proof.
    introv Hinv Hf Hbinds Heq.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hjeq : object_related_proto_not_null_lemma Horel Heq.
    destruct_hyp Hjeq.
    unfolds J.object_proto.
    jauto.
Qed.

Lemma get_own_property_lemma : forall BR k jst jc c st st' r jptr ptr s v_d v_a v_u,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetOwnProperty 
        [L.value_object ptr; L.value_string s; v_d; v_a; v_u]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jfd st'' c' k', 
      jsr = J.specret_val jst'' jfd /\
      ((jfd = J.full_descriptor_undef /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_u []) (L.out_ter st' r)) /\
        state_invariant BR' jst'' st'' \/
       (exists jv1 v1 b1 b2 b3, 
        jfd = J.full_descriptor_some (J.attributes_data_of (J.attributes_data_intro jv1 b1 b2 b3)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_d [v1; L.value_bool b1; L.value_bool b2; L.value_bool b3]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1) \/
       (exists v1 jv1 v2 jv2 b1 b2, 
        jfd = J.full_descriptor_some (J.attributes_accessor_of (J.attributes_accessor_intro jv1 jv2 b1 b2)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_a [v1; v2; L.value_bool b1; L.value_bool b2]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1 /\ value_related BR' jv2 v2)) /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k) \/
      exists jr, 
      jsr = @J.specret_out J.full_descriptor (J.out_ter jst'' jr) /\
      J.abort (J.out_ter jst'' jr) /\ J.res_type jr = J.restype_throw /\ 
      state_invariant BR' jst'' st' /\
      res_related BR' jst'' st' jr r /\ BR \c BR').
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    forwards : object_method_get_own_property_lemma; try eassumption.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* found *)
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Hbinds).
        forwards Hgop : object_method_get_own_property_default_binds_lemma; try eassumption.
        destruct_hyp Hgop.
        repeat ljs_autoforward.
        cases_decide as Hacc. { (* is accessor *)
            inverts Hacc.
            inverts Hgop1 as Harel. inverts Harel.
            repeat ljs_autoforward. simpls.
            jauto_js 30.
        } { (* is data *)
            inverts Hgop1 as Harel; try solve [false; apply Hacc; eapply L.is_accessor_accessor]. inverts Harel.
            repeat ljs_autoforward. simpls.
            jauto_js 20.
        }
    } { (* not found *)
        forwards Hgop : object_method_get_own_property_default_not_index_lemma; try eassumption.
        repeat ljs_autoforward.
        jauto_js 20.
    }
Qed.

(* TODO: factorize the theorem statement *)
Lemma get_property_lemma : forall k BR jst jc c st st' r jptr ptr s v_d v_a v_u,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetProperty 
        [L.value_object ptr; L.value_string s; v_d; v_a; v_u]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jfd st'' c' k', 
      jsr = J.specret_val jst'' jfd /\
      ((jfd = J.full_descriptor_undef /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_u []) (L.out_ter st' r)) /\
        state_invariant BR' jst'' st'' \/
       (exists jv1 v1 b1 b2 b3, 
        jfd = J.full_descriptor_some (J.attributes_data_of (J.attributes_data_intro jv1 b1 b2 b3)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_d [v1; L.value_bool b1; L.value_bool b2; L.value_bool b3]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1) \/
       (exists v1 jv1 v2 jv2 b1 b2, 
        jfd = J.full_descriptor_some (J.attributes_accessor_of (J.attributes_accessor_intro jv1 jv2 b1 b2)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_a [v1; v2; L.value_bool b1; L.value_bool b2]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1 /\ value_related BR' jv2 v2)) /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k) \/
      exists jr, 
      jsr = @J.specret_out J.full_descriptor (J.out_ter jst'' jr) /\
      J.abort (J.out_ter jst'' jr) /\ J.res_type jr = J.restype_throw /\ 
      state_invariant BR' jst'' st' /\
      res_related BR' jst'' st' jr r /\ BR \c BR').
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    forwards : object_method_get_property_lemma; try eassumption.
    forwards : object_method_get_own_property_lemma; try eassumption.
    repeat ljs_autoforward.
    forwards_th Hx : get_own_property_lemma. eassumption.
    destruct_hyp Hx; try ljs_handle_abort. { (* own property undefined, recurse *)
        inverts red_exprh Hx6. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        cases_decide as Hprnul; rewrite stx_eq_null_eq_lemma in Hprnul. { (* prototype is null *)
            forwards Hjproto : object_proto_null_lemma; try prove_bag.
            repeat ljs_autoforward.
            jauto_js 30.
        } { (* prototype not null *)
            forwards Hjproto : object_proto_not_null_lemma; try prove_bag.
            destruct Hjproto as (jptr'&ptr'&Heq1&Heq2&Hf').
            repeat ljs_autoforward.
            unfolds L.object_proto. rewrite Heq1 in *.
            forwards_th Hx : IH. math. prove_bag.
            destruct_hyp Hx; try ljs_handle_abort;
            jauto_js 30.
        }
    } { (* found data *)
        jauto_js 30.
    } { (* found accessor *)
        jauto_js 30.
    }
Qed.

Lemma has_property_lemma_lemma : forall k BR jst jc c st st' r jptr ptr s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privHasProperty [L.value_object ptr; L.value_string s]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_spec BR jst jc c st st' r (J.spec_object_get_prop jptr s) 
        (fun _ _ jfd => r = L.res_value (L.value_bool (isTrue (jfd <> J.full_descriptor_undef)))).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    forwards : object_method_get_property_lemma; try eassumption.
    forwards : object_method_get_own_property_lemma; try eassumption.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* found *)
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Hbinds).
        forwards Hgop : object_method_get_own_property_default_binds_lemma; try eassumption.
        destruct_hyp Hgop.
        repeat ljs_autoforward.
        jauto_js.
    } { (* not found *)
        forwards Hgop : object_method_get_own_property_default_not_index_lemma; try eassumption.
        repeat ljs_autoforward.
        cases_decide as Hprnul; rewrite stx_eq_null_eq_lemma in Hprnul. { (* prototype is null *)
            forwards Hjproto : object_proto_null_lemma; try eassumption.
            repeat ljs_autoforward.
            jauto_js.
        } { (* prototype not null *)
            forwards Hjproto : object_proto_not_null_lemma; try eassumption.
            destruct Hjproto as (jptr'&ptr'&Heq1&Heq2&Hf').
            repeat ljs_autoforward.
            unfolds L.object_proto. rewrite Heq1 in *.
            forwards_th : IH. math. prove_bag.
            destr_concl; try ljs_handle_abort.
            jauto_js.
        }
    }
Qed.

Lemma has_property_lemma : forall BR k jst jc c st st' r jptr ptr s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privHasProperty [L.value_object ptr; L.value_string s]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_has_prop jptr s) 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    forwards : object_method_has_property_lemma; try eassumption.
    forwards_th : has_property_lemma_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    cases_isTrue;
    jauto_js.
Qed.

Lemma attributes_related_configurable_eq_lemma : forall BR attrs jattrs,
    attributes_related BR jattrs attrs ->    
    L.attributes_configurable attrs = J.attributes_configurable jattrs.
Proof.
    introv Hrel.
    inverts Hrel as Hrel; inverts Hrel; trivial.
Qed.

(* TODO move to LibBagExt *)
Lemma js_object_rem_property_lemma : forall jst jptr jobj s,
    binds jst jptr jobj ->
    JsPreliminary.object_rem_property jst jptr s
        (jst \(jptr := J.object_map_properties jobj (fun jprops => J.Heap.rem jprops s))).
Proof.
    introv Hbinds. unfolds. unfolds. jauto.
Qed.

(* TODO move to Common *)
Hint Resolve js_object_rem_property_lemma : js_ljs.

(* TODO move to common *)
Lemma object_properties_related_delete_lemma : forall BR jprops props s,
    object_properties_related BR jprops props ->
    object_properties_related BR (J.Heap.rem jprops s) (props \-- s). (* TODO heap delete in libbag *)
Proof.
    introv Hrel. intro s'.
    destruct (classic (s' = s)) as [Heq|Heq]. { (* equal *)
        skip. (* TODO *)
    } { (* different *)
        specializes Hrel s'.
        destruct_hyp Hrel.
        skip. skip. (* TODO *)
    }
Qed.

Hint Resolve object_properties_related_delete_lemma : js_ljs.

(* TODO move to common *)
Lemma object_prim_related_delete_lemma : forall BR jobj obj s,
    object_prim_related BR jobj obj ->
    object_prim_related BR jobj (L.delete_object_property obj s).
Proof.
    introv Hrel.
    destruct obj. simpls.
    inverts Hrel. constructor; assumption.
Qed.

Hint Resolve object_prim_related_delete_lemma : js_ljs.

(* TODO move to common *)
Lemma object_related_delete_lemma : forall BR jobj obj s,
    object_related BR jobj obj ->
    object_related BR
        (J.object_map_properties jobj (fun jprops => J.Heap.rem jprops s))
        (L.delete_object_property obj s).
Proof.
    introv Horel. destruct Horel.
    destruct obj.
    apply object_related_map_properties_preserved. 
    + eauto_js.
    + simpl. eauto_js.
Qed.

Hint Resolve object_related_delete_lemma : js_ljs.

Lemma delete_lemma : forall BR k jst jc c st st' r jptr ptr s b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDelete [L.value_object ptr; L.value_string s; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_delete_1 J.builtin_delete_default jptr s b) 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    forwards : object_method_get_own_property_lemma; try eassumption.
Opaque decide. (* TODO *)
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* field found *)
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Hbinds).
        forwards Hgop : object_method_get_own_property_default_binds_lemma; try eassumption.
        destruct_hyp Hgop.
        repeat ljs_autoforward.
        sets_eq b1 : (L.attributes_configurable attrs).
        destruct b1; symmetry in EQb1;
        erewrite attributes_related_configurable_eq_lemma in EQb1 by eassumption. { (* configurable *)
            forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf. eassumption.
            repeat ljs_autoforward.
            jauto_js 8.
        } { (* unconfigurable *)
            repeat ljs_autoforward.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th : type_error_lemma. eauto.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* non-strict *)
                repeat ljs_autoforward.
                jauto_js.
            }
        }
    } { (* field not found *)
        forwards Hgop : object_method_get_own_property_default_not_index_lemma; try eassumption.
        repeat ljs_autoforward.
        jauto_js.
    }
Qed.

(* ** More environment record manipulations TODO doc *)

(* TODO move *)
Lemma decl_env_record_vars_related_index_lemma : forall BR jx x s,
    decl_env_record_vars_related BR jx x ->
    index jx s = index x s.
Proof.
    introv Hder.
    specializes Hder s.
    destruct Hder as [(Hder1&Hder2)|(?&?&?&Hder0&Hder1&Hder2)]. {
        apply prop_eq_False_back in Hder1.
        apply prop_eq_False_back in Hder2.
        rewrite Hder1. rewrite Hder2. reflexivity.
    } {
        apply index_binds_inv in Hder0.
        apply index_binds_inv in Hder1.
        rew_logic; split; auto. 
    }
Qed.

(* TODO move *)
Lemma decl_env_record_vars_related_binds_lemma : forall BR jder props s attrs,
    decl_env_record_vars_related BR jder props ->
    binds props s attrs ->
    exists jmut jv v,
    attrs = L.attributes_data_of (L.attributes_data_intro v  
            (mutability_writable jmut) true (mutability_configurable jmut)) /\
    binds jder s (jmut, jv) /\ 
    decl_env_record_var_related BR jmut jv v.
Proof.
    introv Hder Hbinds.
    specializes Hder s.
    destruct Hder as [(Hder1&Hder2)|(jmut&jv&v&Hjxbinds&Hxbinds&Hder)]. {
        false. applys Hder2. prove_bag.
    }
    binds_determine.
    jauto_js.
Qed.

(* TODO move *)
Lemma decl_env_record_var_related_empty_lemma : forall BR jmut jv,
    decl_env_record_var_related BR jmut jv L.value_empty ->
    jmut = J.mutability_uninitialized_immutable /\ jv = J.value_prim J.prim_undef.
Proof.
    introv Hvrel.
    destruct Hvrel as [(Hmut&Hvrel)|Hvrel].
    + inverts Hvrel.
    + destruct_hyp Hvrel. jauto.
Qed.

(* TODO move *)
Lemma decl_env_record_var_related_not_empty_lemma : forall BR jmut jv v,
    v <> L.value_empty ->
    decl_env_record_var_related BR jmut jv v ->
    value_related BR jv v /\ jmut <> J.mutability_uninitialized_immutable.
Proof.
    introv Hnempty Hvrel.
    destruct Hvrel as [Hvrel|Hvrel]; destruct_hyp Hvrel; tryfalse.
    auto.
Qed.

(* TODO begin big block of moving! *)
(* TODO move *)
Definition mutability_of_bools b1 b2 :=
    if b1 then J.mutability_of_bool b2 else J.mutability_immutable.

(* TODO move *)
(*
Lemma js_env_record_write_decl_env_lemma : forall jst jeptr s jmut jv jder,
    binds jst jeptr (J.env_record_decl jder) ->
    J.env_record_write_decl_env jst jeptr s jmut jv = 
        jst \(jeptr := J.env_record_decl (J.decl_env_record_write jder s jmut jv)).
Proof.
    introv Hbinds.
    unfolds J.env_record_write_decl_env.
    rew_heap_to_libbag.
    simpl in Hbinds. unfolds J.env_record_binds. rew_heap_to_libbag in Hbinds.
    erewrite read_binds_inv by eauto.
    reflexivity.
Qed.
*)

Lemma decl_env_record_related_write_preserved : forall BR jder obj s jv v b1 b2,
    b1 || !b2 ->
    value_related BR jv v ->
    decl_env_record_related BR jder obj ->
    decl_env_record_related BR (J.decl_env_record_write jder s (mutability_of_bools b1 b2) jv)
        (L.set_object_property obj s (L.attributes_data_of (L.attributes_data_intro v b1 true b2))).
Proof.
    introv Hboolcond Hvrel Herel.
    unfolds J.decl_env_record_write.
    destruct obj.
    simpls.
    rew_heap_to_libbag.
    destruct Herel.
    constructor; try eassumption.
    unfolds.
    intro s'.
    destruct (classic (s = s')). { (* equal *)
        substs.
        right.
        do 3 eexists. splits; [rew_binds_eq; iauto | idtac | idtac]. { 
            simpls.
            rewrite binds_update_same_eq.
            destruct b1; destruct b2; simpl; tryfalse; try reflexivity. 
        } {
            unfolds. left. split; [idtac | eassumption].
            { intro; destruct b1; destruct b2; tryfalse. }
        }
    } { (* disequal *)
        lets Hx : decl_env_record_related_vars s'.
        destruct_hyp Hx.
        left. split. rew_index_eq. iauto.
        simpls. rew_index_eq. iauto.
        right. simpls. do 3 eexists. rew_heap_to_libbag in *. rew_binds_eq. iauto.
    }
Qed.

Lemma add_accessor_field_lemma : forall k c st st' r s v1 v2 b1 b2 ptr obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privAddAccessorField 
        [L.value_object ptr; L.value_string s; v1; v2; L.value_bool b1; L.value_bool b2])
        (L.out_ter st' r) ->
    binds st ptr obj ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_accessor_of 
        (L.attributes_accessor_intro v1 v2 b1 b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hlred Hbinds.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide. {
        repeat ljs_autoforward. 
        inv_ljs.
    }
    repeat ljs_autoforward.
    destruct obj.
    inv_ljs. {
        binds_determine.
        false. prove_bag.
    }
    simpls.
    do 3 (repeat ljs_autoforward; inv_ljs; [idtac | binds_inv; false; prove_bag 7]). 
    repeat ljs_autoforward. 
    simpls.
    repeat binds_inv.
    simpls.
    rew_bag_simpl.
    eauto_js.
Qed.

Lemma add_data_field_lemma : forall k c st st' r s v b0 b1 b2 ptr obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privAddDataField 
        [L.value_object ptr; L.value_string s; v; L.value_bool b0; L.value_bool b1; L.value_bool b2])
        (L.out_ter st' r) ->
    binds st ptr obj ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of (L.attributes_data_intro v b0 b1 b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hlred Hbinds.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide. {
        repeat ljs_autoforward. 
        inv_ljs.
    }
    repeat ljs_autoforward.
    destruct obj.
    inv_ljs. {
        binds_determine.
        false. prove_bag.
    }
    simpls.
    do 3 (repeat ljs_autoforward; inv_ljs; [idtac | binds_inv; false; prove_bag 7]). 
    repeat ljs_autoforward. 
    simpls.
    repeat binds_inv.
    simpls.
    rew_bag_simpl.
    eauto_js.
Qed.

Lemma decl_env_add_binding_lemma : forall BR k jst jc c st st' r jder jeptr ptr obj b1 b2 jv v s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool b1; L.value_bool b2]) (L.out_ter st' r) -> 
    b1 || !b2 ->
    binds st ptr obj ->
    binds jst jeptr (J.env_record_decl jder) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    decl_env_record_related BR jder obj ->
    value_related BR jv v ->
    fact_js_env jeptr ptr \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of 
        (L.attributes_data_intro v b1 true b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s /\ ~index jder s /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr jder s (mutability_of_bools b1 b2) jv) st'.
Proof.
    introv Hlred Hboolcond Hbinds Hjbinds Hcinv Hinv Herel Hvrel Hfact.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    forwards_th Hx : add_data_field_lemma. eassumption.
    destruct_hyp Hx.
    splits; try eauto_js.
    {
    lets Hx : decl_env_record_related_vars Herel s. 
    destruct_hyp Hx; prove_bag.
    }
    {
    destruct obj.
    eapply state_invariant_modify_env_record_preserved; try eassumption.
    eapply env_record_related_decl.
    lets Hx : decl_env_record_related_write_preserved Hboolcond Hvrel Herel. 
    eapply Hx. 
    reflexivity.
    }
Qed.

Lemma decl_env_add_mutable_binding_lemma : forall BR k jst jc c st st' r jder jeptr ptr obj b2 jv v s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool true; L.value_bool b2]) (L.out_ter st' r) -> 
    binds st ptr obj ->
    binds jst jeptr (J.env_record_decl jder) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    decl_env_record_related BR jder obj ->
    value_related BR jv v ->
    fact_js_env jeptr ptr \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of 
        (L.attributes_data_intro v true true b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s /\ ~index jder s /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) jv) st'.
Proof.
    intros. eapply decl_env_add_binding_lemma; eauto.
Qed.

Lemma create_mutable_binding_some_lemma : forall jst jc jeptr s b2 jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s (Some b2)) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) 
        (J.value_prim J.prim_undef))).
Proof.
    introv Hbinds Hnind. eauto_js.
Qed. 

Lemma create_mutable_binding_none_lemma : forall jst jc jeptr s jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s None) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool false) 
        (J.value_prim J.prim_undef))).
Proof.
    introv Hbinds Hnind. eauto_js.
Qed. 

Lemma js_mutability_of_bool_is_mutable : forall b,
    J.mutability_is_mutable (J.mutability_of_bool b).
Proof. destruct b; intro; tryfalse. Qed.

Hint Resolve js_mutability_of_bool_is_mutable : js_ljs.

Lemma js_mutability_of_bool_is_mutable_if_rewrite : forall T b (x1 : T) x2,
    (If J.mutability_is_mutable (J.mutability_of_bool b) then x1 else x2) = x1.
Proof.
    introv. cases_if. reflexivity. false. eauto_js.
Qed.

Hint Rewrite js_mutability_of_bool_is_mutable_if_rewrite : js_ljs.

Hint Extern 80 => progress rew_heap_to_libbag : js_ljs.

Lemma create_set_mutable_binding_some_lemma : forall jst jc jeptr s b2 jder jv b,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_set_mutable_binding jeptr s (Some b2) jv b) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) jv)).
Proof.
    introv Hbinds Hnind.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    unfolds J.env_record_write_decl_env.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding. eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl. eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x.
    unfolds J.env_record_write_decl_env.
    rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed. 

Hint Resolve create_set_mutable_binding_some_lemma : js_ljs.

Lemma create_set_mutable_binding_none_lemma : forall jst jc jeptr s jder jv b,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_set_mutable_binding jeptr s None jv b) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool false) jv)).
Proof.
    introv Hbinds Hnind.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    unfolds J.env_record_write_decl_env.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding.
    rew_heap_to_libbag. eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl.
    rew_heap_to_libbag. eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x.
    unfolds J.env_record_write_decl_env.
    repeat rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed.

Hint Resolve create_set_mutable_binding_none_lemma : js_ljs.
(* TODO end big block of moving! *)

(* *** Methods of environment records *)

Lemma get_binding_value_lemma : forall BR k jst jc c st st' r ptr s b jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvGetBindingValue 
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_env_record_get_binding_value jeptr s b) (fun _ => True).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hd; rewrite stx_eq_empty_eq_lemma in Hd. { (* TODO uninitialized immutable *)
            skip. (* TODO *)
        } {
            repeat ljs_autoforward.
            simpl.
            forwards (Hvrel&Hjmut) : decl_env_record_var_related_not_empty_lemma; try eassumption.
            jauto_js 15.
        }
    } { (* object records *)
        skip.
    }
Qed.

(* TODO should not be necessary *)
Hint Extern 3 (J.red_expr _ _ (J.expr_assign_1 _ _ _) _) => eapply J.red_expr_assign_1_simple : js_ljs.

Lemma mutability_not_immutable_lemma : forall jmut,
    jmut <> J.mutability_uninitialized_immutable ->
    jmut <> J.mutability_immutable -> 
    mutability_writable jmut = true.
Proof.
    introv Hx1 Hx2.
    destruct jmut; tryfalse; try reflexivity.
Qed.

Lemma decl_env_record_vars_related_write_lemma : forall BR jder props s jmut jv v,
    decl_env_record_vars_related BR jder props ->
    decl_env_record_var_related BR jmut jv v ->
    decl_env_record_vars_related BR (jder\(s:=(jmut, jv)))
        (props\(s:=L.attributes_data_of 
            (L.attributes_data_intro v (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Hvrels Hvrel.
    intro s'.
    destruct (classic (s = s')). {
        substs. 
        right.
        jauto_js.
    } {
        specializes Hvrels s'.
        destruct_hyp Hvrels. {
            left. split; prove_bag.
        } {
            right. repeat eexists; prove_bag.
        }
    }
Qed.

Hint Extern 3 (decl_env_record_vars_related _ ?jder _) => 
    not (is_evar jder); eapply decl_env_record_vars_related_write_lemma : js_ljs.

Lemma decl_env_record_related_write_lemma : forall BR jder s obj jmut jv v,
    decl_env_record_related BR jder obj ->
    decl_env_record_var_related BR jmut jv v ->
    decl_env_record_related BR 
        (J.decl_env_record_write jder s jmut jv)
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Herel Hvrel.
    destruct obj. destruct object_attrs.
    destruct Herel.
    unfolds L.object_proto. unfolds L.object_class. unfolds L.object_extensible.
    simpls.
    constructor; eauto.
    apply decl_env_record_vars_related_write_lemma; assumption.
Qed.

Hint Extern 3 (decl_env_record_related _ ?jer _) => 
    not (is_evar jer); eapply decl_env_record_related_write_lemma : js_ljs.

Lemma object_internal_write_hint : forall obj s attrs,
    L.object_internal obj = L.object_internal (L.set_object_property obj s attrs).
Proof.
    destruct obj. reflexivity.
Qed.

Lemma object_internal_read_option_write_hint : forall obj obj' s,
    L.object_internal obj = L.object_internal obj' ->
    L.object_internal obj\(s?) = L.object_internal obj'\(s?).
Proof.
    introv Heq. rewrite Heq. reflexivity.
Qed.

Hint Resolve object_internal_read_option_write_hint object_internal_write_hint : js_ljs.

Hint Extern 1 (decl_env_record_var_related _ _ _ _) => unfolds : js_ljs.

(*
Lemma env_record_related_decl_write_lemma : forall BR jder s obj jmut jv v,
    env_record_related BR (J.env_record_decl jder) obj ->
    decl_env_record_var_related BR jmut jv v ->
    env_record_related BR 
        (J.env_record_decl (J.decl_env_record_write jder s jmut jv)) 
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Herel Hvrel.
    inverts Herel as Herel.
    constructor. apply decl_env_record_related_write_lemma; assumption.
Qed.

Hint Extern 3 (env_record_related _ ?jer _) => 
    not (is_evar jer); eapply env_record_related_decl_write_lemma : js_ljs.
*)

(*
Lemma env_record_related_decl_write : forall BR jder s obj jmut jv v,
    value_related BR jv v ->
    env_record_related BR (J.env_record_decl jder) obj ->
    jmut <> J.mutability_uninitialized_immutable ->
    env_record_related BR 
        (J.env_record_decl (J.decl_env_record_write jder s jmut jv)) 
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Hvrel Herel Hjmut. 
    destruct obj. destruct object_attrs.
    inverts Herel as Herel. inverts Herel. 
    unfolds L.object_proto. unfolds L.object_class. unfolds L.object_extensible.
    simpls.
    constructor. constructor; eauto.
    simpl.
    intro s'.
    destruct (classic (s = s')) as [Hs|Hs]. {
        subst_hyp Hs.
        right. unfolds decl_env_record_var_related.
        jauto_js.
    } {
        lets Hx : decl_env_record_related_vars s'.
        destruct_hyp Hx. {
            left. 
            asserts Hs' : (s' <> s). solve [eauto].
            unfolds J.decl_env_record_write. repeat rew_heap_to_libbag. 
            split; intro Hi; eapply index_update_diff_inv in Hi; eauto.
        } {
            right. 
            unfolds J.decl_env_record_write. repeat rew_heap_to_libbag. 
            prove_bag 20.
        }
    }
Qed.

Hint Extern 3 (env_record_related _ ?jer _) => not (is_evar jer); eapply env_record_related_decl_write : js_ljs.
*)

Lemma set_mutable_binding_lemma : forall BR k jst jc c st st' r v ptr s b jeptr jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvSetMutableBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_set_mutable_binding jeptr s jv b) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hd; rewrite stx_eq_empty_eq_lemma in Hd. { (* TODO uninitialized immutable *)
            skip. (* TODO *)
        }
        simpl in Hd.
        forwards (Hvrel'&Hjmut) : decl_env_record_var_related_not_empty_lemma; try eassumption.
        destruct (classic (jmut = J.mutability_immutable)) as [Heqmut|Heqmut]. { (* immutable binding *)
            subst_hyp Heqmut.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th Hx : type_error_lemma. eauto_js.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* nonstrict *)
                repeat ljs_autoforward.
                jauto_js 10. 
            }
        } { (* mutable binding *)
            repeat ljs_autoforward.
            rewrite mutability_not_immutable_lemma in H8 by eassumption. (* TODO *)
            repeat ljs_autoforward.
            inv_ljs; repeat binds_determine; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            jauto_js 10. 
        }
    } { (* object records *)
        skip. (* TODO *)
    }
Qed.

Lemma has_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvHasBinding
        [L.value_object ptr; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_env_record_has_binding jeptr s) (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Hidx. {
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            jauto_js 10.
        } {
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            asserts Hjidx : (~J.decl_env_record_indom jder s0). { assumption. }
            jauto_js 10.
        }
    } { (* object records *)
        skip. (* TODO *)
    }
Qed.

Lemma create_mutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr b ob,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    b = unsome_default false ob ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s ob) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hb.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        forwards_th Hx : decl_env_add_mutable_binding_lemma; try prove_bag.
        destruct_hyp Hx.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* object records *)
        skip. (* TODO *)
    }
Qed.

Lemma create_mutable_binding_lemma_some : forall BR k jst jc c st st' r ptr s jeptr b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s (Some b)) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    eapply create_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_mutable_binding_lemma_none : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_false]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s None) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    eapply create_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_set_mutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr b b' ob v jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool b; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    b = unsome_default false ob ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s ob jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel Hb.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    forwards_th : create_mutable_binding_lemma; try eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th : set_mutable_binding_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    jauto_js 10.
Qed.

Lemma create_set_mutable_binding_lemma_some : forall BR k jst jc c st st' r ptr s jeptr b b' v jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool b; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s (Some b) jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel.
    eapply create_set_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_set_mutable_binding_lemma_none : forall BR k jst jc c st st' r ptr s jeptr b' v jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool false; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s None jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel.
    eapply create_set_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_immutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateImmutableBinding
        [L.value_object ptr; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_immutable_binding jeptr s) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        skip. (* TODO *)
(*
        forwards_th Hx : decl_env_add_mutable_binding_lemma; try prove_bag.
        destruct_hyp Hx.
        repeat ljs_autoforward.
        jauto_js 15.
*)
    } { (* object records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
Qed.

(* TODO should not be needed *)
Hint Extern 1 (J.red_expr _ _ (J.spec_env_record_initialize_immutable_binding _ _ _) _) =>
    eapply J.red_spec_env_record_initialize_immutable_binding : js_ljs.

Lemma initialize_immutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr jv v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvInitializeImmutableBinding 
        [L.value_object ptr; L.value_string s; v]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_initialize_immutable_binding jeptr s jv) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
Opaque decide.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hstxeq; rewrite stx_eq_empty_eq_lemma in Hstxeq; simpl in Hstxeq. { (* imm *)
            subst_eq Hstxeq.
            forwards Hx : decl_env_record_var_related_empty_lemma. eassumption.
            destruct_hyp Hx.
            repeat ljs_autoforward.
            destruct obj.
            inv_ljs; repeat binds_determine; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            inv_ljs; repeat binds_inv; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            simpl in H3. (* TODO *)
            binds_inv.
            simpl.
            rew_bag_simpl.
            jauto_js 10.
        } {
            repeat ljs_autoforward. inv_ljs.
        }
    } {
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
Qed.

(* ** Function calls *)

Lemma object_method_call_some_lemma : forall BR jst st jptr ptr obj clo,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_code obj = L.value_closure clo ->
    exists jcall,
    J.object_method J.object_call_ jst jptr (Some jcall) /\
    call_related jcall (L.value_closure clo).
Proof.
    introv Hinv Hbs Hbinds Hclo.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    inverts object_prim_related_call as Hp1 Hp2. {
        symmetry in Hp2. unfolds J.object_method.
        rewrite <- Hclo.
        jauto_js.
    } {
        tryfalse.
    } 
Qed.

Lemma object_method_code_some_lemma : forall BR jst st jptr ptr obj v,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "usercode" v ->
    exists jfb is jle,
    J.object_method J.object_code_ jst jptr (Some jfb) /\
    J.object_method J.object_formal_parameters_ jst jptr (Some is) /\
    J.object_method J.object_scope_ jst jptr (Some jle) /\
    usercode_related BR jfb is jle v.
Proof.
    introv Hinv Hbs Hbinds Hibinds.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_usercode by eassumption.
    inverts object_prim_related_usercode as Hp1 Hp2 Hp3 Hp4.
    symmetry in Hp2. symmetry in Hp3. symmetry in Hp4.
    unfolds J.object_method.
    jauto_js.
Qed.

Lemma object_strict_lemma : forall BR jst st jptr ptr obj v jfb,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "strict" v ->
    J.object_method J.object_code_ jst jptr (Some jfb) ->
    exists b,
    v = L.value_bool b /\
    J.funcbody_is_strict jfb = b.
Proof.
    introv Hinv Hbs Hbinds Hibinds Hcode.
    destruct Hcode as (jobj'&Hjbinds&Hzzz).
    rew_heap_to_libbag in Hjbinds.
    lets Horel : heaps_bisim_consistent_bisim_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs Hjbinds Hbinds.
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_func_strict by eassumption.
    inverts object_prim_related_func_strict as Hp1 Hp2.
    inverts Hp1.
    rewrite Hzzz in Hp2.
    injects.
    jauto_js.
Qed.

Lemma usercode_context_invariant_restore_lemma : forall BR jeptr ptr jle c jv v b v' v'' v''',
    initBR \c BR ->
    binds c "$context" v' ->
    fact_js_env jeptr ptr \in BR ->
    fact_ctx_parent ptr v' \in BR ->
    value_related BR jv v ->
    usercode_context_invariant BR jle b c ->
    context_invariant BR 
        (J.execution_ctx_intro_same (jeptr::jle) jv b) 
        (c\("args" := v'')\("$this" := v)\("obj" := v''')
           \("$context" := L.value_object ptr)\("$vcontext" := L.value_object ptr)).
Proof.
    introv Hinit Hbinds Hf1 Hf2 Hthisrel Hucinv.
    lets Hlerel : usercode_context_invariant_lexical_env_related Hucinv Hbinds.
    destruct Hucinv.
    constructor. {
        assumption.
    } {
        constructor; introv Hb; 
        repeat rewrite binds_update_diff_eq in Hb by prove_bag;
        repeat rewrite binds_update_same_eq in Hb by prove_bag;
        try subst_hyp Hb; simpl; eauto_js 2.
    } 
    + eauto_js 8.
    + constructor; introv Hmem; inverts Hmem as Hmem; eauto_js.
Qed.

Lemma usercode_context_invariant_restore : forall BR k jle c jv v b v' v'' v''' jst st st' r jc' c',
    L.red_exprh k (c\("args" := v'')\("$this" := v)\("obj" := v''')) st 
        (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v']) (L.out_ter st' r) ->
    context_invariant BR jc' c' ->
    state_invariant BR jst st ->
    usercode_context_invariant BR jle b c ->
    binds c "$context" v' ->
    value_related BR jv v ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v'} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    context_invariant BR'
        (J.execution_ctx_intro_same (fresh jst::jle) jv b) 
        (c\("args" := v'')\("$this" := v)\("obj" := v''')
          \("$context" := L.value_object (fresh st))\("$vcontext" := L.value_object (fresh st))) /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hcinv Hinv Hucinv Hbinds Hvrel.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). jauto_js.
    lets Hlerel : usercode_context_invariant_lexical_env_related Hucinv Hbinds.
    forwards_th Hx : only_state_invariant_new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists; splits; try reflexivity; try eassumption.
    lets Hincl : context_invariant_bisim_includes_init Hcinv.
    eapply usercode_context_invariant_restore_lemma; eauto_js.
Qed.

(* TODO: move to TLC LibLogic *)
Lemma case_classic_l_eq : forall P Q, (P \/ (~ P /\ Q)) = (P \/ Q).
Proof.
    introv. rew_logic. split.
    + iauto.
    + auto using case_classic_l.
Qed.

Lemma case_classic_r_eq : forall P Q, (Q \/ (P /\ ~ Q)) = (P \/ Q).
Proof.
    introv. rew_logic. split.
    + iauto.
    + auto using case_classic_r.
Qed.

(* TODO move *)
Lemma js_prog_intro_eta : forall p, J.prog_intro (J.prog_intro_strictness p) (J.prog_elements p) = p.
Proof.
    introv. destruct p. reflexivity.
Qed.

(* TODO move *)
Lemma array_idx_lemma : forall BR k jst jc c st st' ptr jvs vs s k' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privArrayIdx [L.value_object ptr; L.value_string s])
        (L.out_ter st' r) ->
    s = string_of_nat k' ->
    fact_iarray ptr vs \in BR ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    state_invariant BR jst st' /\
    st = st' /\ 
    exists jv v,
    r = L.res_value v /\
    value_related BR jv v /\
    (k' >= length vs /\ jv = J.value_prim J.prim_undef /\ v = L.value_undefined \/ Nth k' jvs jv /\ Nth k' vs v).
Proof.
Admitted. (* TODO *)

Lemma values_related_length_lemma : forall BR jvs vs,
    values_related BR jvs vs ->
    length jvs = length vs.
Proof.
    introv Hvrel.
    inductions Hvrel. { reflexivity. } {
        rew_length. rewrite IHHvrel. reflexivity.
    }
Qed.

Lemma binding_inst_formal_params_lemma_lemma : forall BR k jst jc c st st' r is vs jvs1 jvs2 ptr ptr1 jeptr b k',
    L.red_exprh k c st (L.expr_basic (L.expr_seqs_then L.expr_empty
            (map E.init_arg (zipl_stream (LibStream.map string_of_nat (nat_stream_from k')) is)))) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR (jvs1 ++ jvs2) vs ->
    k' = length jvs1 /\ length jvs2 > 0 \/ k' >= length jvs1 /\ jvs2 = [] ->
    binds c "$strict" (L.value_bool b) ->
    binds c "$vcontext" (L.value_object ptr) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_formal_params jvs2 jeptr is b) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv.
    unfolds E.init_args.
    inductions is gen BR k jst st jvs1 jvs2;
    introv Hlred Hcinv Hinv Hvrels Hk' Hbinds1 Hbinds2 Hbinds3 Hf1 Hf2. {
        repeat ljs_autoforward.
        jauto_js 10.
    }
    simpl in Hlred.
    rew_map in Hlred.
    repeat ljs_autoforward.
    forwards_th Harridx : array_idx_lemma. reflexivity. eassumption. eassumption.
    destruct Harridx as (?&Heq1&jv&v&Heq2&Hvrel&Harridx). subst_hyp Heq1. subst_hyp Heq2.
    asserts Hjvs2 : (k' >= length jvs1 /\ jvs2 = [] /\ v = L.value_undefined /\ jv = J.value_prim J.prim_undef \/ 
            k' = length jvs1 /\ exists jvs2', jvs2 = jv::jvs2'). {
        destruct Hk' as [(Hk1&Hk2)|(Hk1&Hk2)]. {
            right. split. assumption. 
            destruct jvs2; rew_length in Hk2; try solve [false; math].
            destruct Harridx as [Harridx|Harridx]. {
                erewrite <- values_related_length_lemma in Harridx by eassumption.
                rew_length in Harridx. destruct_hyp Harridx. false. math.
            }
            destruct Harridx as (Harridx1&Harridx2).
            apply Nth_app_inv in Harridx1.
            destruct Harridx1 as [Harridx1|Harridx1]. {
                apply Nth_lt_length in Harridx1. false. math.
            }
            destruct Harridx1 as (k''&Heqk''&Harridx1).
            asserts Hzero : (k'' = 0). { math. } subst_hyp Hzero.
            inverts Harridx1.
            jauto.
        } {
            left. 
            destruct Harridx as [Harridx|Harridx]. {
                destruct_hyp Harridx. jauto.
            }
            subst_hyp Hk2.
            destruct Harridx as (Harridx1&Harridx2).
            rew_app in Harridx1.
            apply Nth_lt_length in Harridx1. false. math.
        }
    }
    clear Harridx. clear Hk'.
    asserts Hexit : (exists jvs1' jvs2', values_related BR (jvs1' ++ jvs2') vs /\
            (S k' = length jvs1' /\ length jvs2' > 0 \/ S k' >= length jvs1' /\ jvs2' = []) /\
            (k' >= length jvs1 /\ jvs2 = [] /\ v = L.value_undefined /\ jv = J.value_prim J.prim_undef /\
                jvs1' = jvs1 /\ jvs2' = jvs2 \/ 
             k' = length jvs1 /\ jvs1' = jvs1 & jv /\ jvs2 = jv::jvs2')). {
        destruct Hjvs2 as [Hjvs2|Hjvs2]. {
            exists jvs1 jvs2.
            destruct_hyp Hjvs2. splits. 
            + assumption. 
            + right. split. math. reflexivity.
            + left. jauto_js.
        } {
            destruct_hyp Hjvs2. destruct jvs2' as [|jv' jvs2']. {
                exists (jvs1&jv) (@nil J.value). splits.
                + rew_app. assumption.
                + right. split. { rew_length. math. } reflexivity.
                + right. jauto_js.
            }
            exists (jvs1&jv) (jv'::jvs2'). splits. 
            + rew_app. assumption.
            + left. split. { rew_length. math. } { rew_length. math. }
            + right. jauto_js.
        }
    }
    repeat ljs_autoforward.
    inverts red_exprh H3. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b0. { (* binding already exists *)
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct Hexit as (jvs1'&jvs2'&Hvrels'&Hsk'&Hjvs2').
        forwards_th Hx : IHis; try prove_bag. eauto_js.
        destr_concl; [idtac | destruct_hyp Hjvs2'; try ljs_handle_abort].
        destruct_hyp Hjvs2'; jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_mutable_binding_lemma_none. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort]. 
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct Hexit as (jvs1'&jvs2'&Hvrels'&Hsk'&Hjvs2').
        forwards_th Hx : IHis; try prove_bag. eauto_js.
        destr_concl; [idtac | destruct_hyp Hjvs2'; try ljs_handle_abort].
        destruct_hyp Hjvs2'; jauto_js 10.
    }
Qed.

Lemma binding_inst_formal_params_lemma : forall BR k jst jc c st st' r is vs jvs ptr ptr1 jeptr b,
    L.red_exprh k c st (L.expr_basic (E.init_args is)) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    binds c "$strict" (L.value_bool b) ->
    binds c "$vcontext" (L.value_object ptr) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_formal_params jvs jeptr is b) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv Hlred Hcinv Hinv Hvrels Hbinds1 Hbinds2 Hbinds3 Hf1 Hf2.
    asserts Hvrels' : (values_related BR ([]++jvs) vs). { rew_app. assumption. }
    forwards_th : binding_inst_formal_params_lemma_lemma; try prove_bag.
    destruct jvs; rew_length; intuition math.
Qed.

(* TODO move *)
Lemma red_spec_creating_function_object_ok : forall BR k jst jc c' c st st' r is s jp jle,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privMakeFunctionObject 
            [L.value_closure (funcbody_closure (to_list c) is jp); L.value_number (length is); L.value_string s; 
             L.value_bool (J.prog_intro_strictness jp)])
        (L.out_ter st' r) ->
    context_invariant BR jc c' ->
    state_invariant BR jst st ->
    (forall v, binds c "$context" v -> lexical_env_related BR jle v) ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_creating_function_object is (J.funcbody_intro jp s) jle (J.prog_intro_strictness jp)) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hcinv Hinv Himpl.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : add_data_field_lemma. prove_bag.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    sets_eq b : (J.prog_intro_strictness jp).
(*
    destruct b. { (* strict *)
        repeat ljs_autoforward.
        skip. (* TODO *)
    } { (* not strict *)
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
*)
Admitted. (* TODO *)

(* TODO move to ejs *)
Lemma exprjs_prog_strictness_eq : forall jp, E.prog_strictness (E.js_prog_to_ejs jp) = J.prog_intro_strictness jp.
Proof.
    introv. destruct jp. reflexivity.
Qed.

(* TODO move *)
Ltac determine_fact_js_obj :=
    match goal with
    | Hfact1 : fact_js_obj ?jptr ?ptr1 \in ?BR1, Hfact2 : fact_js_obj ?jptr ?ptr2 \in ?BR2,
      Hinv : state_invariant ?BR _ _ |- _ =>
        let Hsub1 := fresh in let Hsub2 := fresh in let Heq := fresh "Heq" in 
        asserts Hsub1 : (BR1 \c BR); [prove_bag | idtac];
        asserts Hsub2 : (BR2 \c BR); [prove_bag | idtac];
        lets Heq : heaps_bisim_consistent_lfun_obj (state_invariant_heaps_bisim_consistent Hinv) 
            (incl_in Hsub1 Hfact1) (incl_in Hsub2 Hfact2);
        clear Hsub1; clear Hsub2; try (subst_hyp Heq; clear Hfact2)
    end.

Ltac determine_fact_js_env :=
    match goal with
    | Hfact1 : fact_js_env ?jptr ?ptr1 \in ?BR1, Hfact2 : fact_js_env ?jptr ?ptr2 \in ?BR2,
      Hinv : state_invariant ?BR _ _ |- _ =>
        let Hsub1 := fresh in let Hsub2 := fresh in let Heq := fresh "Heq" in 
        asserts Hsub1 : (BR1 \c BR); [prove_bag | idtac];
        asserts Hsub2 : (BR2 \c BR); [prove_bag | idtac];
        lets Heq : heaps_bisim_consistent_lfun_env (state_invariant_heaps_bisim_consistent Hinv) 
            (incl_in Hsub1 Hfact1) (incl_in Hsub2 Hfact2);
        clear Hsub1; clear Hsub2; try (subst_hyp Heq; clear Hfact2)
    end.

Lemma create_arguments_object_ok : forall BR k jst jc c st st' r jptr ptr ptr1 ptr2(*ptr3*)is jvs vs jeptr jlenv v b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmkArgsObj
        [L.value_object ptr2; L.value_null(*object ptr3*); L.value_object ptr1; L.value_object ptr; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    lexical_env_related BR jlenv v ->
    fact_js_obj jptr ptr \in BR ->
    fact_iarray ptr1 vs \in BR ->
(*     fact_iarray ptr3 (map L.value_string is) \in BR -> TODO non-strict args obj *)
    fact_js_env jeptr ptr2 \in BR ->
    fact_ctx_parent ptr2 v \in BR ->
    concl_ext_expr_value BR jst jc c st st' r
        (J.spec_create_arguments_object jptr is jvs (jeptr::jlenv) b) 
        (fun jv => exists ptr0, jv = J.value_object ptr0).
Proof.
Admitted. (* TODO *)

Lemma binding_inst_arg_obj_lemma : forall BR k jst jc c st st' r jptr ptr ptr1 ptr2(*ptr3*)is jvs vs jeptr jlenv v b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvDefineArgsObjOk
        [L.value_object ptr2; L.value_null(*object ptr3*); L.value_object ptr1; L.value_object ptr; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    lexical_env_related BR jlenv v ->
    fact_js_obj jptr ptr \in BR ->
    fact_iarray ptr1 vs \in BR ->
(*    fact_iarray ptr3 (map L.value_string is) \in BR -> TODO non-strict args obj *)
    fact_js_env jeptr ptr2 \in BR ->
    fact_ctx_parent ptr2 v \in BR ->
    J.execution_ctx_variable_env jc = jeptr::jlenv ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_arg_obj jptr is jvs jeptr b) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hvrel Hlrel Hf1 Hf2 Hf3 Hf4 Hvenv.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : create_arguments_object_ok; try prove_bag.
    rewrite <- Hvenv in Hx.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    destruct b. { (* strict *)
        repeat ljs_autoforward.
        forwards_th : create_immutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : initialize_immutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    } { (* non-strict *)
        repeat ljs_autoforward.
        forwards_th : create_set_mutable_binding_lemma_none. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    }
Qed.

Lemma binding_inst_function_decls_lemma : forall BR k jst jc c st st' r jfds jeptr ptr b1 b2,
    L.red_exprh k c st (L.expr_basic 
        (E.init_funcs b1 E.make_fobj (map E.js_funcdecl_to_func jfds))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool b2) ->
    binds c "$vcontext" (L.value_object ptr) ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_function_decls jeptr jfds b2 b1) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv.
    unfolds E.init_funcs.
    inductions jfds gen BR k jst st;
    introv Hlred Hcinv Hinv Hbinds1 Hbinds2 Hf. {
        repeat ljs_autoforward.
        jauto_js.
    }
    destruct a. destruct funcdecl_body.
    rew_map in Hlred.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th : red_spec_creating_function_object_ok. skip. (* { TODO in ES5 variable env required, fixed in ES6
        introv Hbinds.
        binds_inv.
        applys (execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv)).
        assumption.
    } *)
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    inverts red_exprh H12. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b. { (* binding already exists *)
        repeat ljs_autoforward.
        cases_decide as Hgctx. { (* on global context *)
            skip. (* TODO global context *)
        }
        asserts Hq : (jeptr <> J.env_loc_global_env_record). {
            unfolds LjsInitEnv.privglobalContext.
            rewrite stx_eq_object_eq_lemma in Hgctx.
            forwards Hger : context_invariant_global_env_record_lemma Hcinv.
            intro Hjeptr. subst_hyp Hjeptr. apply Hgctx.
            determine_fact_js_env.
            reflexivity.
        }
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : IHjfds; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_mutable_binding_lemma_some. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : IHjfds; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    }
Qed.

Lemma binding_inst_var_decls_lemma : forall BR k jst jc c st st' r is jeptr ptr b1 b2,
    L.red_exprh k c st (L.expr_basic (E.init_vars b1 is)) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool b2) ->
    binds c "$vcontext" (L.value_object ptr) ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_var_decls jeptr is b1 b2) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv.
    unfolds E.init_vars.
    inductions is gen BR k jst st;
    introv Hlred Hcinv Hinv Hbinds1 Hbinds2 Hf. {
        repeat ljs_autoforward.
        jauto_js.
    }
    rew_map in Hlred.
    repeat ljs_autoforward.
    inverts red_exprh H3.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b. { (* binding already exists *)
        repeat ljs_autoforward.
        forwards_th : IHis; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_set_mutable_binding_lemma_some. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : IHis; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    }
Qed.

Opaque E.init_args E.init_vars E.init_funcs.

Lemma binding_inst_global_lemma : forall BR k jst jc c st st' r ptr jp,
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_prog false E.make_fobj (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr) ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_global None jp []) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hbinds1 Hbinds2.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds2.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_var_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    jauto_js 15.
Qed.

Lemma binding_inst_eval_lemma : forall BR k jst jc c st st' r ptr jp,
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_prog true E.make_fobj (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr) ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_eval None jp []) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hbinds1 Hbinds2.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds2.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_var_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    jauto_js 15.
Qed.

Lemma binding_inst_func_lemma : forall BR k jst jc c st st' r ptr ptr1 ptr2 jptr jp jvs vs is,
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_func E.make_fobj is (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    binds c "obj" (L.value_object ptr) ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr2) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_formal_parameters_ jst jptr (Some is) ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_func (Some jptr) jp jvs) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hvrels Hbinds1 Hbinds2 Hbinds3 Hbinds4.
    introv Hf1 Hf2 Hom.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds3.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_formal_params_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    unfolds E.init_args_obj.
    inverts red_exprh H16. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    cases_decide; [idtac | repeat inv_ljs].
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    destruct b. { (* has binding named "arguments" *)
        repeat ljs_autoforward.
        forwards_th : binding_inst_var_decls_lemma; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* no binding named "arguments" *)
        repeat ljs_autoforward.
        forwards_th : binding_inst_arg_obj_lemma; try prove_bag. eauto_js. eauto_js.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : binding_inst_var_decls_lemma; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    }
Qed.

Opaque E.init_bindings_func.

(* TODO move *)
Hint Constructors J.red_prog : js_ljs.

Hint Extern 1 (J.red_prog _ _ (J.prog_1 _ _) _) => eapply J.red_prog_1_stat : js_ljs. 
Hint Extern 50 => progress unfolds J.res_overwrite_value_if_empty : js_ljs.

Lemma prog_els_last_lemma : forall el els,
    E.expr_seqs (List.map E.js_element_to_ejs (els & el)) = 
        E.expr_seq (E.expr_seqs (List.map E.js_element_to_ejs els)) (E.js_element_to_ejs el).
Proof.
    introv.
    unfolds E.expr_seqs.
    rewrite_all list_map_tlc.
    rew_list.
    reflexivity.
Qed.

Lemma prog_ok_lemma : forall els BR k jst jc c st st' r b,
    ih_stat k ->
    L.red_exprh k c st (L.expr_basic (E.ejs_to_ljs (E.expr_seqs (List.map E.js_element_to_ejs els))))
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' jst' jr,
    J.red_prog jst jc (J.prog_basic (J.prog_intro b els)) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.
Proof.
    induction els as [|el els] using list_rev_ind;
    introv IHt Hlred Hcinv Hinv. { (* no more elements *)
        repeat ljs_autoforward.
        jauto_js.
    } (* one element more *)
    rewrite prog_els_last_lemma in Hlred.
    repeat ljs_autoforward.
    specializes IHels (ih_stat_S IHt).
    specializes_th IHels.
    destruct_hyp IHels. res_related_abort; try ljs_handle_abort. (* TODO destr_concl_auto *)
    repeat ljs_autoforward.
    destruct el. { (* statement *)
        repeat ljs_autoforward.
        destr_concl.
        res_related_invert; repeat ljs_autoforward; try resvalue_related_only_invert; jauto_js. 
    } { (* funcdecl *)
        destruct f. (* TODO remove *)
        repeat ljs_autoforward.
        jauto_js.
    }
Qed.

Lemma prog_ok_call_lemma : forall BR k jst jc c st st' r jp,
    ih_stat k ->
    L.red_exprh k c st 
        (L.expr_basic (E.ejs_to_ljs (E.expr_seqs (List.map E.js_element_to_ejs (J.prog_elements jp)))))
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' jst' jr,
    J.red_prog jst jc (J.prog_basic jp) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.
Proof.
    intros. destruct jp. eapply prog_ok_lemma; eassumption.
Qed.

Lemma call_lemma : forall BR k jst jc c st st' r jfb is jle v v1 vs ptr ptr1 jptr jv1 jvs,
    ih_stat k ->
    ih_call_prealloc k ->
    L.red_exprh k c st (L.expr_app_2 v [L.value_object ptr; v1; L.value_object ptr1]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    usercode_related BR jfb is jle v ->
    value_related BR jv1 v1 ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_scope_ jst jptr (Some jle) ->
    J.object_method J.object_formal_parameters_ jst jptr (Some is) ->
    J.object_method J.object_code_ jst jptr (Some jfb) ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_entering_func_code_3 jptr jvs (J.funcbody_is_strict jfb) jfb jv1 (J.spec_call_default_1 jptr)) 
        (fun jv => True).
Proof.
    introv IHt IHp Hlred Hcinv Hinv Hucrel Hvrel Hvrels Hbs Hbs1.
    introv Hom1 Hom2 Hom3.
    inverts Hucrel as Huci.
    unfolds funcbody_closure. unfolds funcbody_expr. unfolds E.make_lambda_expr.
    cases_let as Hprog.
    inverts red_exprh Hlred.
    ljs_apply.
    subst c'.
    repeat ljs_autoforward.
    lets Hlerel : usercode_context_invariant_lexical_env_related Huci ___; try eassumption.
    forwards_th Hx : usercode_context_invariant_restore; try eassumption. 
    destruct_hyp Hx.
    repeat ljs_autoforward.
    rewrite <- (js_prog_intro_eta jp) in Hprog.
    simpl in Hprog.
    injects Hprog.
    rewrite js_prog_intro_eta in *.
    lets Hstrict : usercode_context_invariant_has_strict Huci. (* TODO do a lemma *)
    rewrite index_binds_eq in Hstrict. destruct_hyp Hstrict.
    lets Hstreq : usercode_context_invariant_strict Huci Hstrict. subst_hyp Hstreq.
    forwards_th : binding_inst_func_lemma; try prove_bag 8. { eauto_js. } skip. (* TODO state consistency *)
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    asserts Hom3' : (J.object_method J.object_code_ jst' jptr (Some (J.funcbody_intro jp s))). 
        skip. (* TODO state consistency *)
    lets [Hfbe|Hfbe] : classic (J.funcbody_empty (J.funcbody_intro jp s)). { 
        (* special case required by the spec *)
        unfolds J.funcbody_empty. unfolds J.prog_empty.
        simpl in Hfbe. rewrite Hfbe in *.
        repeat ljs_autoforward.
        jauto_js 10.
    }
    forwards_th Hx : prog_ok_call_lemma.
    destruct_hyp Hx. (* TODO destr_concl *)
    res_related_invert; repeat ljs_autoforward. { (* normal exit *)
        jauto_js 10.
    } { (* exception *)
        jauto_js 10.
    } { (* return *)
        jauto_js 10.
    } { (* break *)
        (* TODO: should never happen due to syntax constraints, but unable to prove this now. *)
        skip. 
    } { (* continue *)
        (* TODO: should never happen due to syntax constraints, but unable to prove this now. *)
        skip. 
    }
Qed.

Lemma red_spec_call_ok : forall BR k jst jc c st st' ptr v ptr1 vs r jptr jv jvs,
    ih_stat k ->
    ih_call_prealloc k ->
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privAppExpr [L.value_object ptr; v; L.value_object ptr1]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_call jptr jv jvs) (fun jv => True).
Proof.
    introv IHt IHp Hlred Hcinv Hinv Hvrel Hvrels Halo Hbs. 
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    lets (jcon&Hmeth&Hcall) : object_method_call_some_lemma Hinv Hbs ___; try eassumption.
    inverts Hcall. { (* prealloc *)
        forwards Hx : IHp; [idtac |  
        forwards_th Hxx : Hx]; try eassumption. omega. (* TODO *)
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* default *)
        inverts red_exprh H8.
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets (jfb&is&jle&Hmcode&Hparams&Hscope&Hcode) : object_method_code_some_lemma ___; try eassumption.
        lets (str&Heqstr&Hfbstr) : object_strict_lemma ___; try eassumption.
        subst_hyp Heqstr.
        inverts red_exprh H21. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        symmetry in Hfbstr.
        destruct str. { (* strict *)
            repeat ljs_autoforward.
            forwards_th Hcl : call_lemma; try eassumption.
            rewrite <- Hfbstr in Hcl.
            destr_concl; try ljs_handle_abort.
            jauto_js 15.
        } { (* not strict *)
            do 2 inv_fwd_ljs.
            (* TODO better condition handling *)
            ljs_out_redh_ter.
            ljs_bool_red_exprh; repeat determine_epsilon.
            cases_isTrue as Hevcond. { (* null or undefined *)
                repeat ljs_autoforward.
                rewrite case_classic_l_eq in Hevcond.
                asserts Hmycond : (jv = J.value_prim J.prim_null \/ jv = J.value_prim J.prim_undef). {
                    inverts Hvrel;
                    destruct Hevcond as [Hevcond|Hevcond]; inverts Hevcond; eauto_js.
                }
                forwards_th Hcl : call_lemma; try eassumption.
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            } 
            repeat ljs_autoforward.
            cases_decide as Hisobj. { (* is object *)
                repeat ljs_autoforward.
                inverts Hvrel; inverts Hisobj.
                forwards_th Hcl : call_lemma; try eassumption.
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            } { (* not object *)
                rewrite case_classic_l_eq in Hevcond.
                rew_logic in Hevcond. destruct Hevcond as (Hevcond1&Hevcond2).
                asserts Hmycond : (jv <> JsSyntax.value_prim JsSyntax.prim_null /\
                    jv <> JsSyntax.value_prim JsSyntax.prim_undef /\
                    JsPreliminary.type_of jv <> JsSyntax.type_object). {
                    inverts Hvrel; try solve [false; eauto_js]; eauto_js.
                }
                repeat ljs_autoforward.
                forwards_th : red_spec_to_object_ok.
                destr_concl; try ljs_handle_abort.
                res_related_invert.
                resvalue_related_invert.
                repeat ljs_autoforward.
                forwards_th Hcl : call_lemma; try eauto_js. skip. skip. skip. (* TODO state consistency issue! *)
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            }
        }
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.

Definition post_to_primitive jv jv' := 
    exists jp', jv' = J.value_prim jp' /\ forall jp, jv = J.value_prim jp -> jp = jp'.

Lemma post_to_primitive_lemma1 : forall jv1 jv2, post_to_primitive jv1 jv2 -> exists jpr, jv2 = J.value_prim jpr.
Proof.
    introv Hpp. unfold post_to_primitive in Hpp. destruct_hyp Hpp. eauto.
Qed.

Lemma post_to_primitive_lemma2 : forall jpr jv, 
    post_to_primitive (J.value_prim jpr) jv -> jv = J.value_prim jpr.
Proof.
    introv Hpp. unfold post_to_primitive in Hpp. destruct_hyp Hpp. 
    eapply func_eq_1. symmetry. eauto.
Qed.

Ltac js_post_to_primitive :=
    match goal with
    | H : post_to_primitive (J.value_prim ?jpr) ?jv |- _ =>
        match jv with
        | J.value_prim jpr => fail 1
        | _ => let H1 := fresh in lets H1 : post_to_primitive_lemma2 H; destruct_hyp H1
        end
    | H : post_to_primitive ?jv1 ?jv2 |- _ =>
        match jv2 with
        | J.value_prim _ => fail 1
        | _ => let H1 := fresh in lets H1 : post_to_primitive_lemma1 H; destruct_hyp H1
        end
    end.

Lemma red_spec_to_primitive_ok : forall BR k jst jc c st st' jv v jprefo r s,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitiveHint [v; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    option_preftype_name jprefo s ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_to_primitive jv jprefo) (post_to_primitive jv).
Proof.
    (* TODO *)
Admitted.

Lemma red_spec_to_primitive_ok_default : forall BR k jst jc c st st' jv v r,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitive [v])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_to_primitive jv None) (post_to_primitive jv).
Proof.
    introv Hlred Hcinv Hinv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok. eapply option_preftype_name_none.
    assumption.
Qed.

(** *** spec_expr_get_value_conv spec_to_boolean 
    It corresponds to [to_bool] in the desugaring. *)

Lemma red_spec_to_boolean_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToBoolean J.spec_to_boolean 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.

    ljs_apply.

    repeat ljs_autoforward. 

    inverts Hvrel; try injects; jauto_js.
Qed.

(* TODO move *)
Lemma to_primitive_primitive_noop_lemma : forall k c st st' r v s,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitiveHint [v; L.value_string s])
        (L.out_ter st' r) ->
    L.is_primitive v ->
    st = st' /\ r = L.res_value v.
Proof.
    introv Hlred Hprim.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide as Hisobj. {
        inverts Hisobj; inverts Hprim.
    }
    repeat ljs_autoforward.
    eauto.
Qed.

Lemma value_related_primitive_lemma : forall BR jv v,
    L.is_primitive v ->
    value_related BR jv v ->
    exists jpv, jv = J.value_prim jpv.
Proof.
    introv Hprim Hvrel.
    inverts Hprim; inverts Hvrel; jauto.
Qed.

Lemma convert_prim_to_number_lemma : forall BR jpv v,
    value_related BR (J.value_prim jpv) v ->
    L.value_to_num_cast v = J.convert_prim_to_number jpv.
Proof.
    introv Hvrel.
    inverts Hvrel; reflexivity.
Qed.

Lemma red_spec_to_number_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToNumber J.spec_to_number
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct (classic (L.is_primitive v0)) as [Hprim|Hprim]. {
        forwards_th Hx : to_primitive_primitive_noop_lemma. { eassumption. }
        destruct_hyp Hx.
        repeat ljs_autoforward.
        forwards Hx : value_related_primitive_lemma Hprim Hvrel.
        destruct_hyp Hx.
        erewrite convert_prim_to_number_lemma by eassumption.
        jauto_js.
    } 
    forwards_th Hx : red_spec_to_primitive_ok. {
        eapply option_preftype_name_some. eapply preftype_name_number.
    }
    inverts Hvrel; try solve [false; eauto_js].
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    js_post_to_primitive.
    resvalue_related_only_invert.
    erewrite convert_prim_to_number_lemma by eassumption.
    jauto_js.
Qed.

Lemma convert_prim_to_string_lemma : forall BR jpv v,
    value_related BR (J.value_prim jpv) v ->
    L.value_to_str_cast v = J.convert_prim_to_string jpv.
Proof.
    introv Hvrel.
    inverts Hvrel; reflexivity.
Qed.

Lemma red_spec_to_string_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToString J.spec_to_string
        (fun jv => exists n, jv = J.value_prim (J.prim_string n)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct (classic (L.is_primitive v0)) as [Hprim|Hprim]. {
        forwards_th Hx : to_primitive_primitive_noop_lemma. { eassumption. }
        destruct_hyp Hx.
        repeat ljs_autoforward.
        forwards Hx : value_related_primitive_lemma Hprim Hvrel.
        destruct_hyp Hx.
        erewrite convert_prim_to_string_lemma by eassumption.
        jauto_js.
    } 
    forwards_th Hx : red_spec_to_primitive_ok. {
        eapply option_preftype_name_some. eapply preftype_name_string.
    }
    inverts Hvrel; try solve [false; eauto_js].
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    match goal with H : post_to_primitive _ _ |- _ => unfold post_to_primitive in H; destruct_hyp H end. (* TODO *)
    resvalue_related_only_invert.
    erewrite convert_prim_to_string_lemma by eassumption.
    jauto_js.
Qed.

Lemma red_spec_to_boolean_ok : forall k je, 
    ih_expr k ->
    th_spec k (E.to_bool (js_expr_to_ljs je))
              (J.spec_expr_get_value_conv J.spec_to_boolean je) 
              (fun _ _ _ _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
                  r = L.res_value (L.value_bool b)).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.

    destr_concl; try ljs_handle_abort.

    repeat inv_internal_fwd_ljs.
    forwards_th : red_spec_to_boolean_unary_ok.

    destr_concl.
    res_related_invert.
    resvalue_related_invert. 
    jauto_js 6.
    jauto_js 6.
Qed.

Lemma construct_related_lemma : forall BR jst st jptr ptr obj v,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (LjsSyntax.object_internal obj) "construct" v ->
    exists jcon,
    construct_related jcon v.
Proof.
    introv Hinv Hbs Hbinds Hcbinds.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_construct by eassumption.
    inverts object_prim_related_construct.
    jauto.
Qed.

Lemma object_method_construct_lemma : forall BR jst st jptr ptr obj jcon,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    option_construct_related jcon (L.object_internal obj\("construct"?)) ->
    J.object_method J.object_construct_ jst jptr jcon.
Proof.
    introv Hinv Hbs Hbinds Hocrel.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    inverts Hocrel as Ho1 Ho2. {
        rewrite <- Ho2 in object_prim_related_construct.
        inverts object_prim_related_construct as Hp1 Hp2.
        asserts Heq : (a = a0). { (* TODO determinism lemma *)
            inverts Ho1 as Ho3; inverts Hp1 as Hp3; try reflexivity;
            try inverts Ho3; try inverts Hp3; reflexivity.
        }
        subst_hyp Heq.
        unfolds. jauto.
    }
    rewrite <- Ho1 in object_prim_related_construct.
    inverts object_prim_related_construct.
    unfolds. jauto.
Qed.

Lemma red_spec_construct_prealloc_ok : forall k jpre, th_construct_prealloc k jpre.
Proof.
    introv Hcinv Hinv Hvrels Halo Hcpre Hlred.
    inverts Hcpre.
Admitted.

Lemma red_spec_construct_ok : forall BR k jst jc c st st' ptr ptr1 vs r jptr jvs,
    ih_stat k ->
    ih_call_prealloc k ->
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
    introv IHt IHp Hlred Hcinv Hinv Hvrels Halo Hbs.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
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
        skip. (* TODO *)
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.

(* TODO lots of cleaning up needed! *)

Lemma ref_base_type_obj_not_unresolvable jref :
    ref_base_type_obj (J.ref_base jref) -> ~J.ref_is_unresolvable jref.
Proof.
    introv Hrbt Hjru. destruct jref. inverts Hrbt as Hoc. simpls. substs. 
    inverts Hoc. unfolds J.ref_is_unresolvable. unfolds J.ref_kind_of. 
    destruct jv; simpls; tryfalse. destruct p; tryfalse.
Qed.

Lemma js_not_identifier_not_unresolvable : forall je jref,
    js_reference_type je (J.ref_base jref) -> (forall s, je <> J.expr_identifier s) -> ~J.ref_is_unresolvable jref.
Proof.
    introv Hrt Hne.
    eapply ref_base_type_obj_not_unresolvable.
    inverts Hrt; try eassumption. 
    specializes Hne s. false.
Qed.

Lemma red_spec_lexical_env_get_identifier_ref_lemma : forall k BR jst jc c st st' r v s b v1 jlenv,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privEnvGetId [v; L.value_string s; v1]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    lexical_env_related BR jlenv v -> 
    exists k' c' v' jrbt jst' st'' BR',
    k' < k /\
    BR \c BR' /\
    state_invariant BR' jst' st'' /\
    L.red_exprh k' c' st'' (L.expr_app_2 v1 [v']) (L.out_ter st' r) /\
    J.red_spec jst jc (J.spec_lexical_env_get_identifier_ref jlenv s b) 
        (J.specret_val jst' (J.ref_intro jrbt s b)) /\
    ref_base_type_related BR' jrbt v' /\
    ref_base_type_var jrbt.
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hinv Hlrel.
    inverts red_exprh Hlred.
    ljs_apply.
    inverts Hlrel as Hlrel1 Hlrel2 Hlrel3. {
        repeat ljs_autoforward.
        jauto_js. 
    }
    repeat ljs_autoforward.
    forwards (jer&Hjbinds&Herel) : env_record_related_lookup_lemma Hinv Hlrel1. eassumption.
    inverts Herel as Herel. {
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Hidx; repeat ljs_autoforward. { (* var found *)
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            jauto_js 8.
        } { (* not found *)
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            rewrite <- decl_env_record_indom_to_libbag in Hidx. (* TODO can be removed somehow? *)
            lets Hp : state_invariant_ctx_parent_ok Hinv Hlrel2.
            destruct_hyp Hp. repeat binds_determine.
            specializes IH ___; try eassumption. math.
            destruct_hyp IH. jauto_js 8. 
        }
    } {
        skip. (* TODO object environments *)
    }
Qed.

(* TODO more things to sort *)

Lemma reference_match_lemma : forall (A : Type) (P : A -> Prop) ee f1 f2 f3,
    P (E.reference_match ee f1 f2 f3) ->
    (exists ee1 ee2, ee = E.expr_get_field ee1 ee2 /\ P (f1 ee1 ee2)) \/
    (exists s, ee = E.expr_var_id s /\ P (f2 s)) \/
    (~ejs_reference_producing ee /\ P (f3 ee)).
Proof.
    destruct ee; eauto.
Qed.

Definition exprjs_red_p k c st o e := L.red_exprh k c st (L.expr_basic e) o.

Lemma reference_match_red_exprh_lemma : forall k c st o ee f1 f2 f3,
    L.red_exprh k c st (L.expr_basic (E.reference_match ee f1 f2 f3)) o ->
    (exists ee1 ee2, ee = E.expr_get_field ee1 ee2 /\ L.red_exprh k c st (L.expr_basic (f1 ee1 ee2)) o) \/
    (exists s, ee = E.expr_var_id s /\ L.red_exprh k c st (L.expr_basic (f2 s)) o) \/
    (~ejs_reference_producing ee /\ L.red_exprh k c st (L.expr_basic (f3 ee)) o).
Proof.
    introv Hlred.
    applys reference_match_lemma (exprjs_red_p k c st o) Hlred.
Qed.

Inductive js_field_access : J.expr -> E.expr -> E.expr -> Prop :=
| js_field_access_access : forall je1 je2,
    js_field_access (J.expr_access je1 je2) (E.js_expr_to_ejs je1) (E.js_expr_to_ejs je2)
| js_field_access_member : forall je1 s,
    js_field_access (J.expr_member je1 s) (E.js_expr_to_ejs je1) (E.expr_string s).

Lemma js_field_access_reference_producing : forall je ee1 ee2,
    js_field_access je ee1 ee2 -> js_reference_producing je.
Proof.
    introv jsfe. inverts jsfe; eauto_js.
Qed.

Hint Constructors js_field_access : js_ljs.
Hint Resolve js_field_access_reference_producing : js_ljs.

Lemma reference_match_red_exprh_js_lemma : forall k c st o je f1 f2 f3,
    L.red_exprh k c st (L.expr_basic (E.reference_match (E.js_expr_to_ejs je) f1 f2 f3)) o ->
    (exists ee1 ee2, js_reference_producing je /\ js_field_access je ee1 ee2 /\ 
        L.red_exprh k c st (L.expr_basic (f1 ee1 ee2)) o) \/
    (exists s, js_reference_producing je /\ je = J.expr_identifier s /\ 
        L.red_exprh k c st (L.expr_basic (f2 s)) o) \/
    (~js_reference_producing je /\ L.red_exprh k c st (L.expr_basic (f3 (E.js_expr_to_ejs je))) o).
Proof.
    introv Hlred.
    lets Hx : reference_match_red_exprh_lemma Hlred.
    destruct je; try destruct l; try destruct b; try destruct f; destruct_hyp Hx; tryfalse;
    try match goal with H : ~ejs_reference_producing _ |- _ => false; apply H; solve [eauto_js 10] end;
    eauto_js 9. 
Qed.

Ltac reference_match_cases Hlred Hx Heq Hrp :=
    lets Hx : (reference_match_red_exprh_js_lemma _ _ _ _ Hlred);
    clear Hlred;
    destruct Hx as [(?ee&?ee&Hrp&Heq&Hlred)|[(?s&Hrp&Heq&Hlred)|(Hrp&Hx)]]; try subst_hyp Heq.

(* TODO move *)
Lemma js_red_expr_getvalue_not_ref_lemma : forall jst jc je jo jo',
    ~js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_out jo') ->
    jo = jo'.
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto.
Qed.

Lemma js_red_expr_getvalue_not_ref_lemma2 : forall jst jst' jc je jo jv,
    ~js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_val jst' jv) ->
    jo = J.out_ter jst' (J.res_normal (J.resvalue_value jv)).
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto.
Qed.

Lemma js_red_expr_getvalue_ref_lemma : forall jst jc je jo jo',
    js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_out jo') ->
    jo = jo' \/ exists jst' jref, jo = J.out_ter jst' (J.res_ref jref) /\
        J.red_spec jst' jc (J.spec_get_value (J.resvalue_ref jref)) (@J.specret_out J.value jo').
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto. eauto_js.
Qed.

Lemma js_red_expr_getvalue_ref_lemma2 : forall jst jst' jc je jo jv,
    js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_val jst' jv) ->
    exists jref jst'', jo = J.out_ter jst'' (J.res_ref jref) /\
        J.red_spec jst'' jc (J.spec_get_value (J.resvalue_ref jref)) (J.specret_val jst' jv).
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    jauto_js.
Qed.

Ltac js_red_expr_getvalue_fwd :=
    match goal with
    | Hnrp : ~js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_out _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_not_ref_lemma Hnrp Hgv;
        subst_hyp H
    | Hnrp : ~js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_val _ _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_not_ref_lemma2 Hnrp Hgv;
        subst_hyp H
    | Hnrp : js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_out _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_ref_lemma Hnrp Hgv;
        destruct_hyp H
    | Hnrp : js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_val _ _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_ref_lemma2 Hnrp Hgv;
        destruct_hyp H
    end.

(* Hint Resolve js_red_expr_getvalue_red_expr : js_ljs. *)
Ltac js_red_expr_getvalue_hint :=
    match goal with
    | Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo _
        |- J.red_expr ?jst ?jc (J.expr_basic ?je) _ =>
        applys js_red_expr_getvalue_red_expr Hgv
    end.

Hint Extern 5 (J.red_expr ?jst ?jc (J.expr_basic _) _) => js_red_expr_getvalue_hint : js_ljs.

Lemma js_field_access_not_unresolvable_lemma : forall jc jst jst' je ee1 ee2 jref jsr,
    js_field_access je ee1 ee2 ->
    js_red_expr_getvalue jst jc je (J.out_ter jst' (J.res_normal (J.resvalue_ref jref))) jsr ->
    ~J.ref_is_unresolvable jref.
Proof.
    introv Hjfa Hgv.
    inverts Hgv as Hxx Hgva.
    inverts Hgva as Ha Hb Hc. {
        inverts Ha as Hx. false. eauto_js.
    }
    applys js_not_identifier_not_unresolvable Hb.
    destruct Hjfa; eauto.
Qed.

Hint Resolve js_field_access_not_unresolvable_lemma : js_ljs.

Ltac ref_base_type_var_invert :=
    match goal with
    | H1 : ref_base_type_var ?jrbt, H2 : ref_base_type_related _ ?jrbt _ |- _ =>
        inverts H1; inverts H2;
        try match goal with
        | H3 : js_object_coercible (J.value_prim J.prim_undef) |- _ => solve [inverts H3; tryfalse]
        | _ => idtac
        end
    end.

(* ** Reference handling *)

(* TODO why get_value is an ext_spec, and put_value is ext_expr? *)
Lemma env_get_value_lemma : forall BR k jst jc c st st' r v s b jrbt,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvGetValue 
        [v; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    ref_base_type_related BR jrbt v ->
    ref_base_type_var jrbt ->
    concl_spec BR jst jc c st st' r 
        (J.spec_get_value (J.resvalue_ref (J.ref_intro jrbt s b))) 
        (fun BR' _ jv => 
            v <> L.value_null /\
            exists v', r = L.res_value v' /\ value_related BR' jv v' ).
Proof.
    introv Hlred Hcinv Hinv Hrbt Hrbtv.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    ref_base_type_var_invert. {
        repeat ljs_autoforward.
        forwards_th Hx : unbound_id_lemma.
        destr_concl; tryfalse; try ljs_handle_abort.
    }
    repeat ljs_autoforward.
    forwards_th : get_binding_value_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    jauto_js 15.
Qed.

Lemma env_put_value_lemma : forall BR k jst jc c st st' r v v' s b jrbt jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvPutValue 
        [v; L.value_string s; v'; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    ref_base_type_related BR jrbt v ->
    ref_base_type_var jrbt ->
    value_related BR jv v' ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_put_value (J.resvalue_ref (J.ref_intro jrbt s b)) jv) 
            (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hrbt Hrbtv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    ref_base_type_var_invert. {
        repeat ljs_autoforward.
        destruct b. { (* strict *)
            repeat ljs_autoforward.
            forwards_th Hx : unbound_id_lemma. 
            destr_concl; tryfalse.
            ljs_handle_abort.
        } { (* nonstrict *)
            repeat ljs_autoforward.
            skip. (* TODO involves the global object *)
        }
    }
    repeat ljs_autoforward.
    forwards_th : set_mutable_binding_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js 15.
Qed.
