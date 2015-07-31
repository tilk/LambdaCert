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
Implicit Type jp : J.prog.
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

(* Expressions *)

(** *** Functions *)

Lemma red_spec_creating_function_object_ok : forall BR k jst jc c st st' r is s jp jle,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privMakeFunctionObject 
            [L.value_closure (funcbody_closure (to_list c) is jp); L.value_number (length is); L.value_string s; 
             L.value_bool (J.prog_intro_strictness jp)])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    (forall v, binds c "$context" v -> lexical_env_related BR jle v) ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_creating_function_object is (J.funcbody_intro jp s) jle (J.prog_intro_strictness jp)) 
        (fun _ => True).
Proof.
    introv Hlred Hcinv Hinv Himpl. 
Admitted. (* TODO *)

Lemma exprjs_prog_strictness_eq : forall jp, E.prog_strictness (E.js_prog_to_ejs jp) = J.prog_intro_strictness jp.
Proof.
    introv. destruct jp. reflexivity.
Qed.

Lemma red_expr_nonrec_function_ok : forall k is fb,
    th_expr k (J.expr_function None is fb).
Proof.
    introv Hcinv Hinv Hlred.
    destruct fb.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th Hx : red_spec_creating_function_object_ok. { 
        eapply execution_ctx_related_lexical_env. 
        eapply context_invariant_execution_ctx_related. 
        eassumption.
    }
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    jauto_js 12.
Qed.

Lemma red_expr_rec_function_ok : forall k s is fb,
    th_expr k (J.expr_function (Some s) is fb).
Proof.
    introv Hcinv Hinv Hlred.
    destruct fb.
    repeat ljs_autoforward.
    forwards_th Hx : state_invariant_new_env_record_decl_lemma; try eassumption.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th Hx : red_spec_creating_function_object_ok. { 
        eapply execution_ctx_related_lexical_env. 
        eapply context_invariant_execution_ctx_related. 
        eassumption.
    }
    destr_concl; [idtac | skip]. (* TODO function object creation never fails *)
    (* TODO uninitialized binding business *)
Admitted. (* TODO *)

Lemma red_expr_function_ok : forall k os is fb,
    th_expr k (J.expr_function os is fb).
Proof.
    introv.
    destruct os.
    eapply red_expr_rec_function_ok.
    eapply red_expr_nonrec_function_ok.
Qed.

(** *** Literals *)

Lemma red_expr_literal_ok : forall k l,
    th_expr k (J.expr_literal l).
Proof.
    introv Hcinv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts red_exprh Hlred; ijauto_js.
Qed.

(** *** This *)

Lemma red_expr_this_ok : forall k,
    th_expr k J.expr_this.
Proof.
    introv Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    forwards Hx : execution_ctx_related_this_binding (context_invariant_execution_ctx_related Hcinv).
    { eassumption. }
    jauto_js 8.
Qed.

(** *** New *)

(* TODO move *)
Lemma values_related_snoc_lemma : forall BR jvl vl jv v,
    values_related BR jvl vl ->
    value_related BR jv v ->
    values_related BR (jvl&jv) (vl&v).
Proof.
    introv Hvrels Hvrel.
    induction Hvrels. {
        constructor. assumption. apply Forall2_nil.
    }
    rew_app.
    constructor; assumption.
Qed.

Lemma iarray_object_snoc_lemma : forall obj vl v,
    iarray_object obj vl ->
    iarray_object (L.set_object_property obj (string_of_nat (length vl))
             (LjsSyntax.attributes_data_of (L.attributes_data_intro v false false false))) (vl & v).
Proof.
    introv Halo.
    destruct Halo.
    destruct obj. simpl.
    constructor. {
        introv Hnth.
        apply Nth_app_inv in Hnth.
        destruct Hnth as [Hnth|Hnth]. {
            lets Hlen : Nth_lt_length Hnth.
            simpl. skip. (* TODO *) 
        }
        destruct Hnth as (m&Hk&Hnth).
        inverts Hnth as Hnth; [idtac | inverts Hnth].
        rew_nat in Hk.
        subst_hyp Hk.
        simpl.
        prove_bag.
    } {
        introv Hidx.
        simpl in Hidx.
        rew_index_eq in Hidx.
        destruct_hyp Hidx. { 
            lets Hx : iarray_all_args Hidx.
            destruct Hx as (?k&?v&Heq&Hx).
            eauto using Nth_app_l.
        }
        do 2 eexists. splits. reflexivity.
        eapply Nth_app_r. eapply Nth_here. math.
    }
Qed.

Lemma red_spec_list_lemma : forall k,
    ih_expr k -> forall k' jel BR jst jc c st jvl vl st' r obj len,
    (k' < k)%nat ->
    len = length vl ->
    L.red_exprh k' c st (L.expr_object_2 []
          (zipl_stream (id_stream_from len)
             (map E.make_args_obj_prop
                (List.map E.ejs_to_ljs (List.map E.js_expr_to_ejs jel)))) obj) (L.out_ter st' r) ->
    values_related BR jvl vl -> 
    iarray_object obj vl ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_spec BR jst jc c st st' r (J.spec_list_expr_1 jvl jel) 
        (fun BR' jst' jvl => exists vl ptr, 
            values_related BR' jvl vl /\ 
            fact_iarray ptr vl \in BR' /\
            r = L.res_value (L.value_object ptr)).
Proof.
    introv IHe. 
    inductions jel; introv Hlt Hlen Hlred Hvrel Halo Hcinv Hinv; subst len. {
        repeat ljs_autoforward.
        jauto_js 12.
    }
    repeat ljs_autoforward. 
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    lets Hvrel' : values_related_bisim_incl_preserved Hvrel. eassumption.
    forwards Hvrel'' : values_related_snoc_lemma Hvrel'. eassumption.
    forwards Halo' : iarray_object_snoc_lemma. eassumption.
    forwards_th : IHjel; try eapply Hvrel''; try eapply Halo'. omega. rew_length. reflexivity.
    destr_concl; try ljs_handle_abort.
    jauto_js 12.
Qed.

Lemma red_spec_list_ok : forall BR k jst jc c st jel st' r,
    ih_expr k ->
    L.red_exprh k c st (L.expr_basic (E.make_args_obj
        (List.map E.ejs_to_ljs (List.map E.js_expr_to_ejs jel)))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_spec BR jst jc c st st' r (J.spec_list_expr jel) 
        (fun BR' jst' jvl => exists vl ptr, 
            values_related BR' jvl vl /\ 
            fact_iarray ptr vl \in BR' /\
            r = L.res_value (L.value_object ptr)).
Proof.
    introv IHe Hlred Hcinv Hinv.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_list_lemma; try eapply Forall2_nil. omega. rew_length. reflexivity. {
        constructor.
        introv Hnth. inverts Hnth.
        introv Hidx. simpls. rew_index_eq in Hidx. tryfalse.
    }
    destr_concl; try ljs_handle_abort.
    jauto_js 12.
Qed.

(* TODO move *)
Opaque L.is_object_decidable. (* TODO MOVE *)
Opaque index_decidable_from_read_option. (* TODO move *)

Lemma not_object_hint : forall BR jv v,
    value_related BR jv v ->
    ~L.is_object v ->
    J.type_of jv <> J.type_object.
Proof.
    introv Hrel Hnobj Hjobj.
    destruct Hrel; tryfalse.
    apply Hnobj. constructor.
Qed.

Hint Resolve not_object_hint : js_ljs.

Lemma red_expr_new_ok : forall k je jel,
    ih_expr k ->
    ih_stat k ->
    ih_call_prealloc k ->
    th_expr k (J.expr_new je jel).
Proof.
    introv IHe IHt IHp HCinv Hinv Hlred.
    inverts red_exprh Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    inv_top_fwd_ljs.
    inv_top_fwd_ljs.
    ljs_out_redh_ter.
    forwards_th : red_spec_list_ok.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat (repeat ljs_autoforward || cases_decide). {
        inverts IH4. (* TODO *)
        rewrite index_binds_eq in H7. destruct H7 as (?x&H7). (* TODO *)
        forwards Hc : construct_related_lemma; try eassumption. eauto_js.
        destruct_hyp Hc.
        forwards Hx : object_method_construct_lemma; try eassumption. eauto_js. eauto_js.
        forwards_th : red_spec_construct_ok; try eassumption. eauto_js. eauto_js. (* TODO *)
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 12.
    } { 
        inverts IH4. (* TODO *)
        forwards Hx : object_method_construct_lemma; try eauto_js.
        forwards_th : type_error_lemma. iauto.
        destr_concl; tryfalse.
        jauto_js 12.
    } {
        forwards_th : type_error_lemma. iauto.
        destr_concl; tryfalse.
        jauto_js 12.
    }
Qed.

(** *** Call *)

(* TODO move *)
Lemma code_not_is_callable_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st -> 
    binds st ptr obj ->
    fact_js_obj jptr ptr \in BR ->
    L.object_code obj = L.value_undefined -> 
    ~J.is_callable jst (J.value_object jptr).
Proof.
    introv Hinv Hbinds Hbs Heq.
    introv (?x&Hj).
    destruct Hj as (jobj&Hjbinds&Hj).
    rew_heap_to_libbag in Hjbinds.
    lets Horel : heaps_bisim_consistent_bisim_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs Hjbinds Hbinds.
    clear Hinv. clear Hbs. clear Hbinds. clear Hjbinds.
    lets Hcrel : object_prim_related_call (object_related_prim Horel).
    destruct obj. destruct object_attrs. unfolds L.object_code. simpl in Heq. subst_hyp Heq.
    inverts Hcrel as Hc. inverts Hc as Hc. inverts Hc. (* TODO *)
    rewrite Hj in Hc. solve [tryfalse].
Qed.

Lemma code_is_callable_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st -> 
    binds st ptr obj ->
    fact_js_obj jptr ptr \in BR ->
    L.object_code obj <> L.value_undefined -> 
    J.is_callable jst (J.value_object jptr).
Proof.
    introv Hinv Hbinds Hbs Heq.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    clear Hinv. clear Hbs. clear Hbinds.
    lets Hcrel : object_prim_related_call (object_related_prim Horel).
    inverts Hcrel as Hc Hx; tryfalse.
    symmetry in Hx. 
    eexists. eexists. jauto_js.
Qed.

Lemma typeof_lemma : forall BR k c jst st st' jv v r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privTypeof [v]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    state_invariant BR jst st' /\
    st' = st /\
    r = L.res_value (L.value_string (J.typeof_value jst jv)).
Proof.
    introv Hlred Hinv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide as Hc1; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc1.
        cases_decide as Hcode; repeat ljs_autoforward.
        inverts Hcode. {
            lets Hnc : code_not_is_callable_lemma Hinv ___. eassumption. eassumption. auto.
            unfolds J.typeof_value. cases_if.
            jauto_js.
        } {
            lets Hc : code_is_callable_lemma Hinv ___. eassumption. eassumption. {
                intro Heq. apply Hcode. unfold L.object_code in Heq. rewrite Heq. eauto_js.
            }
            unfolds J.typeof_value. cases_if.
            jauto_js.
        }
    }
    cases_decide as Hc2; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc2.
        jauto_js.
    }
    cases_decide as Hc3; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc3.
        jauto_js.
    }
    cases_decide as Hc4; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc4.
        jauto_js.
    }
    cases_decide as Hc5; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc5.
        jauto_js.
    }
    cases_decide as Hc6; repeat ljs_autoforward. {
        inverts Hvrel; inverts Hc6.
        jauto_js.
    }
    inverts Hvrel; false; eauto_js.
Qed.

Lemma is_callable_lemma : forall BR k c st st' r jst jv v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privIsCallable [v]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    state_invariant BR jst st' /\
    st = st' /\
    r = L.res_value (L.value_bool (isTrue (J.is_callable jst jv))).
Proof.
    introv Hlred Hinv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    forwards_th Hx : typeof_lemma.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    splits; auto.
    cases_decide as Hd; do 2 apply func_eq_1; fold_bool; rew_reflect. {
        inverts Hd as Hd. 
        inverts Hvrel; tryfalse. simpl in Hd.
        cases_if. assumption.
    } {
        introv Hic.
        lets (?&Hc) : Hic.
        inverts Hvrel; tryfalse. apply Hd.
        simpl. cases_if. eauto_js.
    }
Qed.

Lemma implicit_this_lemma : forall BR k jst jc c st st' r jle jeptr v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvImplicitThis [v]) (L.out_ter st' r) ->
    lexical_env_related BR (jeptr::jle) v ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_env_record_implicit_this_value jeptr) (fun _ => True).
Proof.
    introv Hlred Hlrel Hcinv Hinv.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    inverts Hlrel as Hf1 Hf2 Hlrel.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma Hinv Hf1. eassumption.
    inverts Herel as Herel. { (* declarative record *)
        lets Hcl : decl_env_record_related_class Herel.
        cases_decide as Hx; 
            try solve [false; apply Hx; destruct obj; destruct object_attrs; cbv in Hcl; substs; eauto_js].
        repeat ljs_autoforward.
        jauto_js.
    } { (* object record *)
        lets Hcl : object_env_record_related_class Herel.
        cases_decide as Hx; 
            try solve [inverts Hx as Hcl1; destruct obj; destruct object_attrs; cbv in Hcl; substs; tryfalse].
        repeat ljs_autoforward.
        cases_decide as Hy; 
            try solve [false; apply Hy; destruct obj; destruct object_attrs; cbv in Hcl; substs; eauto_js].
        repeat ljs_autoforward.
        lets Hpt : object_env_record_related_provideThis Herel.
        binds_determine.
        destruct b; repeat ljs_autoforward. {
            lets Hbin : object_env_record_related_bindings Herel.
            lets Hbis : object_env_record_related_bisim Herel.
            binds_determine.
            jauto_js.
        } {
            jauto_js.
        }
    }
Qed.

Lemma red_expr_call_3_hint : forall S0 S C jo rv jv is_eval_direct vs, (* Steps 4-5 *)
    ~ J.is_callable S jv ->
    J.red_expr S C (J.spec_error J.native_error_type) jo ->
    J.red_expr S0 C (J.expr_call_3 (J.res_normal rv) jv is_eval_direct (J.ret S vs)) jo.
Proof.
    introv Hic Hjred. 
    destruct jv. {
        eapply J.red_expr_call_3. left. intro Hx. destruct p; tryfalse. eassumption.
    } {
        eapply J.red_expr_call_3. right. eauto. assumption.
    }
Qed.

Hint Resolve red_expr_call_3_hint : js_ljs.

Lemma is_callable_obj : forall jst jv,
    J.is_callable jst jv ->
    exists jptr, jv = J.value_object jptr.
Proof.
    introv (?&Hic).
    destruct jv; tryfalse. eauto.
Qed.

Lemma red_expr_call_ok : forall k je jel,
    ih_expr k ->
    ih_stat k ->
    ih_call_prealloc k ->
    th_expr k (J.expr_call je jel).
Proof.
    introv IHe IHs IHp HCinv Hinv Hlred. 
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_app.
    reference_match_cases Hlred Hx Heq Hrp. 
    {
        skip.
    } {
        cases_if. { (* TODO eval *)
            skip.
        }
        sets_eq je : (J.expr_identifier s).
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort. (* TODO abort *)
        repeat ljs_autoforward.
        skip. skip.
    } {
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        do 5 inv_top_fwd_ljs.
        ljs_out_redh_ter.
        forwards_th : red_spec_list_ok.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        forwards_th Hx : is_callable_lemma.
        destruct_hyp Hx.
        cases_isTrue as Hic. { (* is callable *)
            repeat ljs_autoforward.
            lets (jptr&Heq) : is_callable_obj Hic. subst_hyp Heq.
            inverts IH4. (* TODO *)
            forwards_th : red_spec_call_ok; try eassumption. eauto_js.
            destruct (classic (jptr = J.object_loc_prealloc J.prealloc_global_eval)). {
                skip. (* TODO eval *)
            }
            destr_concl; try ljs_handle_abort. 
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 15.
        } { (* not callable *)
            repeat ljs_autoforward.
            forwards_th : type_error_lemma. eauto.
            destr_concl; tryfalse; try ljs_handle_abort.
        }
    }
Qed.

(** *** Identifier *)

Lemma red_expr_identifier_ok : forall k i,
    th_expr k (J.expr_identifier i).
Proof.
    introv Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
        eassumption.
    forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
    destruct_hyp Hx.
    inverts red_exprh Hx3.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
        eassumption.
    subst_hyp Hstrict.
    forwards_th Hx : env_get_value_lemma. eauto_js. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js 10.
Qed.

(** *** Conditional *)

Lemma red_expr_conditional_ok : forall k je1 je2 je3,
    ih_expr k ->
    th_expr k (J.expr_conditional je1 je2 je3).
Proof.
    introv IHe Hcinv Hinv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.

    forwards_th : red_spec_to_boolean_ok. 

    destr_concl.
    destruct b;
    inv_internal_fwd_ljs;
    apply_ih_expr.
    (* true *)
    jauto_js 18.
    (* false *)
    jauto_js 18. 
    (* abort *)
    ljs_handle_abort.
Qed.

(** *** Assignment *)

Lemma red_expr_assign0_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_assign je1 None je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_assign.
    reference_match_cases Hlred Hx Heq Hrp. { (* object field assign *)
        skip. (* TODO *)
    } { (* variable assign *)
        repeat ljs_autoforward.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx.
        inverts red_exprh Hx3.
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        inverts red_exprh H12. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        subst_hyp Hstrict.
        forwards_th Hx : env_put_value_lemma. eauto_js. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* invalid lhs, error thrown *)
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        forwards_th Hx : reference_error_lemma. eauto_js.
        destr_concl; tryfalse.
        ljs_handle_abort.
    }
Qed.

Lemma red_expr_assign_ok : forall k je1 je2 oo,
    ih_expr k ->
    th_expr k (J.expr_assign je1 oo je2).
Proof.
    introv IHe.
    destruct oo.
    skip.
    eapply red_expr_assign0_ok; assumption.
Qed.

(** *** Unary operators *)

(* TODO move *)
Lemma nat_one_is_js_one : @eq number one 1.
Admitted. (* TODO *)

Lemma prepost_op_to_ljs_lemma : forall op F b je,
    J.prepost_op op F b ->
    exists lop F',
    L.num_binary_op lop F' /\
    F = (fun n => F' n 1) /\
    js_expr_to_ljs (J.expr_unary_op op je) = 
        E.make_xfix lop b E.ejs_to_ljs (E.js_expr_to_ejs je).
Proof.
    introv Hjop.
    inverts Hjop; unfolds js_expr_to_ljs; simpl;
    [exists L.binary_op_add | exists L.binary_op_sub 
    |exists L.binary_op_add | exists L.binary_op_sub];
    eexists; (split; [eapply L.num_binary_op_add || eapply L.num_binary_op_sub | idtac]);
    rewrite <- nat_one_is_js_one; jauto_js.    
Qed.

Lemma js_prepost_unary_op_hint : forall op F b,
    J.prepost_op op F b -> J.prepost_unary_op op.
Proof. introv Hx. unfolds. eauto. Qed.

Hint Resolve js_prepost_unary_op_hint : js_ljs.

Hint Extern 3 (J.red_expr _ _ (J.expr_prepost_1 _ _) _) => eapply J.red_expr_prepost_1_valid : js_ljs.

(* TODO move, ljs only *)
Lemma eval_binary_op_num_lemma : forall op F st n1 n2 v,
    L.num_binary_op op F ->
    L.eval_binary_op op st (L.value_number n1) (L.value_number n2) v ->
    v = L.value_number (F n1 n2).
Proof.
    introv Hnumop Hevop.
    inverts Hevop as Hxop;
    inverts Hnumop; try inverts Hxop;
    reflexivity.
Qed.

Lemma red_expr_unary_op_prepost_ok : forall k op F b je,
    J.prepost_op op F b ->
    ih_expr k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    introv Hop IHe Hcinv Hinv Hlred.
    lets (lop&F'&Hlop&Feq&Heq) : prepost_op_to_ljs_lemma Hop.
    rewrite Heq in Hlred. clear Heq.
    subst_hyp Feq.
    unfolds E.make_xfix.
    reference_match_cases Hlred Hx Heq Hrp. { (* ++ on objects *)
        skip. (* TODO *)
    } { (* ++ on variables *)
        repeat ljs_autoforward.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx.
        inverts red_exprh Hx3.
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        subst_hyp Hstrict.
        forwards_th Hx : env_get_value_lemma. eauto_js. eassumption.
        destr_concl; try ljs_handle_abort. 
        repeat ljs_autoforward.
        forwards_th Hx : red_spec_to_number_unary_ok.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        repeat ljs_autoforward.
        inverts red_exprh H26. (* TODO *)
        ljs_apply.
        repeat ljs_autoforward.
        forwards Hveq : eval_binary_op_num_lemma; try eassumption.
        subst_hyp Hveq.
        forwards_th Hx : env_put_value_lemma. eauto_js. eassumption. 
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct b; repeat ljs_autoforward; jauto_js 15.
    } { (* ++ on general expressions *)
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort. 
        repeat ljs_autoforward.
        forwards_th Hx : red_spec_to_number_unary_ok.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        repeat ljs_autoforward.
        forwards_th Hx : reference_error_lemma. eauto_js.
        destr_concl; tryfalse.
        ljs_handle_abort.
    }
Qed.

Lemma red_expr_unary_op_2_not_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryNot (J.expr_unary_op_2 J.unary_op_not)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHe Hcinv Hinv Hvrel Hlred.
    inverts Hlred. 
    ljs_apply.
    ljs_context_invariant_after_apply.
    simpls.  
    repeat ljs_autoforward.
    forwards_th : red_spec_to_boolean_unary_ok. 
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma red_expr_unary_op_not_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_not je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th : red_expr_unary_op_2_not_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 8.
Qed.

Lemma red_expr_unary_op_2_add_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryPlus (J.expr_unary_op_2 J.unary_op_add)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHe Hcinv Hinv Hvrel Hlred.
    inverts Hlred. 
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    repeat binds_inv.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. 
Qed.

Lemma red_expr_unary_op_add_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_add je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th : red_expr_unary_op_2_add_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 8.
Qed.

Lemma red_expr_unary_op_2_neg_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryNeg (J.expr_unary_op_2 J.unary_op_neg)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHe Hcinv Hinv Hvrel Hlred.
    inverts Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma red_expr_unary_op_neg_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_neg je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th : red_expr_unary_op_2_neg_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 15.
Qed.

Lemma red_expr_unary_op_void_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_void je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js 8.
Qed.

Lemma red_expr_unary_op_bitwise_not_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_bitwise_not je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    (* TODO ToInt32 spec_to_int32 *)
Admitted. (* TODO *)

Lemma red_expr_unary_op_typeof_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_typeof je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_typeof.
    reference_match_cases Hlred Hx Heq Hrp. {
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort. 
        repeat ljs_autoforward.
        forwards_th Hx : typeof_lemma.
        destruct_hyp Hx.
        jauto_js 15.
    } {
        repeat ljs_autoforward.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx.
        inverts red_exprh Hx3.
        ljs_apply.
        ljs_context_invariant_after_apply.
        ref_base_type_var_invert. {
            repeat ljs_autoforward.
            jauto_js 10.
        }
        repeat ljs_autoforward.
        lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
        inverts Herel as Herel. { (* declarative records *)
            inverts Herel.
            unfolds L.object_class.
            cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
            repeat ljs_autoforward.
            lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
            destruct_hyp Hx.
            forwards_th Hx : typeof_lemma.
            destruct_hyp Hx.
            jauto_js 12.
        } { (* object records *)
            skip.
        }
    } {
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        repeat ljs_autoforward.
        forwards_th Hx : typeof_lemma.
        destruct_hyp Hx.
        jauto_js 15.
    }
Qed.

(* TODO move *)

Lemma spec_env_record_delete_binding_1_deletable_hint : forall jv S C L x Ed S',
      J.decl_env_record_binds Ed x J.mutability_deletable jv ->
      S' = J.env_record_write S L (J.env_record_decl (J.decl_env_record_rem Ed x)) ->
      J.red_expr S C (J.spec_env_record_delete_binding_1 L x (J.env_record_decl Ed)) 
          (J.out_ter S' (J.res_val (J.value_prim (J.prim_bool true)))).
Proof.
    introv Hb Hs. eapply J.red_spec_env_record_delete_binding_1_decl_indom. eassumption. 
    cases_if. eauto_js.
Qed.

Hint Resolve spec_env_record_delete_binding_1_deletable_hint : js_ljs.

Lemma spec_env_record_delete_binding_1_deletable_hint2 : forall jv S C L x Ed jmut,
      J.decl_env_record_binds Ed x jmut jv ->
      jmut <> J.mutability_deletable ->
      J.red_expr S C (J.spec_env_record_delete_binding_1 L x (J.env_record_decl Ed)) 
          (J.out_ter S (J.res_val (J.value_prim (J.prim_bool false)))).
Proof.
    introv Hb Hd. eapply J.red_spec_env_record_delete_binding_1_decl_indom. eassumption. 
    cases_if. eauto_js.
Qed.

Hint Resolve spec_env_record_delete_binding_1_deletable_hint2 : js_ljs.

Lemma env_record_related_decl_rem : forall BR jder s obj,
    env_record_related BR (J.env_record_decl jder) obj ->
    env_record_related BR (J.env_record_decl (J.decl_env_record_rem jder s)) (L.delete_object_property obj s).
Proof.
    introv Herel. 
    destruct obj. destruct object_attrs.
    inverts Herel as Herel. inverts Herel. 
    unfolds L.object_proto. unfolds L.object_class. unfolds L.object_extensible.
    simpls.
    constructor. constructor; eauto.
    simpl.
    intro s'.
    destruct (classic (s = s')). { 
        substs.
        left. split. skip. eauto_js. (* TODO heap/libbag mismatch *)
    } {
        lets Hx : decl_env_record_related_vars s'. destruct_hyp Hx. {
            skip. (* TODO *)
        } 
        right. skip. (* TODO *)
    }
Qed.

Hint Extern 3 (env_record_related _ ?jer _) => not (is_evar jer); eapply env_record_related_decl_rem : js_ljs.

Lemma mutability_not_deletable_lemma : forall jmut,
    jmut <> J.mutability_uninitialized_immutable ->
    jmut <> J.mutability_deletable -> 
    mutability_configurable jmut = false.
Proof.
    introv Hx1 Hx2.
    destruct jmut; tryfalse; try reflexivity.
Qed.

Lemma red_expr_unary_op_delete_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_delete je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_delete.
    reference_match_cases Hlred Hx Heq Hrp. {
        skip. (* TODO fields *)
    } {
        repeat ljs_autoforward.
        inverts red_exprh H7. (* TODO *)
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx.
        inverts red_exprh Hx3.
        ljs_apply.
        ljs_context_invariant_after_apply.
        repeat ljs_autoforward.
        lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        subst_hyp Hstrict.
        inv_ljs. { (* strict *)
            symmetry in H15. (* TODO *) (* J.execution_ctx_strict jc = true *)
            repeat ljs_autoforward.
            forwards_th Hx : syntax_error_lemma. eauto_js.
            destr_concl; tryfalse.
            ref_base_type_var_invert; ljs_handle_abort.
        } (* not strict *)
        symmetry in H15. (* TODO *)
        repeat ljs_autoforward.
        ref_base_type_var_invert. {
            repeat ljs_autoforward.
            jauto_js 15.
        }
        repeat ljs_autoforward.
        lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
        inverts Herel as Herel. { (* declarative records *)
            inverts Herel.
            unfolds L.object_class.
            cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
            repeat ljs_autoforward.
            lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
            destruct_hyp Hx.
            destruct (classic (jmut = J.mutability_deletable)) as [Hmut|Hmut]. { (* deletable *)
                subst_hyp Hmut.
                repeat ljs_autoforward.
                unfolds L.get_object_property. (* TODO ? *)
                erewrite read_option_binds_inv in H25 by solve [eassumption]. (* TODO *)
                repeat ljs_autoforward.
                destruct obj.
                jauto_js 15.
            } {
                rewrite mutability_not_deletable_lemma in H16 by eassumption.
                repeat ljs_autoforward.
                jauto_js 15.
            }
        } { (* object records *)
            skip. (* TODO *)
        }
    } {
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        repeat ljs_autoforward.
        jauto_js 8.
    }
Qed.

Lemma red_expr_unary_op_ok : forall op k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    destruct op; introv.
    apply red_expr_unary_op_delete_ok.
    apply red_expr_unary_op_void_ok.
    apply red_expr_unary_op_typeof_ok.
    applys red_expr_unary_op_prepost_ok. eauto_js.
    applys red_expr_unary_op_prepost_ok. eauto_js.
    applys red_expr_unary_op_prepost_ok. eauto_js.
    applys red_expr_unary_op_prepost_ok. eauto_js.
    apply red_expr_unary_op_add_ok.
    apply red_expr_unary_op_neg_ok.
    apply red_expr_unary_op_bitwise_not_ok.
    apply red_expr_unary_op_not_ok.
Qed.

(** *** Binary operators *)

(* TODO move *)
Lemma state_invariant_lfun_obj : forall BR jst st,
    state_invariant BR jst st ->
    heaps_bisim_lfun_obj BR.
Proof. 
    introv Hinv. 
    eapply heaps_bisim_consistent_lfun_obj. eapply state_invariant_heaps_bisim_consistent. eassumption.
Defined.

Lemma state_invariant_rfun_obj : forall BR jst st,
    state_invariant BR jst st ->
    heaps_bisim_rfun_obj BR.
Proof. 
    introv Hinv. 
    eapply heaps_bisim_consistent_rfun_obj. eapply state_invariant_heaps_bisim_consistent. eassumption.
Defined.

Lemma equality_test_for_same_type_lemma : forall BR jst st jtp jv1 jv2 v1 v2,
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    J.type_of jv1 = jtp ->
    J.type_of jv2 = jtp ->
    decide (L.stx_eq v1 v2) = J.equality_test_for_same_type jtp jv1 jv2.
Proof.
    introv Hinv Hvrel1 Hvrel2 Heq1 Heq2. 
    subst jtp.
    destruct Hvrel1; destruct Hvrel2; tryfalse; try reflexivity.
    (* number *) 
    cases_decide as Hstx; fold_bool; rew_refl.
    inverts Hstx as Hnumeq. unfolds L.eq_number. 
    destruct_hyp Hnumeq; simpls; repeat cases_if; rew_refl; auto; solve [false; auto].
    introv Heqtest.
    apply Hstx.
    eapply L.stx_eq_number. unfolds.
    simpl in Heqtest.
    repeat cases_if; rew_refl in *; auto.
    (* string *)
    simpls.
    cases_decide; fold_bool; rew_refl; auto.
    (* bool *) 
    simpls.
    repeat cases_if; fold_bool; rew_refl; auto.
    (* object *)
    simpls.
    cases_decide as Hd; fold_bool; rew_refl.
    eapply func_eq_1. 
    eapply state_invariant_rfun_obj; eauto.
    intro.
    injects.
    apply Hd.
    applys state_invariant_lfun_obj; eauto.
Qed.

Lemma strict_equality_test_lemma : forall BR jst st jv1 jv2 v1 v2,
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    decide (L.stx_eq v1 v2) = J.strict_equality_test jv1 jv2.
Proof.
    introv Hinv Hvrel1 Hvrel2.
    unfolds J.strict_equality_test.
    cases_if.
    (* same types *)
    eauto using equality_test_for_same_type_lemma.
    (* different types *)
    fold_bool. rew_refl.
    intro Hstx.
    inverts Hstx; inverts Hvrel1; inverts Hvrel2; auto.
Qed.

Lemma red_strict_equality_test_lemma : forall BR jst jv1 v1 jv2 v2 k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privStxEq [v1; v2]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    value_related BR jv2 v2 ->
    value_related BR jv1 v1 ->
    exists b, 
    b = J.strict_equality_test jv1 jv2 /\
    r = L.res_value (L.value_bool b) /\
    state_invariant BR jst st'.
Proof.
    introv Hlred Hinv Hvrel1 Hvrel2.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    applys strict_equality_test_lemma; eauto.
    reflexivity.
    assumption.
Qed.

Lemma red_expr_binary_op_strict_equal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_strict_equal je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th Heql : red_strict_equality_test_lemma.
    destruct_hyp Heql.
    jauto_js 12.
Qed.

Lemma red_expr_binary_op_strict_disequal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_strict_disequal je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th Heql : red_strict_equality_test_lemma.
    destruct_hyp Heql.
    repeat ljs_autoforward.
    jauto_js 12.
Qed.

(* TODO move *)
Lemma value_related_equality_test_same_type : forall BR jst st jtp jv1 jv2 v1 v2,
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    J.type_of jv1 = jtp ->
    J.type_of jv2 = jtp ->
    value_related BR 
        (J.value_prim (J.prim_bool (J.equality_test_for_same_type jtp jv1 jv2))) 
        (L.value_bool (decide (L.stx_eq v1 v2))).
Proof.
    introv Hinv Hvrel1 Hvrel2 Heq1 Heq2.
    erewrite equality_test_for_same_type_lemma; eauto_js.
Qed.

Hint Resolve value_related_equality_test_same_type : js_ljs.

(* TODO move *)

Ltac find_last_invariant_then T :=
    match goal with
    | H : state_invariant ?BR ?jst _ _ _ |- _ => T BR 
    end.

Ltac unfold_concl_tac_with BR :=
    match goal with
    | |- concl_expr_getvalue _ _ _ _ _ _ _ _ => unfolds; unfold_concl_tac_with BR 
    | |- concl_spec _ _ _ _ _ _ _ _ _ _ => 
        unfolds; exists BR 
    end.

Ltac unfold_concl_tac := find_last_invariant_then unfold_concl_tac_with.

(*
Tactic Notation "ljs_handle_abort_tac" integer(k) := 
    repeat (ljs_propagate_abort || ljs_abort_from_js); 
    unfold_concl_tac; solve [jauto_set; eauto k with js_ljs bag typeclass_instances].

Tactic Notation "ljs_handle_abort_tac" := ljs_handle_abort_tac 5.
*)
(* TODO move *)
Tactic Notation "determine_epsilon_binds" := 
    match goal with
    | H2 : context [ @epsilon _ _ (@binds ?a ?b ?t ?bb ?m ?k) ] |- _ => 
        let H1 := fresh "H" in
        forwards H1 : (@deterministic_epsilon _ _ (@binds a b t bb m k) _); [prove_bag 20 | idtac]; 
        rewrite H1 in H2; clear H1
    | |- context [ @epsilon _ _ (@binds ?a ?b ?t ?bb ?m ?k) ] => 
        let H1 := fresh "H" in
        forwards H1 : (@deterministic_epsilon _ _ (@binds a b t bb m k) _); [prove_bag 20 | idtac]; 
        rewrite H1; clear H1
    end. 

(* TODO move *)
Lemma js_equality_test_for_same_type_sym_eq : forall jtp jv1 jv2,
    J.type_of jv1 = jtp -> J.type_of jv2 = jtp ->
    J.equality_test_for_same_type jtp jv1 jv2 = J.equality_test_for_same_type jtp jv2 jv1.
Proof.
    introv Heq1 Heq2.
    destruct jtp; tryfalse; simpls; repeat cases_decide; try reflexivity.
    destruct jv1 as [p1|p1]; tryfalse; destruct jv2 as [p2|p2]; tryfalse.
    destruct p1; tryfalse; destruct p2; tryfalse.
    repeat cases_if; repeat cases_decide; substs; tryfalse; iauto.
Qed.

Lemma red_spec_equal_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privEqEq J.spec_equal
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat inv_top_fwd_ljs.
    repeat binds_inv.
    inv_ljs.
    (* same type *)
    repeat ljs_autoforward.
    fold_bool.
    rew_refl in H5. (* TODO *)
Admitted.
(*
    asserts Htpeq : (J.type_of jv1 = J.type_of jv2);
        [inverts Hvrel1; inverts Hvrel2; tryfalse; reflexivity | idtac].
    jauto_js.
    (* diff type *)

Ltac munch_elseif Hx :=
    inv_fwd_ljs;
    ljs_out_redh_ter;
    ljs_bool_red_exprh;
    repeat binds_inv;
    repeat determine_epsilon_binds;
    repeat determine_epsilon;
    cases_isTrue as Hx;
    inv_ljs; [idtac | let Hx1 := fresh Hx in rename Hx into Hx1; try munch_elseif Hx].

    munch_elseif Hx.

    (* undefined-null, null-undefined *)
    repeat ljs_autoforward;
    destruct Hx as [(Hx1&Hx2)|(Hx0&Hx1&Hx2)];
    repeat ljs_autoforward;
    inverts Hx1; inverts Hx2;
    inverts Hvrel1; tryfalse;
    inverts Hvrel2; tryfalse;
    jauto_js.
    (* number-string *)
    destruct Hx as (Hx1&Hx2);
    inverts Hx1; inverts Hx2;
    repeat ljs_autoforward. 
    inverts Hvrel1; tryfalse;
    inverts Hvrel2; tryfalse.
    
    unfold_concl.
    do 3 eexists. split.
    eauto_js 12.
    split. left. eauto_js.
    eauto_js 12.
    (* string-number *)
    destruct Hx as (HxA&HxB);
    inverts HxA; inverts HxB;
    repeat ljs_autoforward. 
    inverts Hvrel1; tryfalse;
    inverts Hvrel2; tryfalse.
    
    unfold_concl.
    do 3 eexists. split.
    eauto_js 12.
    split. left. eauto_js.

    rewrite js_equality_test_for_same_type_sym_eq by reflexivity.
    jauto_js. 
    (* left boolean *)
    inverts Hx; 
    repeat ljs_autoforward. 
    inverts Hvrel1; tryfalse.
    specializes IH H18. 
    omega.
    ljs_state_invariant.
    eauto_js. eauto_js.
    destr_concl. (* TODO handle abort *)

    unfold_concl.
    do 3 eexists. split. 
    eapply J.red_spec_equal. simpl. reflexivity. reflexivity.
    eapply J.red_spec_equal_1_diff_type. 
    do 5 cases_if_auto_js.
    reflexivity.
    eapply J.red_spec_equal_3_convert_and_recurse.
    eauto_js.
    eapply J.red_spec_equal_4_recurse.
    skip. skip. skip. (* symmetry, jscert problem *)
    (* right boolean *)
    inverts Hx; 
    repeat ljs_autoforward. 
    inverts Hvrel2; tryfalse.
    specializes IH H9. (* TODO *)
    omega. ljs_state_invariant. eauto_js. eauto_js.
    destr_concl. (* TODO ljs_handle_abort *)

    unfold_concl.
    do 3 eexists. split. 
    eapply J.red_spec_equal. simpl. reflexivity. reflexivity.
    eapply J.red_spec_equal_1_diff_type. 
    do 4 cases_if_auto_js. cases_if_auto_js. skip. (* TODO *) cases_if_auto_js.
    reflexivity.
    eapply J.red_spec_equal_3_convert_and_recurse.
    eauto_js.
    eapply J.red_spec_equal_4_recurse.
    eassumption.
    split. left.
    eauto_js 12.
    skip.  skip.
    (* (string|number)-object *)
    skip.
    (* object-(string|number) *)
    skip. 
    (* otherwise false *)
    repeat ljs_autoforward.
    skip.
Admitted.
*)

Lemma red_expr_binary_op_3_equal_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privEqEq (J.expr_binary_op_3 J.binary_op_equal)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    forwards_th : red_spec_equal_ok.
    destr_concl;
    jauto_js. 
Qed.

Lemma red_expr_binary_op_equal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_equal je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th : red_expr_binary_op_3_equal_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    jauto_js 8.
Qed.

Lemma red_expr_binary_op_disequal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_disequal je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th : red_spec_equal_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js 15. 
Qed.

Lemma red_expr_binary_op_and_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_and je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_boolean_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    destruct b; repeat ljs_autoforward.
    destr_concl.
    jauto_js 8. 
    jauto_js 9.
    exists BR'0. (* TODO *)
    jauto_js 8.
Qed.

Lemma red_expr_binary_op_or_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_or je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_boolean_unary_ok.
    destr_concl; try ljs_handle_abort. 
    res_related_invert.
    resvalue_related_invert.
    destruct b; repeat ljs_autoforward.
    exists BR'0. jauto_js 8. (* TODO *) 
    destr_concl. 
    jauto_js 8.
    jauto_js 9.
Qed.

(* TODO move *) 
Lemma puremath_op_regular : forall jop F, 
    J.puremath_op jop F ->
    J.regular_binary_op jop.
Proof.
    introv Hpure. destruct Hpure; simpl; trivial.
Qed.

Hint Resolve puremath_op_regular : js_ljs.

Lemma js_puremath_to_ljs : forall jop F,
    J.puremath_op jop F ->
    exists op,
    L.num_binary_op op F /\
    forall je1 je2,
    js_expr_to_ljs (J.expr_binary_op je1 jop je2) = 
        E.make_app_builtin "%PrimMultOp" [js_expr_to_ljs je1; js_expr_to_ljs je2; E.op2_func op].
Proof.
    introv Hpure.
    inverts Hpure; eexists; (splits; [idtac | jauto]).
    eapply L.num_binary_op_mul. 
    eapply L.num_binary_op_div.
    eapply L.num_binary_op_mod.
    eapply L.num_binary_op_sub.
Qed.

Lemma red_expr_binary_op_puremath : forall k je1 je2 jop F,
    J.puremath_op jop F ->
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 jop je2).
Proof.
    introv Hpure IHe Hcinv Hinv Hlred.
    forwards (op&Hnumop&Heq) : js_puremath_to_ljs Hpure.
    rewrite Heq in Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort. 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort. 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    inverts red_exprh H14. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    forwards_th Hx : eval_binary_op_num_lemma. eassumption. eassumption. 
    destruct_hyp Hx.
    jauto_js 18.
Qed.

(* TODO move to ljs *)
Lemma value_related_type_string_eq : forall BR jv v,
    value_related BR jv v ->
    (L.typeof v = "string") = (J.type_of jv = J.type_string).
Proof.
    introv Hvrel.
    rew_logic.
    split; intro; inverts Hvrel; tryfalse; reflexivity.
Qed.

Lemma value_related_to_num_append_lemma : forall BR jpr1 jpr2 v1 v2,
    value_related BR (J.value_prim jpr1) v1 ->
    value_related BR (J.value_prim jpr2) v2 ->
    value_related BR 
        (J.value_prim (J.prim_number
            (add (J.convert_prim_to_number jpr1) (J.convert_prim_to_number jpr2))))
        (L.value_number (add (L.value_to_num_cast v1) (L.value_to_num_cast v2))).
Proof.
    introv Hvrel1 Hvrel2.
    repeat erewrite convert_prim_to_number_lemma by eassumption.
    eauto_js.
Qed.

Hint Resolve value_related_to_num_append_lemma : js_ljs.

Lemma value_related_to_str_append_lemma : forall BR jpr1 jpr2 v1 v2,
    value_related BR (J.value_prim jpr1) v1 ->
    value_related BR (J.value_prim jpr2) v2 ->
    value_related BR 
        (J.value_prim (J.prim_string
            (J.convert_prim_to_string jpr1 ++ J.convert_prim_to_string jpr2)))
        (L.value_string (L.value_to_str_cast v1 ++ L.value_to_str_cast v2)).
Proof.
    introv Hvrel1 Hvrel2.
    repeat erewrite convert_prim_to_string_lemma by eassumption.
    eauto_js.
Qed.

Hint Resolve value_related_to_str_append_lemma : js_ljs.

Lemma red_expr_binary_op_add : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_add je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok_default.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok_default.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    repeat js_post_to_primitive.
    inv_ljs; cases_decide. {
        repeat ljs_autoforward.
        erewrite value_related_type_string_eq in * by eassumption.
        jauto_js 20.
    } 
    repeat ljs_autoforward.
    inv_ljs; cases_decide. {
        repeat ljs_autoforward.
        erewrite value_related_type_string_eq in * by eassumption.
        jauto_js 20.
    }
    repeat ljs_autoforward.
    erewrite value_related_type_string_eq in * by eassumption.
    jauto_js 20.
Qed.

(* TODO move *) 
Lemma inequality_op_regular : forall jop b1 b2, 
    J.inequality_op jop b1 b2 ->
    J.regular_binary_op jop.
Proof.
    introv Hop. destruct Hop; simpl; trivial.
Qed.

Hint Resolve inequality_op_regular : js_ljs.

Lemma js_inequality_to_ljs : forall jop b1 b2 je1 je2,
    J.inequality_op jop b1 b2 ->
    js_expr_to_ljs (J.expr_binary_op je1 jop je2) = 
        E.make_app_builtin "%CompareOp" [js_expr_to_ljs je1; js_expr_to_ljs je2; L.expr_bool b1; L.expr_bool b2].
Proof.
    introv Hop.
    inverts Hop; reflexivity.
Qed.

Inductive inequality_result_related : J.prim -> L.value -> Prop :=
| inequality_result_related_bool : forall b, inequality_result_related (J.prim_bool b) (L.value_bool b)
| inequality_result_related_undefined : inequality_result_related J.prim_undef L.value_undefined
.

Hint Constructors inequality_result_related : js_ljs.

Hint Constructors L.same_value : js_ljs. (* TODO move *)

Lemma same_value_eq_lemma : forall v1 v2, L.value_type v1 <> L.type_closure -> L.same_value v1 v2 = (v1 = v2).
Proof.
    introv Htype.
    rew_logic.
    split.
    introv Hsv. inverts Hsv; reflexivity.
    introv Heq. subst. destruct v2; simpls; tryfalse; eauto_js.
Qed.

Lemma value_number_eq_lemma : forall n1 n2, (L.value_number n1 = L.value_number n2) = (n1 = n2).
Proof.
    introv.
    rew_logic.
    split.
    introv Hx. injects. reflexivity.
    introv Hx. substs. reflexivity.
Qed.

(* TODO move *)
Ltac munch_elseif Hx :=
    inv_fwd_ljs;
    ljs_out_redh_ter;
    ljs_bool_red_exprh;
    repeat binds_inv;
    repeat determine_epsilon_binds;
    repeat determine_epsilon;
    repeat binds_determine;
    cases_isTrue as Hx;
    repeat rewrite same_value_eq_lemma in Hx by solve [auto];
    repeat rewrite value_number_eq_lemma in Hx;
    inv_ljs; [idtac | let Hx1 := fresh Hx in rename Hx into Hx1; try munch_elseif Hx].

Lemma inequality_test_number_lemma : forall k c st st' r n1 n2,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privNumberCompareOp [L.value_number n1; L.value_number n2]) (L.out_ter st' r) ->
    exists v jpr,
    J.inequality_test_number n1 n2 = jpr /\
    inequality_result_related jpr v /\
    st' = st /\ r = L.res_value v.
Proof.
    introv Hlred.
    inverts red_exprh Hlred.
    ljs_apply.

    munch_elseif Hcond;
    unfolds J.inequality_test_number. { (* one is NaN *)
        repeat ljs_autoforward.
        destruct_hyp Hcond;
        cases_if; try solve [false; auto];
        jauto_js.
    } { (* are equal *)
        repeat ljs_autoforward.
        subst_hyp Hcond.
        cases_if; try solve [false; iauto].
        cases_if.
        jauto_js. 
    } {
        skip.
    }
Admitted. (* TODO *)

Lemma inequality_test_primitive_lemma : forall k BR1 BR2 c st st' r v1 v2 jpr1 jpr2,
    value_related BR1 (J.value_prim jpr1) v1 ->
    value_related BR2 (J.value_prim jpr2) v2 ->
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privPrimitiveCompareOp [v1; v2]) (L.out_ter st' r) ->
    exists v jpr,
    J.inequality_test_primitive jpr1 jpr2 = jpr /\
    inequality_result_related jpr v /\
    st' = st /\ r = L.res_value v.
Proof.
    introv Hvrel1 Hvrel2 Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
Admitted. (* TODO *)

Lemma red_expr_binary_op_inequality : forall k je1 je2 jop b1 b2,
    J.inequality_op jop b1 b2 ->
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 jop je2).
Proof.
    introv Hop IHe Hcinv Hinv Hlred.
    erewrite js_inequality_to_ljs in * by eassumption.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok_default.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok_default.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat js_post_to_primitive.
    repeat ljs_autoforward.

    destruct b1. {
        repeat ljs_autoforward.
        forwards_th Hineq : inequality_test_primitive_lemma.
        destruct_hyp Hineq.
        repeat ljs_autoforward.
        cases_decide as Hund. {
            inverts Hund.
            inverts Hineq0 as Hundef.
            repeat ljs_autoforward.
            jauto_js 15.
        }
        repeat ljs_autoforward.
        inverts Hineq0; try solve [false; eauto_js].
        destruct b2. {
            repeat ljs_autoforward.
            destruct b0; jauto_js 15.
        } {
            repeat ljs_autoforward.
            destruct b; jauto_js 15.
        }
    } { (* copy-pasted :( *)
        repeat ljs_autoforward.
        forwards_th Hineq : inequality_test_primitive_lemma.
        destruct_hyp Hineq.
        repeat ljs_autoforward.
        cases_decide as Hund. {
            inverts Hund.
            inverts Hineq0 as Hundef.
            repeat ljs_autoforward.
            jauto_js 15.
        }
        repeat ljs_autoforward.
        inverts Hineq0; try solve [false; eauto_js].
        destruct b2. {
            repeat ljs_autoforward.
            destruct b0; jauto_js 15.
        } {
            repeat ljs_autoforward.
            destruct b; jauto_js 15.
        }
    }
Qed.

Lemma red_expr_binary_op_coma_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_coma je2).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl. 
    jauto_js 8. 
    jauto_js 8.
Qed.

Lemma red_expr_binary_op_ok : forall op k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 op je2).
Proof.
    destruct op; introv.
    applys red_expr_binary_op_puremath J.puremath_op_mult.
    applys red_expr_binary_op_puremath J.puremath_op_div.
    applys red_expr_binary_op_puremath J.puremath_op_mod.
    applys red_expr_binary_op_add.
    applys red_expr_binary_op_puremath J.puremath_op_sub.
    skip.
    skip.
    skip.
    applys red_expr_binary_op_inequality J.inequality_op_lt.
    applys red_expr_binary_op_inequality J.inequality_op_gt.
    applys red_expr_binary_op_inequality J.inequality_op_le.
    applys red_expr_binary_op_inequality J.inequality_op_ge.
    skip.
    skip.
    apply red_expr_binary_op_equal_ok.
    apply red_expr_binary_op_disequal_ok.
    apply red_expr_binary_op_strict_equal_ok.
    apply red_expr_binary_op_strict_disequal_ok.
    skip.
    skip.
    skip.
    apply red_expr_binary_op_and_ok.
    apply red_expr_binary_op_or_ok.
    apply red_expr_binary_op_coma_ok.
Qed.
