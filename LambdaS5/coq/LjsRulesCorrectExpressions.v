Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Import LjsRulesCorrectSpecFuns.
Require Import LjsRulesCorrectConstruct.
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

(** *** Objects *)

Lemma red_expr_object_ok : forall k l,
    th_expr k (J.expr_object l).
Proof.
    introv Hcinv Hinv Hlred.
    repeat ljs_autoforward.
Admitted.

(** *** Functions *)

Lemma red_expr_nonrec_function_ok : forall k is fb,
    th_expr k (J.expr_function None is fb).
Proof.
    introv Hcinv Hinv Hlred.
    destruct fb.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th Hx : red_spec_creating_function_object_ok.
        { applys* usercode_context_invariant_lexical_env_lemma. }
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    jauto_js 12.
Qed.

Hint Extern 1 (J.red_expr _ _ (J.expr_function_1 _ _ _ _ _ _) _) => eapply J.red_expr_function_named_1 : js_ljs.

Opaque fresh. 

Lemma red_expr_rec_function_ok : forall k s is fb,
    th_expr k (J.expr_function (Some s) is fb).
Proof.
    introv Hcinv Hinv Hlred.
    destruct fb.
    repeat ljs_autoforward.
    lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
        eassumption.
    forwards_th Hx : only_state_invariant_new_env_record_decl_lemma; try eassumption.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th Hx : create_immutable_binding_lemma. prove_bag.
    destr_concl; try solve [progress repeat (ljs_propagate_abort || ljs_abort_from_js); jauto_js 10]. (* TODO *)
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_creating_function_object_ok. {
        constructor.
        + destruct Hcinv. eauto_js.
        + introv Hbinds. binds_inv.
          eapply lexical_env_related_cons. eauto_js. eauto_js.
          eapply execution_ctx_related_lexical_env; try eassumption. eapply context_invariant_execution_ctx_related.
          eauto_js.
        + introv Hbinds. binds_inv. reflexivity.
        + lets Hee : context_invariant_env_records_exist Hcinv. destruct Hee.
          introv Hmem. inverts Hmem as Hmem. eauto_js 8. 
          unfolds env_records_exist_env. apply env_record_exist_lexical_env in Hmem.
          destruct Hmem. eauto_js.
        + eauto_js.
    }
    destr_concl; try solve [progress repeat (ljs_propagate_abort || ljs_abort_from_js); jauto_js 10]. (* TODO *)
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : initialize_immutable_binding_lemma. (* TODO *) prove_bag 8.
    destr_concl; try solve [progress repeat (ljs_propagate_abort || ljs_abort_from_js); jauto_js 11]. (* TODO *)
    res_related_invert.
    repeat ljs_autoforward.
    jauto_js 11.
Qed.

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

(* TODO move *)
Parameter string_of_nat_injection_lemma : forall k1 k2, string_of_nat k1 = string_of_nat k2 -> k1 = k2. (* TODO *)

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
            lets Hx : iarray_has_args Hnth. 
            asserts Hdiff : (string_of_nat k <> string_of_nat (length vl)). {
                introv Heq. apply string_of_nat_injection_lemma in Heq. math.
            }
            prove_bag.
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
    ~L.is_object v ->
    value_related BR jv v ->
    J.type_of jv <> J.type_object.
Proof.
    introv Hnobj Hrel Hjobj.
    destruct Hrel; tryfalse.
    apply Hnobj. constructor.
Qed.

Hint Extern 10 (J.type_of _ <> J.type_object) => 
    match goal with
    | H : ~L.is_object _ |- _ => applys not_object_hint H
    end : js_ljs.

Lemma red_expr_new_ok : forall k je jel,
    ih_expr k ->
    ih_stat k ->
    ih_call k ->
    th_expr k (J.expr_new je jel).
Proof.
    introv IHe IHt IHc HCinv Hinv Hlred.
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
        inverts IH5. (* TODO *)
        rewrite index_binds_eq in H7. destruct H7 as (?x&H7). (* TODO *)
        forwards Hc : construct_related_lemma; try eassumption. prove_bag.
        destruct_hyp Hc.
        forwards Hx : object_method_construct_lemma; try eassumption. prove_bag. eauto_js.
        forwards_th : red_spec_construct_ok; try eassumption. prove_bag. (* TODO *)
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 12.
    } { 
        inverts IH5. (* TODO *)
        forwards Hx : object_method_construct_lemma; try eassumption; try eauto_js.
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

Hint Extern 3 (J.red_expr _ _ (J.expr_access_3 _ _ _) _) => eapply J.red_expr_access_3 : js_ljs. (* TODO *)

Hint Extern 3 (js_object_coercible ?jv) => not is_evar jv; unfolds : js_ljs.

Lemma check_object_coercible_lemma : forall BR k jst jc c st st' r v1 jv1, (* TODO factorize to new th_ *)
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 -> 
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privCheckObjectCoercible [v1]) (L.out_ter st' r) ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_check_object_coercible jv1) 
        (fun jrv => jrv = J.resvalue_empty /\ js_object_coercible jv1).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    cases_decide as Heq1; rewrite stx_eq_undefined_eq_lemma in Heq1. { (* undefined *)
        subst_hyp Heq1.
        inverts Hvrel.
        repeat ljs_autoforward.
        forwards_th : type_error_lemma. eauto.
        destr_concl; tryfalse.
        ljs_handle_abort.
    }
    repeat ljs_autoforward.
    cases_decide as Heq2; rewrite stx_eq_null_eq_lemma in Heq2. { (* null *)
        subst_hyp Heq2.
        inverts Hvrel.
        repeat ljs_autoforward.
        forwards_th : type_error_lemma. eauto.
        destr_concl; tryfalse.
        ljs_handle_abort.
    }
    repeat ljs_autoforward.
    inverts Hvrel; tryfalse;
    jauto_js 10.
Qed.

Lemma ref_is_property_object_coercible_hint : forall jref jv,
    J.ref_base jref = J.ref_base_type_value jv ->
    js_object_coercible jv ->
    J.ref_is_property jref.
Proof.
    introv Heq Hoc.
    destruct jref. simpls. substs.
    destruct Hoc as (Hoc1&Hoc2).
    destruct jv as [()|]; tryfalse; unfolds; unfolds J.ref_kind_of; simpl; iauto.
Qed.

Hint Resolve ref_is_property_object_coercible_hint : js_ljs.

Lemma field_access_lemma : forall BR k jst jc c st st' r je ee1 ee2 s0,
    ih_call k ->
    ih_expr k ->
    L.red_exprh k c st (L.expr_basic (E.make_app_builtin "%PropertyAccess" 
        [L.expr_id s0; E.ejs_to_ljs ee1; E.ejs_to_ljs ee2; L.expr_id "$strict"])) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    js_field_access je ee1 ee2 ->
    exists BR' jst'' jr,
    J.red_expr jst jc (J.expr_basic je) (J.out_ter jst'' jr) /\
    ((exists jv s c' k' v1 v2 st'', 
      jr = J.res_ref (J.ref_intro (J.ref_base_type_value jv) s (J.execution_ctx_strict jc)) /\
      binds c s0 v1 /\
      L.red_exprh k' c' st''
          (L.expr_app_2 v1 [v2; L.value_string s; L.value_bool (J.execution_ctx_strict jc)])
          (L.out_ter st' r) /\
      state_invariant BR' jst'' st'' /\
      value_related BR' jv v2 /\
      js_object_coercible jv /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k) \/
      J.abort (J.out_ter jst'' jr) /\ J.res_type jr = J.restype_throw /\ 
      state_invariant BR' jst'' st' /\
      res_related BR' jst'' st' jr r /\ BR \c BR').
Proof.
    introv IHc IHe Hlred Hcinv Hinv Hfa.
        inverts Hfa. { (* access *)
            repeat ljs_autoforward.
            destr_concl; try ljs_handle_abort.
            repeat ljs_autoforward.
            destr_concl; try ljs_handle_abort.
            repeat ljs_autoforward.
            lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
                eassumption.
            subst_hyp Hstrict.
            ljs_invert_apply.
            repeat ljs_autoforward.
            forwards_th : check_object_coercible_lemma.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            repeat ljs_autoforward.
            forwards_th : red_spec_to_string_unary_ok.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_invert.
            repeat ljs_autoforward.
            jauto_js 25.
        } { (* member *)
            repeat ljs_autoforward.
            destr_concl; try ljs_handle_abort.
            repeat ljs_autoforward.
            lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
                eassumption.
            subst_hyp Hstrict.
            ljs_invert_apply.
            repeat ljs_autoforward.
            forwards_th : check_object_coercible_lemma.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            repeat ljs_autoforward.
            forwards_th : red_spec_to_string_unary_ok.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_invert.
            repeat ljs_autoforward.
            jauto_js 25.
         }
Qed.

(* TODO why get_value is an ext_spec, and put_value is ext_expr? *)
Lemma prop_get_value_lemma : forall BR k jst jc c st st' r jv v s b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetField
           [v; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    js_object_coercible jv ->
    concl_spec BR jst jc c st st' r
        (J.spec_get_value (J.resvalue_ref (J.ref_intro (J.ref_base_type_value jv) s b)))
        (fun BR' _ jv =>
            exists v', r = L.res_value v' /\ value_related BR' jv v' ).
Proof.
    introv IHe Hlred Hcinv Hinv Hvrel Hoc.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq. { (* object *)
        inverts Hvrel; tryfalse.
        repeat ljs_autoforward.
        forwards_th : get_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    } { (* primitive value *)
        asserts Hpb : (J.ref_has_primitive_base (J.ref_intro (J.ref_base_type_value jv) s b)). {
            inverts Hoc; inverts Hvrel; tryfalse; try solve [false; apply Heq; reflexivity]; reflexivity.
        }
        repeat ljs_autoforward.
        forwards_th : get_prim_lemma.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 15.
    }
Qed.

(* TODO move *)
Lemma js_reference_type_object_hint : forall je ee1 ee2 jv,
    js_field_access je ee1 ee2 ->
    js_object_coercible jv ->
    js_reference_type je (J.ref_base_type_value jv).
Proof.
    introv Hfa Hoc.
    inverts Hfa; inverts Hoc; eauto_js.
Qed.

Hint Extern 3 (js_reference_type _ _) => eapply js_reference_type_object_hint : js_ljs. (* TODO *)

Lemma red_expr_access_generic_ok : forall BR k jst jc c st st' r ee1 ee2 je,
    ih_expr k ->
    ih_call k ->
    L.red_exprh k c st (L.expr_basic
        (E.ejs_to_ljs (E.expr_get_field ee1 ee2))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    js_field_access je ee1 ee2 ->
    concl_expr_getvalue BR jst jc c st st' r je.
Proof.
    introv IHe IHc Hlred Hcinv Hinv Hfa.
    forwards_th Hx : field_access_lemma. eassumption. 
    destruct_hyp Hx; try ljs_handle_abort.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : prop_get_value_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js 10.
Qed.

Lemma red_expr_member_ok : forall k je s,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_member je s).
Proof.
    introv IHe IHc Hcinv Hinv Hlred.
    applys red_expr_access_generic_ok IHe IHc Hlred; try eassumption. eapply js_field_access_member.
Qed.

Lemma red_expr_access_ok : forall k je1 je2,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_access je1 je2).
Proof.
    introv IHe IHc Hcinv Hinv Hlred.
    applys red_expr_access_generic_ok IHe IHc Hlred; try eassumption. eapply js_field_access_access.
Qed.

Lemma implicit_this_lemma : forall BR k jst jc c st st' r jeptr ptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvImplicitThis [L.value_object ptr]) (L.out_ter st' r) ->
    fact_js_env jeptr ptr \in BR ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value_gen BR jst jc c st st' r (J.spec_env_record_implicit_this_value jeptr) 
        (fun BR' jst' _ => BR' = BR /\ jst' = jst) False.
Proof.
    introv Hlred Hlrel Hcinv Hinv.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma Hinv Hlrel. eassumption.
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

Lemma is_syntactic_eval_reference_producing_lemma : forall je,
    J.is_syntactic_eval je -> js_reference_producing je.
Proof.
    introv Hse. 
    destruct je; tryfalse. eauto_js.
Qed.

(* TODO should not be needed *)
Hint Extern 3 (J.red_expr _ _ (J.expr_call_1 _ _ _) _) => eapply J.red_expr_call_1 : js_ljs.

Lemma red_expr_call_ok : forall k je jel,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_call je jel).
Proof.
    introv IHe IHc Hcinv Hinv Hlred. 
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_app.
    reference_match_cases Hlred Hx Heq Hrp. 
    {
        repeat ljs_autoforward.
        ljs_invert_apply.
        do 2 ljs_autoforward.
        forwards_th Hx : field_access_lemma. eassumption. 
        destruct_hyp Hx; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : prop_get_value_lemma. assumption.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        forwards_th : red_spec_list_ok.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th Hx : is_callable_lemma.
        destruct_hyp Hx.
        cases_isTrue as Hic. { (* is callable *)
            repeat ljs_autoforward.
            lets (jptr&Heqc) : is_callable_obj Hic. subst_hyp Heqc.
            inverts H12. (* TODO *) (* inverting value_related *)
            asserts Hseval : (!J.is_syntactic_eval je). {
                rew_refl. inverts Heq; eauto_js.
            }
            apply_ih_call. eauto_js.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 15.
        } { (* not callable *)
            repeat ljs_autoforward.
            forwards_th : type_error_lemma. eauto.
            destr_concl; tryfalse; try ljs_handle_abort.
        }
    } {
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward. 
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        subst_hyp Hstrict.
        forwards_th Hx : env_get_value_lemma. eauto_js. eassumption.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        forwards_th : red_spec_list_ok.
        destr_concl; try ljs_handle_abort.
(* TODO place for better boolean condition handling  *)
        do 2 inv_top_fwd_ljs.
        ljs_out_redh_ter.
        ljs_bool_red_exprh; repeat determine_epsilon.
        cases_isTrue as Hevcond. { (* eval *)
            destruct Hevcond as (Hevcond1&Hevcond2).
            specializes H32 Hevcond1. destruct_hyp H32. repeat determine_epsilon. (* TODO better! *)
            repeat ljs_autoforward.
            skip. (* TODO prove eval *)
        } 
        rew_logic in Hevcond.
        repeat ljs_autoforward.
        forwards_th Hx : is_callable_lemma.
        destruct_hyp Hx.
        cases_isTrue as Hic. { (* is callable *)
            lets (jptr&Heq) : is_callable_obj Hic. subst_hyp Heq.
            repeat ljs_autoforward.
            ref_base_type_var_invert; tryfalse.
            forwards_th Hx : implicit_this_lemma. prove_bag.
            destr_concl; tryfalse.
            res_related_invert.
            resvalue_related_only_invert.
            repeat ljs_autoforward.
            inverts keep Hx11. (* TODO *)
            inverts keep Hx12. (* TODO *)
            asserts Hseval : (jptr <> J.object_loc_prealloc J.prealloc_global_eval \/ 
                    !J.is_syntactic_eval (J.expr_identifier s)). {
                apply case_classic_l in Hevcond.
                destruct Hevcond as [Hevcond|Hevcond]. { (* var is not named eval *)
                    right. rew_refl. intro Heval. simpl in Heval.
                    rewrite stx_eq_string_eq_lemma in Hevcond.
                    cases_decide.
                } { (* var is named eval, but does not refer to eval *)
                    left.
                    rew_logic in Hevcond.
                    destruct Hevcond as (Hevcond1&Hevcond2).
                    specializes H32 Hevcond1. destruct_hyp H32. repeat determine_epsilon. (* TODO *)
                    repeat binds_inv.
                    introv Heqeval. subst_hyp Heqeval.
                    apply Hevcond2.
                    unfolds LjsInitEnv.priveval. rewrite stx_eq_object_eq_lemma.
                    lets Hfact : context_invariant_prealloc_lemma Hcinv prealloc_related_global_eval.
                    determine_fact_js_obj.
                    reflexivity.
                }
            }
            apply_ih_call.
            destr_concl; try ljs_handle_abort. 
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 15.
        } { (* not callable *)
            repeat ljs_autoforward.
            forwards_th : type_error_lemma. eauto.
            destr_concl; tryfalse; try ljs_handle_abort.
        }
    } {
        repeat ljs_autoforward.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        do 5 inv_top_fwd_ljs.
        ljs_out_redh_ter.
        forwards_th : red_spec_list_ok.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th Hx : is_callable_lemma.
        destruct_hyp Hx.
        cases_isTrue as Hic. { (* is callable *)
            repeat ljs_autoforward.
            lets (jptr&Heq) : is_callable_obj Hic. subst_hyp Heq.
            inverts IH5. (* TODO *)
            apply_ih_call.
            asserts Hseval : (!J.is_syntactic_eval je). {
                rew_refl.
                eauto using is_syntactic_eval_reference_producing_lemma.
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
    ih_call k ->
    th_expr k (J.expr_identifier i).
Proof.
    introv IHc Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
        eassumption.
    forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
    destruct_hyp Hx; try ljs_handle_abort.
    ljs_invert_apply.
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

(* TODO move *)
Lemma prop_put_value_lemma : forall BR k jst jc c st st' r jv v jv' v' s b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privSetField
        [v; L.value_string s; v'; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    js_object_coercible jv ->
    value_related BR jv' v' ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_put_value (J.resvalue_ref (J.ref_intro (J.ref_base_type_value jv) s b)) jv') 
            (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrel Hoc Hvrel'.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq. { (* object *)
        inverts Hvrel; tryfalse.
        repeat ljs_autoforward.
        forwards_th : put_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        jauto_js 10.
    } { (* primitive value *)
        asserts Hpb : (J.ref_has_primitive_base (J.ref_intro (J.ref_base_type_value jv) s b)). {
            inverts Hoc; inverts Hvrel; tryfalse; try solve [false; apply Heq; reflexivity]; reflexivity.
        }
        repeat ljs_autoforward.
        forwards_th : put_prim_lemma.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 15.
    }
Qed.

Lemma red_expr_unary_op_prepost_ok : forall k op F b je,
    J.prepost_op op F b ->
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    introv Hop IHe IHc Hcinv Hinv Hlred.
    lets (lop&F'&Hlop&Feq&Heq) : prepost_op_to_ljs_lemma Hop.
    rewrite Heq in Hlred. clear Heq.
    subst_hyp Feq.
    unfolds E.make_xfix.
    reference_match_cases Hlred Hx Heq Hrp. { (* ++ on objects *)
        repeat ljs_autoforward.
        ljs_invert_apply.
        do 2 ljs_autoforward. (* TODO stopping condition *)
        forwards_th Hx : field_access_lemma. eassumption.
        destruct_hyp Hx; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : prop_get_value_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        forwards_th : red_spec_to_number_unary_ok.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards Hveq : eval_binary_op_num_lemma; try eassumption.
        subst_hyp Hveq.
        forwards_th : prop_put_value_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct b; repeat ljs_autoforward; jauto_js 15.
    } { (* ++ on variables *)
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
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
        ljs_invert_apply.
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
    ljs_invert_apply.
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
    ih_call k ->
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryPlus (J.expr_unary_op_2 J.unary_op_add)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHc IHe Hcinv Hinv Hvrel Hlred.
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
    ih_call k ->
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_add je).
Proof.
    introv IHk IHe Hcinv Hinv Hlred.
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
    ih_call k ->
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryNeg (J.expr_unary_op_2 J.unary_op_neg)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHk IHe Hcinv Hinv Hvrel Hlred.
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
    ih_call k ->
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_neg je).
Proof.
    introv IHk IHe Hcinv Hinv Hlred.
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

(* TODO move to specfuns *)
Lemma red_spec_to_int32_ok : forall k,
    ih_call k ->
    forall BR jst jc c st st' r jv v, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privToInt32 [v]) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r (J.spec_to_int32 jv) 
        (fun BR' jst' a => r = L.res_value (L.value_int a)).
Proof.
    introv IHc Hcinv Hinv Hvrel Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_number_unary_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma red_expr_unary_op_bitwise_not_ok : forall k je,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_unary_op J.unary_op_bitwise_not je).
Proof.
    introv IHe IHc Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_int32_ok.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    jauto_js 10.
Qed.

Lemma red_expr_unary_op_typeof_ok : forall k je,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_unary_op J.unary_op_typeof je).
Proof.
    introv IHe IHc Hcinv Hinv Hlred.
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
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
        ref_base_type_var_invert. {
            repeat ljs_autoforward.
            jauto_js 10.
        }
        repeat ljs_autoforward.
        forwards Hx : execution_ctx_related_strictness_flag; try eassumption.
        { eapply context_invariant_execution_ctx_related. eassumption. }
        subst_hyp Hx.
        forwards_th : get_binding_value_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th Hx : typeof_lemma.
        destruct_hyp Hx.
        jauto_js 15.
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
    jmut <> J.mutability_deletable -> 
    mutability_configurable jmut = false.
Proof.
    introv Hx.
    destruct jmut; tryfalse; try reflexivity.
Qed.

Lemma red_expr_unary_op_delete_ok : forall k je,
    ih_call k ->
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_delete je).
Proof.
    introv IHk IHe Hcinv Hinv Hlred.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_delete.
    reference_match_cases Hlred Hx Heq Hrp. {
        forwards_th Hx : field_access_lemma. eassumption.
        destruct_hyp Hx; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : red_spec_to_object_ok.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        repeat ljs_autoforward.
        forwards_th : delete_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js 20.
    } {
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
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
                destruct obj.
                jauto_js 10.
            } {
                rewrite mutability_not_deletable_lemma in H16 by eassumption.
                repeat ljs_autoforward.
                jauto_js 15.
            }
        } { (* object records *)
            inverts Herel.
            unfolds L.object_class.
            cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
            repeat ljs_autoforward.
            cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
            repeat ljs_autoforward.
            forwards_th : delete_lemma. eassumption.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_invert.
            jauto_js 15.
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
    ih_call k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    destruct op; introv IHe IHc.
    applys~ red_expr_unary_op_delete_ok. 
    applys~ red_expr_unary_op_void_ok.
    applys~ red_expr_unary_op_typeof_ok.
    applys~ red_expr_unary_op_prepost_ok J.prepost_op_post_incr.
    applys~ red_expr_unary_op_prepost_ok J.prepost_op_post_decr.
    applys~ red_expr_unary_op_prepost_ok J.prepost_op_pre_incr.
    applys~ red_expr_unary_op_prepost_ok J.prepost_op_pre_decr.
    applys~ red_expr_unary_op_add_ok.
    applys~ red_expr_unary_op_neg_ok.
    applys~ red_expr_unary_op_bitwise_not_ok.
    applys~ red_expr_unary_op_not_ok.
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

Inductive regular_binary_op_impl : J.binary_op -> L.value -> Prop :=
| regular_binary_op_impl_coma : regular_binary_op_impl J.binary_op_coma LjsInitEnv.privPrimComma
| regular_binary_op_impl_add : regular_binary_op_impl J.binary_op_add LjsInitEnv.privPrimAdd
| regular_binary_op_impl_sub : regular_binary_op_impl J.binary_op_sub LjsInitEnv.privPrimSub
| regular_binary_op_impl_mult : regular_binary_op_impl J.binary_op_mult LjsInitEnv.privPrimMult
| regular_binary_op_impl_div : regular_binary_op_impl J.binary_op_div LjsInitEnv.privPrimDiv
| regular_binary_op_impl_mod : regular_binary_op_impl J.binary_op_mod LjsInitEnv.privPrimMod
| regular_binary_op_impl_bitwise_and : regular_binary_op_impl J.binary_op_bitwise_and LjsInitEnv.privBitwiseAnd
| regular_binary_op_impl_bitwise_or : regular_binary_op_impl J.binary_op_bitwise_or LjsInitEnv.privBitwiseOr
| regular_binary_op_impl_bitwise_xor : regular_binary_op_impl J.binary_op_bitwise_xor LjsInitEnv.privBitwiseXor
| regular_binary_op_impl_left_shift : regular_binary_op_impl J.binary_op_left_shift LjsInitEnv.privLeftShift
| regular_binary_op_impl_right_shift : 
    regular_binary_op_impl J.binary_op_right_shift LjsInitEnv.privSignedRightShift
| regular_binary_op_impl_unsigned_right_shift : 
    regular_binary_op_impl J.binary_op_unsigned_right_shift LjsInitEnv.privUnsignedRightShift
| regular_binary_op_impl_lt : regular_binary_op_impl J.binary_op_lt LjsInitEnv.privLtOp
| regular_binary_op_impl_le : regular_binary_op_impl J.binary_op_le LjsInitEnv.privLeOp
| regular_binary_op_impl_gt : regular_binary_op_impl J.binary_op_gt LjsInitEnv.privGtOp
| regular_binary_op_impl_ge : regular_binary_op_impl J.binary_op_ge LjsInitEnv.privGeOp
| regular_binary_op_impl_instanceof : regular_binary_op_impl J.binary_op_instanceof LjsInitEnv.privinstanceof
| regular_binary_op_impl_in : regular_binary_op_impl J.binary_op_in LjsInitEnv.privin
| regular_binary_op_impl_equal : regular_binary_op_impl J.binary_op_equal LjsInitEnv.privEqEq
| regular_binary_op_impl_strict_equal : regular_binary_op_impl J.binary_op_strict_equal LjsInitEnv.privStxEq
| regular_binary_op_impl_disequal : regular_binary_op_impl J.binary_op_disequal LjsInitEnv.privnotEqEq
| regular_binary_op_impl_strict_disequal : 
    regular_binary_op_impl J.binary_op_strict_disequal LjsInitEnv.privnotStxEq
.

Hint Constructors regular_binary_op_impl : js_ljs.

Lemma regular_binary_op_hint : forall op v,
    regular_binary_op_impl op v ->
    J.regular_binary_op op.
Proof.
    introv Hop. inverts Hop; eauto_js.
Qed.

Hint Resolve regular_binary_op_hint : js_ljs.

Lemma make_op2_red_expr_lemma : forall op e1 e2 v,
    regular_binary_op_impl op v ->
    exists s,
    E.make_op2 op e1 e2 = E.make_app_builtin s [e1; e2] /\
    forall BR jc c v',
    context_invariant BR jc c ->
    binds c s v' ->
    v' = v.
Proof.
    introv Hop.
    destruct Hop;
    eexists; (
    split; [reflexivity | 
    introv Hcinv Hbinds; ljs_get_builtin; reflexivity]).
Qed.

Lemma red_expr_regular_binary_op_ok : forall k je1 je2 op v,
    regular_binary_op_impl op v ->
    th_ext_expr_binary k v (J.expr_binary_op_3 op) (fun _ => True) ->
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 op je2).
Proof.
    introv Hrop Hth IHe Hcinv Hinv Hlred.
    lets (s&Heq&Hbuiltin) : make_op2_red_expr_lemma Hrop.
    unfolds js_expr_to_ljs. simpl in Hlred.
    rewrite Heq in Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    specializes Hbuiltin ___; try eassumption. subst_hyp Hbuiltin.
    eapply L.red_exprh_lt in H7. (* TODO *)
    forwards_th : Hth.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    jauto_js 12.
    math. (* TODO *)
Qed.

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

Lemma red_expr_binary_op_3_strict_equal_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privStxEq (J.expr_binary_op_3 J.binary_op_strict_equal) (fun _ => True).
Proof.
    introv Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    forwards_th Heql : red_strict_equality_test_lemma.
    destruct_hyp Heql.
    jauto_js 12.
Qed.

Lemma red_expr_binary_op_3_strict_disequal_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privnotStxEq (J.expr_binary_op_3 J.binary_op_strict_disequal) (fun _ => True).
Proof.
    introv Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
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
    repeat ljs_op_inv;
    cases_isTrue as Hx;
    repeat rewrite same_value_eq_lemma in Hx by solve [auto];
    repeat rewrite value_number_eq_lemma in Hx;
    inv_ljs.

Lemma red_spec_equal_ok : forall k,
    ih_call k ->
    th_ext_expr_binary k LjsInitEnv.privEqEq J.spec_equal
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    ljs_invert_apply.
    repeat inv_top_fwd_ljs.
    repeat ljs_op_inv.
    repeat binds_inv.
    cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq. { (* same type *)
        repeat ljs_autoforward.
        asserts Htpeq : (J.type_of jv1 = J.type_of jv2);
            [inverts Hvrel1; inverts Hvrel2; tryfalse; reflexivity | idtac].
        jauto_js.
    }
    (* diff type *)
    inv_fwd_ljs.
    munch_elseif Hx1; repeat rewrite stx_eq_string_eq_lemma in Hx1. { (* undefined-null, null-undefined *)
        destruct_hyp Hx1; repeat ljs_autoforward;
        inverts Hvrel1; tryfalse;
        inverts Hvrel2; tryfalse;
        jauto_js.
    }
    asserts : (~(J.type_of jv1 = J.type_null /\ J.type_of jv2 = J.type_undef) /\
               ~(J.type_of jv1 = J.type_undef /\ J.type_of jv2 = J.type_null)). {
        rew_logic in Hx1. rew_logic. destruct_hyp Hx1; tryfalse;
        inverts Hvrel1; auto; inverts Hvrel2; auto.
    }
    munch_elseif Hx2; repeat rewrite stx_eq_string_eq_lemma in Hx2. { (* number-string *)
        destruct_hyp Hx2. repeat ljs_autoforward.
        inverts Hvrel1; tryfalse.
        inverts Hvrel2; tryfalse.
        jauto_js 12.
    }
    asserts : (~(J.type_of jv1 = J.type_number /\ J.type_of jv2 = J.type_string)). {
        rew_logic in Hx2. rew_logic. destruct_hyp Hx2.
        + left. inverts Hvrel1; auto.
        + right. inverts Hvrel2; auto.
    }
    munch_elseif Hx3; repeat rewrite stx_eq_string_eq_lemma in Hx3. { (* string-number *)
        destruct_hyp Hx3. repeat ljs_autoforward.
        inverts Hvrel1; tryfalse.
        inverts Hvrel2; tryfalse.
        jauto_js 15.
    }
    asserts : (~(J.type_of jv1 = J.type_string /\ J.type_of jv2 = J.type_number)). {
        rew_logic in Hx3. rew_logic. destruct_hyp Hx3.
        + left. inverts Hvrel1; auto.
        + right. inverts Hvrel2; auto.
    }
    munch_elseif Hx4; repeat rewrite stx_eq_string_eq_lemma in Hx4. { (* left boolean *)
        repeat ljs_autoforward.
        inverts Hvrel1; tryfalse.
        forwards_th : IH. math.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js 15.
    }
    asserts : (J.type_of jv1 <> J.type_bool). { inverts Hvrel1; auto. }
    munch_elseif Hx5; repeat rewrite stx_eq_string_eq_lemma in Hx5. { (* right boolean *)
        repeat ljs_autoforward.
        inverts Hvrel2; tryfalse.
        forwards_th : IH. math.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js 15.
    }
    asserts : (J.type_of jv2 <> J.type_bool). { inverts Hvrel2; auto. }
    munch_elseif Hx6; repeat rewrite stx_eq_string_eq_lemma in Hx6. { (* right object *)
        destruct Hx6 as (Hx6a&Hx6b).
        inverts Hvrel2; tryfalse.
        asserts : (J.type_of jv1 = J.type_string \/ J.type_of jv1 = J.type_number). {
            destruct_hyp Hx6a; inverts Hvrel1; tryfalse; auto.
        }
        repeat ljs_autoforward.
        forwards_th : red_spec_to_primitive_ok_default.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : IH. math.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js 15.
    }
    asserts : (~((J.type_of jv1 = J.type_string \/ J.type_of jv1 = J.type_number) /\ 
                 J.type_of jv2 = J.type_object)). {
        rew_logic in Hx6. rew_logic. destruct_hyp Hx6; tryfalse.
        + left; inverts Hvrel1; tryfalse; auto.
        + right; inverts Hvrel2; tryfalse; auto.
    }
    munch_elseif Hx7; repeat rewrite stx_eq_string_eq_lemma in Hx7. { (* left object *)
        destruct Hx7 as (Hx7a&Hx7b).
        inverts Hvrel1; tryfalse.
        asserts : (J.type_of jv2 = J.type_string \/ J.type_of jv2 = J.type_number). {
            destruct_hyp Hx7a; inverts Hvrel2; tryfalse; auto.
        }
        repeat ljs_autoforward.
        forwards_th : red_spec_to_primitive_ok_default.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : IH. math.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js 15.
    }
    asserts : (~(J.type_of jv1 = J.type_object /\ 
                 (J.type_of jv2 = J.type_string \/ J.type_of jv2 = J.type_number))). {
        rew_logic in Hx7. rew_logic. destruct_hyp Hx7; tryfalse.
        + right; inverts Hvrel2; tryfalse; auto.
        + left; inverts Hvrel1; tryfalse; auto.
    }
    repeat ljs_autoforward.
    jauto_js 15.
Qed.

Lemma red_expr_binary_op_3_equal_ok : forall k,
    ih_call k ->
    th_ext_expr_binary k LjsInitEnv.privEqEq (J.expr_binary_op_3 J.binary_op_equal)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    forwards_th : red_spec_equal_ok.
    destr_concl;
    jauto_js. 
Qed.

Lemma red_expr_binary_op_3_disequal_ok : forall k,
    ih_call k ->
    th_ext_expr_binary k LjsInitEnv.privnotEqEq (J.expr_binary_op_3 J.binary_op_disequal)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
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
    + jauto_js 10.
    + jauto_js 10.
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
    + jauto_js 10.
    + jauto_js 10.
Qed.

(* TODO move *) 
Lemma puremath_op_regular : forall jop F, 
    J.puremath_op jop F ->
    exists v,
    regular_binary_op_impl jop v.
Proof.
    introv Hpure. destruct Hpure; eauto_js.
Qed.

Lemma red_expr_mult_op_lemma : forall BR k jst jc c st st' r jv1 jv2 v1 v2 s1 s2 op jop F,
    ih_call k ->
    J.puremath_op jop F ->
    L.num_binary_op op F ->
    binds c s1 v1 ->
    binds c s2 v2 ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    L.red_exprh k c st 
        (L.expr_basic (E.make_app_builtin "%PrimMultOp" [L.expr_id s1; L.expr_id s2; E.op2_func op]))
        (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (J.expr_binary_op_3 jop jv1 jv2) (fun _ => True).
Proof.
    introv IHc Hpure Hbop Hbinds1 Hbinds2 Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    ljs_invert_apply.
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
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : eval_binary_op_num_lemma. eassumption. eassumption. 
    destruct_hyp Hx.
    jauto_js 18.
Qed.

Hint Constructors L.num_binary_op : js_ljs.

Lemma red_expr_binary_op_3_puremath_ok : forall jop v F,
    J.puremath_op jop F ->
    regular_binary_op_impl jop v ->
    forall k,
    ih_call k ->
    th_ext_expr_binary k v (J.expr_binary_op_3 jop) (fun jv => True).
Proof.
    introv Hpure Hreg IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts keep Hpure; inverts keep Hreg; inverts red_exprh Hlred;
    ljs_apply; ljs_context_invariant_after_apply;
    lets Hx : red_expr_mult_op_lemma Hvrel1 Hvrel2 __;
    try eassumption; eauto_js 1;
    destr_concl; try ljs_handle_abort; jauto_js 10.
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

Lemma red_expr_binary_op_3_add_ok : forall k,
    ih_call k ->
    ih_expr k ->
    th_ext_expr_binary k LjsInitEnv.privPrimAdd (J.expr_binary_op_3 J.binary_op_add) (fun jv => True).
Proof.
    introv IHc IHe Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    inverts red_exprh Hlred.
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

Inductive inequality_result_related : J.prim -> L.value -> Prop :=
| inequality_result_related_bool : forall b, inequality_result_related (J.prim_bool b) (L.value_bool b)
| inequality_result_related_undefined : inequality_result_related J.prim_undef L.value_undefined
.

Hint Constructors inequality_result_related : js_ljs.

(* TODO move *)
Lemma neg_zero_lemma : neg zero = neg_zero.
Admitted.

Lemma neg_zero_diff_zero : neg_zero <> zero.
Admitted.

(* TODO move *)
Lemma num_lt_eq_lt_bool_lemma : forall n1 n2, L.num_lt n1 n2 = lt_bool n1 n2.
Proof. 
    unfolds L.num_lt. unfolds L.num_comparison_op. 
    rew_refl. eauto.
Qed.

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
    unfolds J.inequality_test_number.
    munch_elseif Hcond. { (* one is NaN *)
        repeat ljs_autoforward.
        destruct_hyp Hcond;
        cases_if; try solve [false; auto];
        jauto_js.
    }
    rew_logic in Hcond.
    cases_if. false; iauto.
    munch_elseif Hcond1. { (* are equal *)
        repeat ljs_autoforward.
        subst_hyp Hcond1.
        cases_if; try solve [false; iauto].
        jauto_js. 
    }
    cases_if.
    munch_elseif Hcond2. { (* zero-negzero *)
        repeat ljs_autoforward.
        destruct_hyp Hcond2.
        specializes H6 __. eauto_js. destruct_hyp H6. repeat determine_epsilon.
        repeat ljs_op_inv. injects.
        rewrite of_int_zero_lemma. rewrite neg_zero_lemma.
        cases_if; try solve [false; auto].
        jauto_js.
    }
    rew_logic in Hcond2.
    cases_if. destruct_hyp a. (* TODO *)
    specializes H6 __. rewrite of_int_zero_lemma; eauto_js. destruct_hyp H6. repeat determine_epsilon. (* TODO *)
    ljs_op_inv. rewrite of_int_zero_lemma in Hcond2.
    rewrite neg_zero_lemma in Hcond2. solve [false; iauto].
    munch_elseif Hcond3. { (* negzero-zero *)
        repeat ljs_autoforward.
        destruct_hyp Hcond3.
        rewrite of_int_zero_lemma. rewrite neg_zero_lemma.
        cases_if; try solve [false; auto].
        jauto_js.
    }
    rew_logic in Hcond3.
    cases_if. destruct_hyp a. (* TODO *)
    specializes H7 __. rewrite of_int_zero_lemma; rewrite neg_zero_lemma; eauto_js. 
        destruct_hyp H7. repeat determine_epsilon. (* TODO *)
    ljs_op_inv. rewrite of_int_zero_lemma in Hcond3.
    rewrite neg_zero_lemma in Hcond3. solve [false; iauto].
    munch_elseif Hcond4. { (* left infinity *)
        repeat ljs_autoforward.
        subst_hyp Hcond4.
        cases_if. jauto_js.
    }
    cases_if.
    munch_elseif Hcond5. { (* right infinity *)
        repeat ljs_autoforward.
        subst_hyp Hcond5.
        cases_if. jauto_js.
    }
    cases_if.
    munch_elseif Hcond6. { (* right neg-infinity *)
        repeat ljs_autoforward.
        subst_hyp Hcond6.
        cases_if. jauto_js.
    }
    cases_if.
    munch_elseif Hcond7. { (* left neg-infinity *)
        repeat ljs_autoforward.
        subst_hyp Hcond7.
        cases_if. jauto_js.
    }
    cases_if.
    repeat ljs_autoforward.
    rewrite num_lt_eq_lt_bool_lemma.
    jauto_js.
Qed.

Lemma inequality_test_string_lemma : forall s1 s2,
    J.inequality_test_string s1 s2 = L.string_lt s1 s2.
Proof.
    eauto.
Qed.

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
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq. {
        inverts Hvrel1; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq2; rewrite stx_eq_string_eq_lemma in Heq2. {
            inverts Hvrel2; tryfalse.
            repeat ljs_autoforward.
            rewrite <- inequality_test_string_lemma.
            jauto_js.
        } {
            repeat ljs_autoforward.
            forwards_th Hx : inequality_test_number_lemma.
            destruct_hyp Hx.
            inverts Hvrel2; unfolds L.typeof; simpl in Heq2; tryfalse;
            jauto_js.
        }
    } {
        repeat ljs_autoforward.
        forwards_th Hx : inequality_test_number_lemma.
        destruct_hyp Hx.
        inverts Hvrel1; unfolds L.typeof; simpl in Heq; tryfalse;
        inverts Hvrel2;
        jauto_js.
    }
Qed.

Lemma red_expr_inequality_op_lemma : forall BR k jst jc c st st' r jv1 jv2 v1 v2 s1 s2 jop b1 b2,
    ih_call k ->
    J.inequality_op jop b1 b2 ->
    binds c s1 v1 ->
    binds c s2 v2 ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    L.red_exprh k c st 
        (L.expr_basic (E.make_app_builtin "%CompareOp" [L.expr_id s1; L.expr_id s2; L.expr_bool b1; L.expr_bool b2]))
        (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (J.expr_binary_op_3 jop jv1 jv2) (fun _ => True).
Proof.
    introv IHc Hop Hbinds1 Hbinds2 Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    ljs_invert_apply.
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

Lemma red_expr_binary_op_3_inequality_ok : forall jop v b1 b2,
    J.inequality_op jop b1 b2 ->
    regular_binary_op_impl jop v ->
    forall k,
    ih_call k ->
    th_ext_expr_binary k v (J.expr_binary_op_3 jop) (fun jv => True).
Proof.
    introv Hpure Hreg IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts keep Hpure; inverts keep Hreg; inverts red_exprh Hlred;
    ljs_apply; ljs_context_invariant_after_apply;
    lets Hx : red_expr_inequality_op_lemma Hvrel1 Hvrel2 __;
    try eassumption; eauto_js 1;
    destr_concl; try ljs_handle_abort; jauto_js 10.
Qed.

Lemma red_expr_binary_op_3_coma_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privPrimComma (J.expr_binary_op_3 J.binary_op_coma) (fun jv => True).
Proof.
    introv Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js 8.
Qed.

Lemma red_expr_binary_op_3_in_ok : forall k,
    ih_call k ->
    th_ext_expr_binary k LjsInitEnv.privin (J.expr_binary_op_3 J.binary_op_in)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
Opaque decide.
    repeat ljs_autoforward.
    cases_decide as Hobj. { (* v is object *)
        repeat ljs_autoforward.
        inverts Hobj.
        inverts Hvrel2.
        forwards_th : red_spec_to_string_unary_ok.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        repeat ljs_autoforward.
        forwards_th : has_property_lemma. prove_bag. (* TODO *)
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js.
    } { (* v not an object, throw *)
        repeat ljs_autoforward.
(*
        asserts Htp : (J.type_of jv2 <> J.type_object). {
            intro Htp.
            inverts Hvrel2; tryfalse.
            apply Hobj. apply L.is_object_object.
        }
*)
        forwards_th : type_error_lemma. iauto.
        destr_concl; tryfalse; ljs_handle_abort.
    }
Qed.

(* TODO move *)
Lemma th_ext_expr_binary_clear_side_condition : forall k v j P,
    th_ext_expr_binary k v j P ->
    th_ext_expr_binary k v j (fun jv => True).
Proof.
    introv Hth Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    forwards_th Hx : Hth.
    destr_concl; try ljs_handle_abort.
    jauto_js.
Qed.

(* TODO move, ljs only *)
Lemma eval_binary_op_int_lemma : forall op F st k1 k2 v,
    L.int_binary_op op F ->
    L.eval_binary_op op st (L.value_int k1) (L.value_int k2) v ->
    v = L.value_int (F k1 k2).
Proof.
    introv Hnumop Hevop.
    inverts Hevop as Hxop;
    inverts Hnumop; try inverts Hxop;
    reflexivity.
Qed.

Lemma red_expr_bitwise_op_lemma : forall BR k jst jc c st st' r jv1 jv2 v1 v2 s1 s2 op jop F,
    ih_call k ->
    J.bitwise_op jop F ->
    L.int_binary_op op F ->
    binds c s1 v1 ->
    binds c s2 v2 ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    L.red_exprh k c st 
        (L.expr_basic (E.make_app_builtin "%BitwiseInfix" [L.expr_id s1; L.expr_id s2; E.op2_func op]))
        (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (J.expr_binary_op_3 jop jv1 jv2) (fun _ => True).
Proof.
    introv IHc Hpure Hbop Hbinds1 Hbinds2 Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_int32_ok.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_int32_ok.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : eval_binary_op_int_lemma. eassumption. eassumption. 
    destruct_hyp Hx.
    jauto_js 18.
Qed.

Hint Constructors L.int_binary_op : js_ljs.

Lemma red_expr_binary_op_3_bitwise_ok : forall jop v F,
    J.bitwise_op jop F ->
    regular_binary_op_impl jop v ->
    forall k,
    ih_call k ->
    th_ext_expr_binary k v (J.expr_binary_op_3 jop) (fun jv => True).
Proof.
    introv Hpure Hreg IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    inverts keep Hpure; inverts keep Hreg; inverts red_exprh Hlred;
    ljs_apply; ljs_context_invariant_after_apply;
    lets Hx : red_expr_bitwise_op_lemma Hvrel1 Hvrel2 __;
    try eassumption; eauto_js 1;
    destr_concl; try ljs_handle_abort; jauto_js 10.
Qed.

Opaque decide. (* TODO move *)

Lemma has_instance_search_ok : forall k BR jst jc c st st' r jptr1 jptr2 ptr1 ptr2,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privHasInstanceSearch [L.value_object ptr1; L.value_object ptr2])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr1 ptr1 \in BR ->
    fact_js_obj jptr2 ptr2 \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_function_has_instance_2 jptr1 jptr2) (fun jv => True).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hcinv Hinv Hf1 Hf2.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Heq; rewrite stx_eq_null_eq_lemma in Heq. { (* is null *)
        forwards* : object_proto_null_lemma.
        repeat ljs_autoforward.
        jauto_js.
    } { (* not null *)
        forwards* Hx : object_proto_not_null_lemma.
        unfold L.object_proto in Hx.
        destruct_hyp Hx.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite Hx0 in *; rewrite stx_eq_object_eq_lemma in Heq1. { (* same *)
            subst_hyp Heq1.
            repeat ljs_autoforward.
            determine_fact_js_obj.
            jauto_js.
        } { (* diff *)
            erewrite <- fact_js_obj_eq_lemma in Heq1 by eassumption.
            repeat ljs_autoforward.
            forwards_th : IH. math. eassumption. eassumption.
            destr_concl; try ljs_handle_abort.
            jauto_js.
        }
    }
Qed.

Lemma has_instance_ok : forall BR k jst jc c st st' r jhi v' jv v jptr ptr,
    ih_call k ->
    has_instance_related jhi v' ->
    J.object_method JsSyntax.object_has_instance_ jst jptr (Some jhi) ->
    L.red_exprh k c st (L.expr_app_2 v' [L.value_object ptr; v]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_has_instance jptr jv) (fun jv => True).
Proof.
    introv IHc Hhirel Hjom Hlred Hcinv Hinv Hvrel Hf.
    inverts Hhirel. {
        ljs_invert_apply.
        repeat ljs_autoforward.
        cases_decide as Hobj. { (* is object *)
            inverts Hobj. inverts Hvrel.
            repeat ljs_autoforward.
            forwards_th : get_lemma. eassumption.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            repeat ljs_autoforward.
            cases_decide as Hpobj. { (* prototype is object *)
                inverts Hpobj.
                inverts H. (* TODO value_related *)
                repeat ljs_autoforward.
                skip. (* TODO search *)
            } { (* prototype not object *)
                lets* Hnobj : not_is_object_js_type_lemma Hpobj.
                repeat ljs_autoforward.
                forwards_th : type_error_lemma. eauto_js.
                destr_concl; try ljs_handle_abort. tryfalse.
            }
        } { (* not object *)
            lets* Hnobj : not_is_object_js_prim_lemma Hobj.
            destruct_hyp Hnobj.
            repeat ljs_autoforward.
            jauto_js.
        }
    } { (* bind *)
        skip. (* not yet in jscert *)
    }
Qed.

Lemma red_expr_binary_op_3_instanceof_ok : forall k,
    ih_call k ->
    th_ext_expr_binary k LjsInitEnv.privinstanceof (J.expr_binary_op_3 J.binary_op_instanceof) (fun jv => True).
Proof.
    introv IHc Hcinv Hinv Hvrel1 Hvrel2 Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hobj. {
        inverts Hobj.
        inverts Hvrel2.
        repeat ljs_autoforward.
        cases_decide as Hidx. {
            rewrite index_binds_eq in Hidx.
            destruct Hidx as (?&Hbindsi).
            forwards* (?&Hhir) : has_instance_related_lemma.
            forwards* : object_method_has_instance_lemma. {
                erewrite read_option_binds_inv by eassumption. econstructor. eassumption.
            }
            repeat ljs_autoforward.
            forwards_th : has_instance_ok; try eassumption.
            destr_concl; try ljs_handle_abort.
            jauto_js.
        } { (* no hasinstance method *)
            repeat ljs_autoforward.
            forwards* : object_method_has_instance_lemma. {
                erewrite read_option_not_index_inv by eassumption. constructor.
            }
            forwards_th : type_error_lemma. eauto_js.
            destr_concl; try ljs_handle_abort. tryfalse.
        }
    } {
        repeat ljs_autoforward.
        lets Hnobj : not_is_object_js_type_lemma Hvrel2 Hobj.
        forwards_th : type_error_lemma. eauto_js.
        destr_concl; try ljs_handle_abort. tryfalse.
    }
Qed.

Lemma red_expr_binary_op_3_regular_ok : forall k op v,
    ih_expr k ->
    ih_call k ->
    regular_binary_op_impl op v ->
    th_ext_expr_binary k v (J.expr_binary_op_3 op) (fun jv => True).
Proof.
    introv IHe IHc Hrop.
    inverts keep Hrop.
    applys~ red_expr_binary_op_3_coma_ok.
    applys~ red_expr_binary_op_3_add_ok.
    applys~ red_expr_binary_op_3_puremath_ok J.puremath_op_sub Hrop.
    applys~ red_expr_binary_op_3_puremath_ok J.puremath_op_mult Hrop.
    applys~ red_expr_binary_op_3_puremath_ok J.puremath_op_div Hrop.
    applys~ red_expr_binary_op_3_puremath_ok J.puremath_op_mod Hrop.
    applys~ red_expr_binary_op_3_bitwise_ok J.bitwise_op_and Hrop.
    applys~ red_expr_binary_op_3_bitwise_ok J.bitwise_op_or Hrop.
    applys~ red_expr_binary_op_3_bitwise_ok J.bitwise_op_xor Hrop.
    skip. (* TODO shifts *)
    skip.
    skip.
    applys~ red_expr_binary_op_3_inequality_ok J.inequality_op_lt Hrop.
    applys~ red_expr_binary_op_3_inequality_ok J.inequality_op_le Hrop.
    applys~ red_expr_binary_op_3_inequality_ok J.inequality_op_gt Hrop.
    applys~ red_expr_binary_op_3_inequality_ok J.inequality_op_ge Hrop.
    applys~ red_expr_binary_op_3_instanceof_ok.
    applys th_ext_expr_binary_clear_side_condition. applys~ red_expr_binary_op_3_in_ok.
    applys th_ext_expr_binary_clear_side_condition. applys~ red_expr_binary_op_3_equal_ok.
    applys th_ext_expr_binary_clear_side_condition. applys~ red_expr_binary_op_3_strict_equal_ok.
    applys th_ext_expr_binary_clear_side_condition. applys~ red_expr_binary_op_3_disequal_ok.
    applys th_ext_expr_binary_clear_side_condition. applys~ red_expr_binary_op_3_strict_disequal_ok.
Qed.

Lemma regular_binary_op_get_impl_lemma : forall op,
    J.regular_binary_op op ->
    exists v,
    regular_binary_op_impl op v.
Proof.
    introv Hop. destruct op; tryfalse; eauto_js.
Qed.

Lemma red_expr_binary_op_ok : forall op k je1 je2,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_binary_op je1 op je2).
Proof.
    introv IHe IHc.
    destruct (classic (J.regular_binary_op op)) as [Hreg|Hreg]. { (* regular ops *)
        lets (v&Himpl) : regular_binary_op_get_impl_lemma Hreg.
        applys red_expr_regular_binary_op_ok; try eassumption. 
        applys red_expr_binary_op_3_regular_ok; try assumption. 
    }
    destruct op; try solve [false; apply Hreg; eauto_js].
    apply red_expr_binary_op_and_ok; eassumption.
    apply red_expr_binary_op_or_ok; eassumption.
Qed.

(** *** Assignment *)

(* TODO should not be necessary *)
Hint Extern 3 (J.red_expr _ _ (J.expr_assign_1 _ (Some _) _) _) =>
    eapply J.red_expr_assign_1_compound : js_ljs.

Lemma red_expr_assign_compound_ok : forall k je1 je2 op,
    J.regular_binary_op op ->
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_assign je1 (Some op) je2).
Proof.
    introv Hreg IHe IHc Hcinv Hinv Hlred.
    lets (v&Himpl) : regular_binary_op_get_impl_lemma Hreg.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_assign.
    reference_match_cases Hlred Hx Heq Hrp. { (* object field assign *)
        unfolds E.make_modify_field.
        lets (s'&Heqq&Hbuiltin) : make_op2_red_expr_lemma Himpl. unfolds E.js_op2_func.
        rewrite Heqq in Hlred. clear Heqq.
        repeat ljs_autoforward.
        ljs_invert_apply.
        do 2 ljs_autoforward. (* TODO stopping condition for autoforward *)
        forwards_th Hx : field_access_lemma. eassumption.
        destruct_hyp Hx; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : prop_get_value_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Heq1 : Hbuiltin ___; try eassumption. subst_hyp Heq1.
        forwards_th Hx : red_expr_binary_op_3_regular_ok. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : prop_put_value_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* variable assign *)
        unfolds E.make_var_modify.
        lets (s'&Heqq&Hbuiltin) : make_op2_red_expr_lemma Himpl. unfolds E.js_op2_func.
        rewrite Heqq in Hlred. clear Heqq.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hstrict : execution_ctx_related_strictness_flag (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        subst_hyp Hstrict.
        forwards_th Hx : env_get_value_lemma. eauto_js. eassumption.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Heq : Hbuiltin ___; try eassumption. subst_hyp Heq.
        forwards_th Hx : red_expr_binary_op_3_regular_ok. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th Hx : env_put_value_lemma. eauto_js. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* invalid lhs, error thrown *)
        lets (s&Heqq&Hbuiltin) : make_op2_red_expr_lemma Himpl.
        rewrite Heqq in Hx. clear Heqq.
        repeat ljs_autoforward.
        lets Heq : Hbuiltin ___; try eassumption. subst_hyp Heq.
        destr_concl; js_red_expr_getvalue_fwd; try ljs_handle_abort.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        forwards_th Hx : red_expr_binary_op_3_regular_ok. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th Hx : reference_error_lemma. eauto_js.
        destr_concl; tryfalse.
        ljs_handle_abort.
    }
Qed.

Lemma red_expr_assign_simple_ok : forall k je1 je2,
    ih_expr k ->
    ih_call k ->
    th_expr k (J.expr_assign je1 None je2).
Proof.
    introv IHe IHk Hcinv Hinv Hlred.
    unfolds js_expr_to_ljs. simpl in Hlred. unfolds E.make_assign.
    reference_match_cases Hlred Hx Heq Hrp. { (* object field assign *)
        unfolds E.make_set_field.
        repeat ljs_autoforward.
        ljs_invert_apply.
        do 2 ljs_autoforward. (* TODO stopping condition for autoforward *)
        forwards_th Hx : field_access_lemma. eassumption.
        destruct_hyp Hx; try ljs_handle_abort.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        destr_concl; try ljs_handle_abort.
        repeat ljs_autoforward.
        forwards_th : prop_put_value_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* variable assign *)
        repeat ljs_autoforward.
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets Hlerel : execution_ctx_related_lexical_env (context_invariant_execution_ctx_related Hcinv) ___.
            eassumption.
        forwards_th Hx : red_spec_lexical_env_get_identifier_ref_lemma.
        destruct_hyp Hx; try ljs_handle_abort.
        ljs_invert_apply.
        repeat ljs_autoforward.
        ljs_invert_apply.
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
    ih_call k ->
    th_expr k (J.expr_assign je1 oo je2).
Proof.
    introv IHe IHc.
    destruct oo.
    eapply red_expr_assign_compound_ok. skip. assumption. assumption. (* TODO: regular op assumption *)
    eapply red_expr_assign_simple_ok; assumption.
Qed.
