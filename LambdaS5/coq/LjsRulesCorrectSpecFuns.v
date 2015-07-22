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

(* TODO move *)
(*
Hint Extern 50 => erewrite read_option_not_index_inv by prove_bag : js_ljs.
Hint Extern 50 => erewrite read_option_binds_inv by prove_bag : js_ljs.
*)
Lemma option_construct_related_none_lemma : forall (m : finmap _ _) s,
    ~index m s ->
    option_construct_related None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option_construct_related_some_lemma : forall jcall (m : finmap _ _) s v,
    binds m s v ->
    construct_related jcall v ->
    option_construct_related (Some jcall) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Resolve option_construct_related_none_lemma option_construct_related_some_lemma : js_ljs.

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

Lemma option_codetxt_related_none_lemma : forall (m : finmap _ _) s,
     ~index m s ->
     option_codetxt_related None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option_codetxt_related_some_lemma : forall (m : finmap _ _) s jfb v,
     binds m s v ->
     codetxt_related jfb v ->
     option_codetxt_related (Some jfb) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Resolve option_codetxt_related_none_lemma option_codetxt_related_some_lemma : js_ljs.

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

Lemma option_call_related_lemma : forall BR jst st jptr ptr obj v,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_code obj = v ->
    exists jcon,
    option_call_related jcon v.
Proof.
    introv Hinv Hbs Hbinds Hcode.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    rewrite Hcode in object_prim_related_call.
    eauto.
Qed.

Lemma call_related_lemma : forall BR jst st jptr ptr obj clo,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_code obj = L.value_closure clo ->
    exists jcon,
    call_related jcon (L.value_closure clo).
Proof.
    introv Hinv Hbs Hbinds Hcode.
    forwards (jcon&Hocall) : option_call_related_lemma; try eassumption.
    inverts Hocall.
    eauto.
Qed.

Lemma call_related_not_undefined_lemma : forall jcon v,
    call_related jcon v -> v <> L.value_undefined.
Proof.
    introv Hrel Hv.
    subst_hyp Hv.
    inverts Hrel as Hx. inverts Hx.
Qed.

(* TODO move *)
Lemma call_related_determine1_lemma : forall jcall1 jcall2 v,
    call_related jcall1 v ->
    call_related jcall2 v ->
    jcall1 = jcall2.
Proof.
    introv Hcr1 Hcr2.
    skip. (* TODO modify the env, this is not true! *)
Qed.

Lemma object_method_call_lemma : forall BR jst st jptr ptr obj jcall,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    call_related jcall (L.object_code obj) -> (* TODO option_call *)
    J.object_method J.object_call_ jst jptr (Some jcall).
Proof.
    introv Hinv Hbs Hbinds Hcrel.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    inverts object_prim_related_call as Hp1 Hp2. {
        lets Heq : call_related_determine1_lemma Hp1 Hcrel. subst_hyp Heq.
        symmetry in Hp2. unfolds.
        jauto_js.
    } {
        rewrite <- Hp2 in Hcrel.
        lets Hx : call_related_not_undefined_lemma Hcrel. tryfalse.
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
    lets (jcon&Hcall) : call_related_lemma Hinv Hbs ___; try eassumption. (* TODO *)
    lets Hmeth : object_method_call_lemma ___; try eassumption. rewrite H6. eassumption.
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
        skip. (* TODO *)
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

Lemma make_native_error_lemma : forall BR k jst jc c st st' jv1 jv2 v1 v2 r,
    L.red_exprh k c st 
       (L.expr_app_2 LjsInitEnv.privMakeNativeError [v1; v2]) 
       (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    (v2 = L.value_undefined \/ exists s, v2 = L.value_string s) ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_build_error jv1 jv2) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hcinv Hinv Hv Hvrel1 Hvrel2. 
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    repeat ljs_autoforward. {
        inverts Hvrel2.
        jauto_js 15.
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
    (forwards_th : make_native_error_lemma; [eauto | idtac]);
    destr_concl.
    res_related_invert.
    repeat inv_fwd_ljs.
    forwards_th Hy : priv_js_error_lemma. destruct_hyp Hy.
    repeat inv_fwd_ljs.
    resvalue_related_invert.
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
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat (ljs_autoforward || decide_stx_eq).
    (* null *)
    destruct Hvrel; invert_stx_eq.
    forwards_th Hx : type_error_lemma. iauto. 
    destr_concl; tryfalse.
    jauto_js.
    (* undefined *)
    destruct Hvrel; invert_stx_eq.
    forwards_th Hx : type_error_lemma. iauto. 
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
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    jauto_js 22.
    (* boolean *)
    destruct Hvrel; invert_stx_eq.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    jauto_js 22.
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
    forwards Hmeth : object_method_construct_lemma; try eassumption. eauto_js.
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

Lemma decl_env_record_related_empty : forall BR,
    decl_env_record_vars_related BR \{} \{}.
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
    asserts Hlerel : (lexical_env_related BR (J.execution_ctx_lexical_env jc) v).
    solve [eauto using context_invariant_lexical_env_related].
    forwards_th Hx : new_env_record_decl_lemma. 
    destruct_hyp Hx.
    do 2 eexists. splits; try reflexivity.
    eauto_js.
    eauto_js 8.
    eapply context_invariant_push_context_lemma.
    eapply lexical_env_related_cons; eauto_js 15.
    eauto_js 10. eauto_js 10.
Qed.

(* TODO move *)
Definition mutability_of_bools b1 b2 :=
    if b1 then J.mutability_of_bool b2 else J.mutability_immutable.

(* TODO move *)
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
    destruct (classic (s = s')).
    (* equal *)
    substs.
    right.
    do 3 eexists. split.
    rew_binds_eq. iauto.
    split; [idtac | eassumption].
    simpls.
    rewrite binds_update_same_eq.
    destruct b1; destruct b2; simpl; tryfalse; try reflexivity. 
    (* disequal *)
    lets Hx : decl_env_record_related_vars s'.
    destruct_hyp Hx.
    left. split. rew_index_eq. iauto.
    simpls. rew_index_eq. iauto.
    right. simpls. do 3 eexists. rew_heap_to_libbag in *. rew_binds_eq. iauto.
Qed.

Lemma make_getter_lemma : forall k c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeGetter [v]) (L.out_ter st' r) ->
    exists ptr obj,
    ~index st ptr /\
    getter_proxy obj v /\
    st' = st \(ptr := obj) /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    do 2 eexists. splits; eauto_js; eauto_js.
Qed.

Lemma make_setter_lemma : forall k c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeSetter [v]) (L.out_ter st' r) ->
    exists ptr obj,
    ~index st ptr /\
    setter_proxy obj v /\
    st' = st \(ptr := obj) /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    do 2 eexists. splits; eauto_js; eauto_js.
Qed.

Lemma make_getter_invariant_lemma : forall BR k c jst st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeGetter [v]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    exists ptr,
    st \c st' /\ 
    state_invariant (\{fact_getter_proxy ptr v} \u BR) jst st' /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred Hinv.
    lets Hx : make_getter_lemma Hlred.
    destruct_hyp Hx.
    jauto_js.
Qed.

Lemma make_setter_invariant_lemma : forall BR k c jst st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privMakeSetter [v]) (L.out_ter st' r) ->
    state_invariant BR jst st ->
    exists ptr,
    st \c st' /\ 
    state_invariant (\{fact_setter_proxy ptr v} \u BR) jst st' /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred Hinv.
    lets Hx : make_setter_lemma Hlred.
    destruct_hyp Hx.
    jauto_js.
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
    state_invariant BR (J.env_record_write_decl_env jst jeptr s (mutability_of_bools b1 b2) jv) st'.
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
    erewrite js_env_record_write_decl_env_lemma by eauto.
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
    state_invariant BR (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool b2) jv) st'.
Proof.
    intros. eapply decl_env_add_binding_lemma; eauto.
Qed.

Lemma create_mutable_binding_some_lemma : forall jst jc jeptr s b2 jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s (Some b2)) 
        (J.out_void (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool b2) 
        (J.value_prim J.prim_undef))).
Proof.
    introv Hbinds Hnind. eauto_js.
Qed. 

Lemma create_mutable_binding_none_lemma : forall jst jc jeptr s jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s None) 
        (J.out_void (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool false) 
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
        (J.out_void (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool b2) jv)).
Proof.
    introv Hbinds Hnind.
    erewrite js_env_record_write_decl_env_lemma by eauto.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    erewrite js_env_record_write_decl_env_lemma by eauto.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding.
    eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl.
    eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x. 
    erewrite js_env_record_write_decl_env_lemma in EQx by eauto_js.
    rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed. 

Hint Resolve create_set_mutable_binding_some_lemma : js_ljs.

Lemma create_set_mutable_binding_none_lemma : forall jst jc jeptr s jder jv b,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_set_mutable_binding jeptr s None jv b) 
        (J.out_void (J.env_record_write_decl_env jst jeptr s (J.mutability_of_bool false) jv)).
Proof.
    introv Hbinds Hnind.
    erewrite js_env_record_write_decl_env_lemma by eauto.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    erewrite js_env_record_write_decl_env_lemma by eauto.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding.
    rew_heap_to_libbag. eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl.
    rew_heap_to_libbag. eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x. 
    erewrite js_env_record_write_decl_env_lemma in EQx by eauto_js.
    rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed. 

Hint Resolve create_set_mutable_binding_none_lemma : js_ljs.
