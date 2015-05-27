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

(* Expressions *)

Lemma red_expr_literal_ok : forall k l,
    th_expr k (J.expr_literal l).
Proof.
    introv.
    unfolds.
    introv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts red_exprh Hlred; ijauto_js.
Qed.

Lemma get_identifier_value_lemma : forall jlenv k BR jst jc c st st' r b v i,
    lexical_env_related BR st jlenv v ->
    binds c "strict" (L.value_bool b) ->
    binds c "context" v ->
    binds c "id" (L.value_string i) ->
    includes_init_ctx c ->
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic LjsInitEnv.ex_privEnvGet) (L.out_ter st' r) ->
    exists BR' jst' jst'' jref,
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_spec jst jc (J.spec_lexical_env_get_identifier_ref jlenv i b) (J.specret_val jst'' jref) /\
    (exists jv v', r = L.res_value v' /\
     J.red_spec jst'' jc (J.spec_get_value (J.resvalue_ref jref)) (J.specret_val jst' jv) /\
     value_related BR' jv v').
Proof.
    inductions jlenv;
    introv Henvrel; inverts Henvrel;
    introv Hstrict Hcontext Hid Hii Hinv Hred.
    (* nil *)
    repeat ljs_autoforward. 
    skip.
    (* cons *)
    repeat ljs_autoforward.
(*
    cases_decide. 
    repeat ljs_autoforward.
*)
    skip.
Qed.

Lemma red_expr_identifier_ok : forall k i,
    th_expr k (J.expr_identifier i).
Proof.
    introv Hinv Hlred.
    repeat ljs_autoforward.
Admitted.
(*
    inverts H7. (* TODO *)
    ljs_inv_value_is_closure. 
    ljs_inv_closure_ctx. unfold L.closure_body in H12.
    skip.
Qed.
*)

(* TODO Delete *)
Ltac cases_if_auto_js ::=
    let Hif := fresh "Hif" in 
    first [case_if as Hif; [try solve [destruct_hyp Hif; tryfalse] | try solve [false; apply Hif; eauto_js]] 
          |case_if as Hif; [idtac]].

Lemma red_expr_conditional_ok : forall k je1 je2 je3,
    ih_expr k ->
    th_expr k (J.expr_conditional je1 je2 je3).
Proof.
    introv IHe Hinv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.

    forwards_th red_spec_to_boolean_ok. 

    destr_concl.
    destruct b;
    inv_internal_fwd_ljs;
    apply_ih_expr.
    (* true *)
    jauto_js 11.
    jauto_js 18.
    (* false *)
    repeat destr_concl; unfold_concl.
    jauto_js 11.
    jauto_js 18. 
    (* abort *)
    ljs_handle_abort.
Qed.

Lemma red_expr_assign0_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_assign je1 None je2).
Proof.
Admitted.

Lemma red_expr_unary_op_2_not_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryNot (J.expr_unary_op_2 J.unary_op_not)
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHe Hinv Hvrel Hlred.
    inverts Hlred. 
    ljs_apply.
    ljs_state_invariant_after_apply.
    simpls.  
    repeat ljs_autoforward.
    forwards_th red_spec_to_boolean_unary_ok. 
    destr_concl;
    (asserts Hinv'' : (state_invariant BR' jst' jc c st0); [skip | idtac]); (* TODO *)
    try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma red_expr_unary_op_not_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_not je).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th red_expr_unary_op_2_not_ok.
    repeat destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js.
    jauto_js 15.
Qed.

Lemma red_expr_unary_op_2_add_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryPlus (J.expr_unary_op_2 J.unary_op_add)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHe Hinv Hvrel Hlred.
    inverts Hlred. 
    ljs_apply.
    ljs_state_invariant_after_apply. 
    repeat ljs_autoforward.
    repeat binds_inv.
    forwards_th red_spec_to_number_unary_ok.
    destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. 
    jauto_js. 
Qed.

Lemma red_expr_unary_op_add_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_add je).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th red_expr_unary_op_2_add_ok.
    repeat destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js.
    jauto_js. right. jauto_js.
Qed.

Lemma red_expr_unary_op_2_neg_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privUnaryNeg (J.expr_unary_op_2 J.unary_op_neg)
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv IHe Hinv Hvrel Hlred.
    inverts Hlred.
    ljs_apply.
    ljs_state_invariant_after_apply. 
    repeat ljs_autoforward.
    forwards_th red_spec_to_number_unary_ok.
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
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th red_expr_unary_op_2_neg_ok.
    repeat destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js.
    jauto_js 15.
Qed.

Lemma red_expr_unary_op_void_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_void je).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js. left. jauto_js.
Qed.

Lemma red_expr_unary_op_bitwise_not_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_bitwise_not je).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    (* TODO ToInt32 spec_to_int32 *)
Admitted.

Lemma red_expr_unary_op_ok : forall op k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    destruct op.
    skip.
    apply red_expr_unary_op_void_ok.
    skip.
    skip.
    skip.
    skip.
    skip.
    apply red_expr_unary_op_add_ok.
    apply red_expr_unary_op_neg_ok.
    apply red_expr_unary_op_bitwise_not_ok.
    apply red_expr_unary_op_not_ok.
Qed.

(* TODO move *)
Lemma state_invariant_lfun_obj : forall BR jst jc c st,
    state_invariant BR jst jc c st ->
    heaps_bisim_lfun_obj BR.
Proof. 
    introv Hinv. 
    eapply heaps_bisim_consistent_lfun_obj. eapply state_invariant_heaps_bisim_consistent. eassumption.
Qed.

Lemma state_invariant_rfun_obj : forall BR jst jc c st,
    state_invariant BR jst jc c st ->
    heaps_bisim_rfun_obj BR.
Proof. 
    introv Hinv. 
    eapply heaps_bisim_consistent_rfun_obj. eapply state_invariant_heaps_bisim_consistent. eassumption.
Qed.

Lemma equality_test_for_same_type_lemma : forall BR jst jc c st jtp jv1 jv2 v1 v2,
    state_invariant BR jst jc c st ->
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

Lemma strict_equality_test_lemma : forall BR jst jc c st jv1 jv2 v1 v2,
    state_invariant BR jst jc c st ->
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

Lemma red_strict_equality_test_lemma : forall BR jst jc jv1 v1 jv2 v2 k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privStxEq [v1; v2]) (L.out_ter st' r) ->
    state_invariant BR jst jc c st ->
    value_related BR jv2 v2 ->
    value_related BR jv1 v1 ->
    exists b, 
    b = J.strict_equality_test jv1 jv2 /\
    r = L.res_value (L.value_bool b) /\
    st = st'.
Proof.
    introv Hlred Hinv Hvrel1 Hvrel2.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    applys strict_equality_test_lemma; eauto.
    reflexivity.
    reflexivity.
Qed.

Lemma red_expr_binary_op_strict_equal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_strict_equal je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards Heql : red_strict_equality_test_lemma.
    jauto_js. jauto_js. jauto_js. jauto_js. destruct_hyp Heql.
    jauto_js. left. jauto_js 8.
Qed.

Lemma red_expr_binary_op_strict_disequal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_strict_disequal je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards Heql : red_strict_equality_test_lemma.
    jauto_js. jauto_js. jauto_js. jauto_js. destruct_hyp Heql. 
    repeat ljs_autoforward. 
    jauto_js. left. jauto_js 8.
Qed.

(* TODO move *)
Lemma value_related_equality_test_same_type : forall BR jst jc c st jtp jv1 jv2 v1 v2,
    state_invariant BR jst jc c st ->
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
    | H : state_invariant ?BR ?jst _ _ _ |- _ =>
        match goal with HS : BR \c _ |- _ => fail 1 | _ => idtac end; 
        match goal with
        | _ : J.abort (J.out_ter jst ?jr) |- _ => T BR jst jr
        | _ => T BR jst true
        end
    end.

Ltac unfold_concl_tac_with BR jst dir :=
    match goal with
    | |- concl_expr_getvalue _ _ _ _ _ _ _ _ => unfolds; unfold_concl_tac_with BR jst dir
    | |- concl_spec _ _ _ _ _ _ _ _ _ _ => 
        unfolds; exists BR jst; split; [match dir with true => left | _ => right; exists dir end | splits]
    end.

Ltac unfold_concl_tac := find_last_invariant_then unfold_concl_tac_with.

Tactic Notation "ljs_handle_abort_tac" integer(k) := 
    repeat (ljs_propagate_abort || ljs_abort_from_js); 
    unfold_concl_tac; solve [jauto_set; eauto k with js_ljs bag typeclass_instances].

Tactic Notation "ljs_handle_abort_tac" := ljs_handle_abort_tac 5.

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
    introv Hinv Hvrel1 Hvrel2 Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_state_invariant_after_apply.
    repeat inv_fwd_ljs.
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
    introv Hinv Hvrel1 Hvrel2 Hlred.
    forwards_th red_spec_equal_ok.
    destr_concl;
    jauto_js. 
Qed.

Lemma red_expr_binary_op_equal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_equal je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th red_expr_binary_op_3_equal_ok.
    repeat destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js 8.
    jauto_js 15.
Qed.

Lemma red_expr_binary_op_disequal_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_disequal je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat inv_fwd_ljs.
    forwards_th red_spec_equal_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    jauto_js. left. jauto_js 15. 
Qed.

Lemma red_expr_binary_op_and_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_and je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th red_spec_to_boolean_unary_ok.
    destr_concl; [idtac | ljs_handle_abort_tac 14].
    res_related_invert.
    resvalue_related_invert.
    destruct b; repeat ljs_autoforward.
    destr_concl; [idtac | ljs_handle_abort_tac 8].
    unfold_concl_tac; jauto_js 8.
    unfold_concl_tac; jauto_js 8. 
Qed.

Lemma red_expr_binary_op_or_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_or je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th red_spec_to_boolean_unary_ok.
    destr_concl; [idtac | ljs_handle_abort_tac 14].
    res_related_invert.
    resvalue_related_invert.
    destruct b; repeat ljs_autoforward.
    unfold_concl_tac; jauto_js 8. 
    destr_concl; [idtac | ljs_handle_abort_tac 8].
    unfold_concl_tac; jauto_js 8. 
Qed.

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
    introv Hpure IHe Hinv Hlred.
    forwards (op&Hnumop&Heq) : js_puremath_to_ljs Hpure.
    rewrite Heq in Hlred.
    repeat ljs_autoforward.
    destr_concl; [idtac | ljs_handle_abort_tac 15].
    repeat ljs_autoforward.
    destr_concl; [idtac | ljs_handle_abort_tac 15].
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    ljs_apply.
    ljs_state_invariant_after_apply. 
    repeat ljs_autoforward.
    forwards_th red_spec_to_number_unary_ok.
    destr_concl(*; try ljs_handle_abort*). 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th red_spec_to_number_unary_ok.
    destr_concl(*; try ljs_handle_abort*). 
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    inverts red_exprh H15. (* TODO *)
    ljs_apply.
    repeat ljs_autoforward.
    autoforwards Hx : eval_binary_op_num_lemma. 
    destruct_hyp Hx.
    unfold_concl_tac. 
    jauto_js 18. 
    applys state_invariant_restore_lexical_env Hinv H16. (* TODO *)
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.

    (* TODO *)
    repeat (ljs_propagate_abort || ljs_abort_from_js).
    unfold_concl_tac. jauto_js 14. 
    applys state_invariant_restore_lexical_env Hinv H16. (* TODO *)
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.

    (* TODO *)
    repeat (ljs_propagate_abort || ljs_abort_from_js).
    unfold_concl_tac. jauto_js 14. 
    applys state_invariant_restore_lexical_env Hinv H10. (* TODO *)
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.
    eauto_js 6.
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

Lemma red_expr_binary_op_inequality : forall k je1 je2 jop b1 b2,
    J.inequality_op jop b1 b2 ->
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 jop je2).
Proof.
Admitted.

Lemma red_expr_binary_op_coma_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 J.binary_op_coma je2).
Proof.
    introv IHe Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    destr_concl; [idtac | ljs_handle_abort_tac 15].
    unfold_concl_tac; jauto_js 8.
Qed.

Lemma red_expr_binary_op_ok : forall op k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 op je2).
Proof.
    destruct op; introv.
    applys red_expr_binary_op_puremath J.puremath_op_mult.
    applys red_expr_binary_op_puremath J.puremath_op_div.
    applys red_expr_binary_op_puremath J.puremath_op_mod.
    skip.
    applys red_expr_binary_op_puremath J.puremath_op_sub.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
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
