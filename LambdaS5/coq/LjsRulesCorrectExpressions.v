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
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.

(* Expressions *)

Lemma red_expr_literal_ok : forall k l,
    th_expr k (J.expr_literal l).
Proof.
    introv.
    unfolds.
    introv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts red_exprh Hlred; ijauto_js.
Qed.

Lemma red_expr_identifier_ok : forall k i,
    th_expr k (J.expr_identifier i).
Proof.
    introv Hinv Hlred.
    repeat ljs_autoforward.

    skip.
Qed.


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
    repeat destr_concl; unfold_concl.
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
    simpls.  
    repeat ljs_autoforward.
(* TODO *)
    match goal with H : binds ?c _ _ |- _ => sets_eq c' : c end.
    asserts Hinv' : (state_invariant BR jst jc c' st). skip.
    subst c'.

    repeat binds_inv.
    forwards_th red_spec_to_boolean_unary_ok. 
    destr_concl;
    (asserts Hinv'' : (state_invariant BR' jst' jc c st0); [skip | idtac]); (* TODO *)
    try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    binds_inv.
    injects.
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
    repeat ljs_autoforward.
(* TODO *)
    match goal with H : binds ?c _ _ |- _ => sets_eq c' : c end.
    asserts Hinv' : (state_invariant BR jst jc c' st). skip.
    subst c'.

    repeat binds_inv.
    forwards_th red_spec_to_number_unary_ok.
    destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. skip.
    jauto_js. skip.
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
Admitted.

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

Lemma red_expr_unary_op_ok : forall op k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    destruct op.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    apply red_expr_unary_op_add_ok.
    apply red_expr_unary_op_neg_ok.
    skip.
    apply red_expr_unary_op_not_ok.
Qed.

Lemma strict_equality_test_lemma : forall BR jv1 v1 jv2 v2 k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privStxEq [v1; v2]) (L.out_ter st' r) ->
    value_related BR jv2 v2 ->
    value_related BR jv1 v1 ->
    exists b, 
    b = J.strict_equality_test jv1 jv2 /\
    r = L.res_value (L.value_bool b) /\
    st = st'.
Proof.
Admitted.

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
    forwards Heql : strict_equality_test_lemma.
    jauto_js. jauto_js. jauto_js. destruct_hyp Heql.
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
    forwards Heql : strict_equality_test_lemma.
    jauto_js. jauto_js. jauto_js. destruct_hyp Heql. 
    repeat ljs_autoforward. injects.
    jauto_js. left. jauto_js 8.
Qed.

Lemma red_spec_equal_ok : forall k,
    th_ext_expr_binary k LjsInitEnv.privEqEq J.spec_equal
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
Admitted.

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
    inv_fwd_ljs.
    injects.
    jauto_js. left. jauto_js 15. 
Qed.

Lemma red_expr_binary_op_ok : forall op k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_binary_op je1 op je2).
Proof.
    destruct op.
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
    apply red_expr_binary_op_equal_ok.
    apply red_expr_binary_op_disequal_ok.
    apply red_expr_binary_op_strict_equal_ok.
    apply red_expr_binary_op_strict_disequal_ok.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
Qed.
