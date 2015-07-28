Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Export LjsPrettyRulesIndexedInvert.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(** ** Implicit Type declarations 
    They are common for all LjsRulesCorrect* libraries. *)

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

(** ** Tactics and proof automation *)

(** The hint database [js_ljs] is used for automated proving of conclusions. *)

Create HintDb js_ljs discriminated.

Create HintDb xcore discriminated.

Hint Resolve conj or_introl or_intror ex_intro : xcore.
Hint Extern 0 => reflexivity : xcore.
Hint Extern 50 (~_) => progress rew_logic : xcore.
Hint Extern 60 (~_) => solve [let H := fresh in intro H; inversion H] : xcore.

Hint Extern 1 => solve [eauto 10 with nocore typeclass_instances] : js_ljs.

(* Hint Extern 99 (~_) => solve [intro; eauto 4 with js_ljs bag nocore xcore] : js_ljs.*) (* potentially slow *) 

(** The constructors for relating JS to S5 are used as hints. *)

Hint Constructors construct_prealloc_related : js_ljs.
Hint Constructors construct_related : js_ljs.
Hint Constructors codetxt_related : js_ljs.
Hint Constructors usercode_related : js_ljs.
Hint Constructors call_prealloc_related : js_ljs.
Hint Constructors call_related : js_ljs.
Hint Constructors option_call_related : js_ljs.
Hint Constructors attributes_data_related : js_ljs.
Hint Constructors attributes_accessor_related : js_ljs. 
Hint Constructors attributes_related : js_ljs.
Hint Constructors type_related : js_ljs.
Hint Constructors value_related : js_ljs.
Hint Constructors resvalue_related : js_ljs.
Hint Constructors res_related : js_ljs.
Hint Constructors env_record_related : js_ljs.
Hint Constructors decl_env_record_related : js_ljs.
Hint Constructors object_env_record_related : js_ljs.
Hint Constructors lexical_env_related : js_ljs.
Hint Constructors object_related : js_ljs.
Hint Constructors object_prim_related : js_ljs.
Hint Constructors js_exn_object_ptr : js_ljs.
Hint Constructors js_exn_object : js_ljs.
Hint Constructors getter_proxy : js_ljs.
Hint Constructors setter_proxy : js_ljs.
Hint Constructors fact_ptr : js_ljs.
(* Hint Constructors arg_list : js_ljs. *)
Hint Constructors js_red_spec_get_value_or_abort : js_ljs.
Hint Constructors js_red_expr_getvalue : js_ljs.
Hint Constructors ejs_reference_producing js_reference_producing : js_ljs.
Hint Constructors ref_base_type_related : js_ljs.
Hint Constructors ref_base_type_var : js_ljs.
Hint Constructors ref_base_type_obj : js_ljs.
Hint Constructors js_reference_type : js_ljs.

Hint Constructors Option Option2 Option3 Option4 Forall Forall2 Forall3 : js_ljs.

Hint Extern 99 (value_related _ (J.object_proto_ _) (L.object_proto _)) => (* why is it needed? *)
    first [eapply value_related_null | eapply value_related_object] : js_ljs.

(** The constructors for S5 *)

Hint Constructors L.stx_eq : js_ljs.
Hint Constructors L.abort L.res_is_control L.res_is_value : js_ljs.
Hint Constructors L.is_primitive : js_ljs. 

(** The constructors of JSCert are used as hints, for automated building of
    the derivation trees for the semantics judgment. *)

Hint Constructors J.red_expr : js_ljs.
Hint Constructors J.red_stat : js_ljs.
Hint Constructors J.red_spec : js_ljs.
Hint Constructors J.abort : js_ljs.
Hint Constructors J.lazy_op : js_ljs.
Hint Constructors J.bitwise_op : js_ljs.
Hint Constructors J.shift_op : js_ljs.
Hint Constructors J.inequality_op : js_ljs.
Hint Constructors J.puremath_op : js_ljs.
Hint Constructors J.prepost_op : js_ljs.

(** Unfolding hints *)

Hint Extern 4 (option_value_related _ _ _) => unfold option_value_related : js_ljs.
Hint Extern 4 (option_construct_related _ _) => unfold option_construct_related : js_ljs.
Hint Extern 4 (option_codetxt_related _ _) => unfold option_codetxt_related : js_ljs.
Hint Extern 4 (option_usercode_related _ _ _ _ _) => unfold option_usercode_related : js_ljs.
Hint Extern 4 (res_related _ _ _ (J.res_throw _) _) => unfold J.res_throw : js_ljs.
Hint Extern 4 (J.regular_binary_op _) => unfold J.regular_binary_op : js_ljs.
Hint Extern 4 (J.ref_is_unresolvable _) => unfold J.ref_is_unresolvable : js_ljs.

(** Automatic deconstructing of ifs in goals *)

(*
Hint Extern 11 => match goal with |- context [If _ then _ else _] => case_if end : js_ljs.
*)

(* TODO logical hints - move? different database? *)

Hint Extern 50 (~_) => progress rew_logic.
Hint Extern 1 (_ <> _) => solve [let H := fresh in intro H; injects H; false]. 
Hint Extern 5 (_ < _) => math : js_ljs. 

(** Additional hints *)

Hint Resolve js_object_alloc_lemma : js_ljs.
Hint Resolve js_lexical_env_alloc_object_lemma : js_ljs.
Hint Resolve js_lexical_env_alloc_decl_lemma : js_ljs.
Hint Resolve js_object_set_property_lemma : js_ljs.
Hint Resolve js_object_fresh_index js_env_record_fresh_index : js_ljs.
Hint Resolve js_state_fresh_ok_update_object_preserved : js_ljs.
Hint Resolve js_state_fresh_ok_update_env_record_preserved : js_ljs.
Hint Resolve js_state_fresh_ok_next_fresh_update_object_preserved : js_ljs.
Hint Resolve js_state_fresh_ok_next_fresh_update_env_record_preserved : js_ljs.
Hint Resolve js_state_next_fresh_index_object_preserved : js_ljs.
Hint Resolve js_state_next_fresh_index_env_record_preserved : js_ljs.
Hint Resolve js_state_next_fresh_binds_object_preserved : js_ljs.
Hint Resolve js_state_next_fresh_binds_env_record_preserved : js_ljs.
Hint Resolve js_state_next_fresh_index_object_preserved_inv : js_ljs.
Hint Resolve js_state_next_fresh_index_env_record_preserved_inv : js_ljs.
Hint Resolve js_state_next_fresh_binds_object_preserved_inv : js_ljs.
Hint Resolve js_state_next_fresh_binds_env_record_preserved_inv : js_ljs.

(** Pre-substitution hints *)
(* TODO are they necessary? *)

Lemma res_related_break_hint : forall BR jst st jrv v jl s,
    resvalue_related BR jrv v -> s = E.js_label_to_ejs "%break" jl ->
    res_related BR jst st (J.res_intro J.restype_break jrv jl) 
        (L.res_break s v). 
Proof. intros. substs. eauto with js_ljs. Qed.

Lemma res_related_continue_hint : forall BR jst st jrv v jl s,
    resvalue_related BR jrv v -> s = E.js_label_to_ejs "%continue" jl ->
    res_related BR jst st (J.res_intro J.restype_continue jrv jl) 
        (L.res_break s v). 
Proof. intros. substs. eauto with js_ljs. Qed.

Hint Resolve res_related_break_hint : js_ljs.
Hint Resolve res_related_continue_hint : js_ljs.

Ltac init_ctx_lookup :=
    eapply fast_string_assoc_mem;
    LjsInitEnv.ctx_compute;
    reflexivity.

Ltac ljs_abort := match goal with
    | H : L.abort (L.out_ter _ (L.res_value _)) |- _ => 
        let H1 := fresh "H" in 
        solve [invert H as H1; inverts H1]
    end.

Ltac inv_ljs_in H :=
    inverts red_exprh H; try ljs_abort; tryfalse.

Ltac inv_fwd_ljs_in H :=
    (inverts red_exprh H; try ljs_abort; tryfalse); [idtac].

Inductive inv_ljs_stop : L.ext_expr -> Prop := red_exprh_no_invert_intro : forall ee, inv_ljs_stop ee.

Ltac inv_ljs_stop ee := let STOP := fresh "STOP" in lets STOP : red_exprh_no_invert_intro ee.
 
Ltac ljs_check_top ee :=
    match eval hnf in (L.out_of_ext_expr ee) with
    | Some (L.out_ter _ ?r) => not is_var r
    | None => idtac
    end.

Ltac with_top_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        ljs_check_top ee;
        unfold js_expr_to_ljs, js_stat_to_ljs in H; simpl in H;
        match ee with 
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *) 
        | _ => is_hyp (inv_ljs_stop ee); fail 1
        | _ => T H
        end
    end.

Ltac with_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        unfold js_expr_to_ljs, js_stat_to_ljs in H; simpl in H;
        match ee with 
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *) 
        | _ => is_hyp (inv_ljs_stop ee); fail 1
        | _ => T H
        end
    end.

Ltac with_internal_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        unfold js_expr_to_ljs, js_stat_to_ljs in H; simpl in H;
        match ee with 
        | L.expr_basic _ => fail 1
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *)  
        | _ => is_hyp (inv_ljs_stop ee); fail 1
        | _ => T H
        end
    end.

Ltac inv_ljs := with_red_exprh inv_ljs_in.

Ltac inv_internal_ljs := with_internal_red_exprh inv_ljs_in.

Ltac inv_fwd_ljs := with_red_exprh inv_fwd_ljs_in.

Ltac inv_internal_fwd_ljs := with_internal_red_exprh inv_fwd_ljs_in.

Ltac inv_top_fwd_ljs := with_top_red_exprh inv_fwd_ljs_in.

Ltac inv_literal_ljs := 
    let H := match goal with
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_empty) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_true) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_false) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_null) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_undefined) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic (L.expr_number _)) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic (L.expr_string _)) _ |- _ => constr:H
    end in inverts red_exprh H.

Ltac unfold_concl := 
    unfold concl_ext_expr_value, concl_ext_expr_resvalue, concl_expr_getvalue, 
        concl_stat, concl_spec.
 
Tactic Notation "unfold_concl" "in" hyp(H) := 
    unfold concl_ext_expr_value, concl_ext_expr_resvalue, concl_expr_getvalue, 
        concl_stat, concl_spec in H. 

Ltac js_ljs_false_invert := match goal with 
    | H : J.abort_intercepted_expr _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_stat _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_spec _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_stat (J.stat_label_1 _ _) |- _ => 
        solve [let H' := fresh "H" in inverts H as H'; [discriminate H' || injects H']; tryfalse]
    | H : J.res_is_normal _ |- _ => inverts H
    end.

Hint Extern 10 => js_ljs_false_invert : js_ljs.
Hint Extern 10 (~_) => solve [intro; js_ljs_false_invert] : js_ljs. 

Ltac js_abort_rel_contr := match goal with
    | Ha : J.abort (J.out_ter ?jst ?x), Hr : res_related _ ?jst _ ?x (L.res_value _) |- _ =>
        let Hisn := fresh "Hisn" in
        inverts Ha as Hisn; inverts Hr; unfold J.res_is_normal, J.res_type in Hisn; false
    end.

Hint Extern 10 => js_abort_rel_contr : js_ljs.
 
Hint Extern 1 (J.regular_unary_op _) =>
    solve [let H := fresh "H" in intro H; unfolds in H; destruct_hyp H; inverts H] : js_ljs.

Tactic Notation "autoforwards" simple_intropattern(I) ":" constr(E) :=
    (forwards I : E; try eassumption; try omega); [idtac].

Ltac destr_concl := match goal with
    | H : concl_spec _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_stat _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_ext_expr_value _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_ext_expr_resvalue _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_expr_getvalue _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    end.

Tactic Notation "eauto_js" integer(k) := eauto k with js_ljs bag nocore xcore.

Tactic Notation "eauto_js" := eauto_js 5.

Tactic Notation "debug" "eauto_js" integer(k) := debug eauto k with js_ljs bag nocore xcore.

Tactic Notation "debug" "eauto_js" := debug eauto_js 5.

(* TODO move *)
Ltac jauto_set_slim :=
  intros; jauto_set_hyps;
  intros; jauto_set_goal.

Tactic Notation "jauto_js" integer(k) := 
    repeat destr_concl; jauto_set_slim; eauto with js_ljs bag nocore xcore; 
    repeat (try unfold_concl; jauto_set_slim; eauto k with js_ljs bag nocore xcore).

Tactic Notation "jauto_js" := jauto_js 5.

Ltac solve_jauto_js := solve [jauto_js 50].

Ltac ijauto_js := repeat intuition jauto_js.

Ltac solve_ijauto_js := solve [ijauto_js; solve_jauto_js].

Ltac cases_if_auto_js :=
    let Hif := fresh "Hif" in 
    first [case_if as Hif; [try solve [destruct_hyp Hif; tryfalse] | try solve [false; apply Hif; eauto_js]] 
          |case_if as Hif; [idtac]].

Hint Extern 11 => cases_if_auto_js; [idtac] : js_ljs.

(* TODO move *)
Lemma overwrite_value_if_empty_assoc : assoc L.overwrite_value_if_empty.
Proof.
    intros v1 v2 v3. destruct v3; reflexivity.
Qed.

Lemma overwrite_value_if_empty_left_empty : 
    neutral_l L.overwrite_value_if_empty L.value_empty.
Proof.
    intros v. destruct v; reflexivity.
Qed.

Lemma overwrite_value_if_empty_right_empty : 
    neutral_r L.overwrite_value_if_empty L.value_empty.
Proof.
    intros v. reflexivity.
Qed.

Lemma res_overwrite_value_if_empty_lemma : forall jrv jr,
    J.res_overwrite_value_if_empty jrv jr = 
        J.res_intro (J.res_type jr) (J.res_value (J.res_overwrite_value_if_empty jrv jr)) (J.res_label jr).
Proof.
    intros.
    unfold J.res_overwrite_value_if_empty.
    cases_if; substs; destruct jr;
    reflexivity.    
Qed.

Definition resvalue_overwrite_value_if_empty jrv1 jrv2 :=
    ifb jrv2 = J.resvalue_empty then jrv1 else jrv2.

Lemma resvalue_overwrite_value_if_empty_lemma : forall jrv1 jrv2 jrt jl,
    J.res_value (J.res_overwrite_value_if_empty jrv1 (J.res_intro jrt jrv2 jl)) =
        resvalue_overwrite_value_if_empty jrv1 jrv2.
Proof.
    introv. 
    unfold J.res_overwrite_value_if_empty.
    cases_if; substs; unfold resvalue_overwrite_value_if_empty; cases_if; reflexivity.
Qed.

Lemma resvalue_overwrite_value_if_empty_hint1 : forall jr jrv,
    (If J.res_value jr <> J.resvalue_empty then J.res_value jr else jrv) =
        J.res_value (J.res_overwrite_value_if_empty jrv jr).
Proof.
    intros. unfolds J.res_overwrite_value_if_empty. 
    repeat cases_if; destruct jr; reflexivity. 
Qed.

Hint Rewrite resvalue_overwrite_value_if_empty_lemma : js_ljs.
Hint Rewrite resvalue_overwrite_value_if_empty_hint1 : js_ljs.

Hint Extern 20 => progress autorewrite with js_ljs : js_ljs.

Lemma resvalue_related_overwrite_if_empty : forall BR jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    resvalue_related BR 
        (resvalue_overwrite_value_if_empty jrv1 jrv2) 
        (L.overwrite_value_if_empty v1 v2).
Proof.
    introv Hrel1 Hrel2.
    unfold resvalue_overwrite_value_if_empty.
    cases_if; substs. 
    (* empty *)
    inverts Hrel2.
    assumption.
    (* nonempty *)
    destruct jrv2;
    inverts Hrel2 as Hvrel2; tryfalse.
    inverts Hvrel2; jauto_js.
Qed.

Lemma resvalue_related_res_overwrite_if_empty : forall BR jrv1 jrv2 v1 v2 jrt jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    resvalue_related BR 
        (J.res_value (J.res_overwrite_value_if_empty jrv1 (J.res_intro jrt jrv2 jl))) 
        (L.overwrite_value_if_empty v1 v2).
Proof.
    introv Hrel1 Hrel2.
    rewrite resvalue_overwrite_value_if_empty_lemma.
    eauto using resvalue_related_overwrite_if_empty.
Qed.

Lemma res_related_value_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_normal jrv2))
        (L.res_value (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_normal. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma res_related_break_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2 s jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    s = E.js_label_to_ejs "%break" jl ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_intro J.restype_break jrv2 jl))
        (L.res_break s (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2 Hs. substs. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_break. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma res_related_continue_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2 s jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    s = E.js_label_to_ejs "%continue" jl ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_intro J.restype_continue jrv2 jl))
        (L.res_break s (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2 Hs. substs. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_continue. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma js_res_overwrite_value_if_empty_lemma : forall jrv jrt jv jl,
    J.res_overwrite_value_if_empty jrv (J.res_intro jrt (J.resvalue_value jv) jl) = 
        (J.res_intro jrt (J.resvalue_value jv) jl).
Proof.
    introv.
    unfold J.res_overwrite_value_if_empty. cases_if. reflexivity.
Qed.

Hint Rewrite js_res_overwrite_value_if_empty_lemma : js_ljs.

Lemma res_related_return_overwrite_if_empty : forall BR jst st jv2 v1 v2,
    value_related BR jv2 v2 ->
    res_related BR jst st 
        (J.res_intro J.restype_return (J.resvalue_value jv2) J.label_empty)
        (L.res_break "%ret" (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel2. 
    eapply res_related_return.
    inverts Hrel2; 
    unfolds L.overwrite_value_if_empty;
    jauto_js.
Qed.

Hint Resolve resvalue_related_overwrite_if_empty : js_ljs.
Hint Resolve res_related_value_overwrite_if_empty : js_ljs.
Hint Resolve res_related_break_overwrite_if_empty : js_ljs.
Hint Resolve res_related_continue_overwrite_if_empty : js_ljs.
Hint Resolve res_related_return_overwrite_if_empty : js_ljs.

Lemma res_related_invert_continue : forall BR jst st jr jl v,
    res_related BR jst st jr (L.res_break (E.js_label_to_ejs "%continue" jl) v) ->
    exists jrv,
    jr = J.res_intro J.restype_continue jrv jl /\
    resvalue_related BR jrv v.
Proof.
    introv Hrel.
    inverts Hrel.
    destruct jl; destruct jl0; repeat injects; tryfalse; eauto.
Qed.

Lemma res_related_invert_break : forall BR jst st jr jl v,
    res_related BR jst st jr (L.res_break (E.js_label_to_ejs "%break" jl) v) ->
    exists jrv,
    jr = J.res_intro J.restype_break jrv jl /\
    resvalue_related BR jrv v.
Proof.
    introv Hrel.
    inverts Hrel.
    destruct jl; destruct jl0; repeat injects; tryfalse; eauto.
Qed.

Ltac res_related_invert :=
    match goal with
    | H : res_related ?BR ?jst ?st ?jr ?r |- _ =>
(*      match goal with H1 : resvalue_related BR jst st _ _ |- _ => fail 2 | _ => idtac end; *)
        is_var jr; (* TODO better condition *)
        match r with
        | L.res_break (E.js_label_to_ejs "%continue" _) _ => 
            lets (?jrv&?H1&?H2) : (res_related_invert_continue H); subst jr
        | L.res_break (E.js_label_to_ejs "%break" _) _ => 
            lets (?jrv&?H1&?H2) : (res_related_invert_break H); subst jr
        | _ => inverts keep H 
        end
    | H : res_related ?BR ?jst ?st ?jr ?r |- _ =>
        is_var r; inverts keep H
    end. 

Ltac resvalue_related_only_invert :=
    match goal with
    | H : resvalue_related _ ?jrv ?v |- _ =>
        let H1 := fresh "H" in
        (is_var jrv || is_var v); inverts keep H as H1; try (inverts keep H1; [idtac])
    end.

Ltac resvalue_related_invert :=
    match goal with
    | H : resvalue_related _ ?jrv ?v |- _ =>
        let H1 := fresh "H" in
        (is_var jrv || is_var v); inverts keep H as H1; inverts keep H1
    end.

(* workaround *)
Lemma stat_block_1_hint : forall (S0 S : JsSyntax.state) (C : JsSyntax.execution_ctx)
         (t : JsSyntax.stat) jrv jo jo1,
       J.red_stat S C (J.stat_basic t) jo1 ->
       J.red_stat S C (J.stat_block_2 jrv jo1) jo ->
       J.red_stat S0 C (J.stat_block_1
            (J.out_ter S (J.res_intro J.restype_normal jrv J.label_empty)) t) jo.
Proof. intros. fold (J.res_normal jrv). jauto_js. Qed.
Hint Resolve stat_block_1_hint : js_ljs.

Lemma label_set_mem_lemma : forall jl jls, Mem jl jls -> J.label_set_mem jl jls.
Proof.
    introv Hmem.
    unfolds.
    rew_refl.
    assumption.
Qed.

Lemma res_label_in_lemma : forall jl jrt jrv jls, 
    Mem jl jls -> J.res_label_in (J.res_intro jrt jrv jl) jls.
Proof.
    introv Hmem.
    unfolds.
    auto using label_set_mem_lemma.
Qed.

Lemma label_set_mem_inv_lemma : forall jl jls, J.label_set_mem jl jls -> Mem jl jls.
Proof.
    introv Hjls.
    unfolds in Hjls.
    rew_refl in Hjls.
    assumption.
Qed.

Lemma res_label_in_inv_lemma : forall jl jrt jrv jls,
    J.res_label_in (J.res_intro jrt jrv jl) jls -> Mem jl jls.
Proof.
    introv Hmem.
    unfolds in Hmem.
    auto using label_set_mem_inv_lemma.
Qed.

Hint Resolve res_label_in_inv_lemma : js_ljs.
Hint Resolve res_label_in_lemma : js_ljs.

(* HERE START PROOFS *)

Lemma type_related_lemma : forall BR jv v,
    value_related BR jv v ->
    type_related (J.type_of jv) (L.value_type v).
Proof.
    introv Hvrel.
    destruct Hvrel; eauto_js.
Qed.

(* Lemmas about invariants *)

Lemma heaps_bisim_consistent_rnoghost_obj : forall BR jst st,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_rnoghost_obj BR st.
Proof.
    introv Hbic Hbi.
    eapply heaps_bisim_consistent_rnoghost; try eauto_js.
Qed.

Lemma heaps_bisim_consistent_rnoghost_env : forall BR jst st,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_rnoghost_env BR st.
Proof.
    introv Hbic Hbi.
    eapply heaps_bisim_consistent_rnoghost; try eauto_js.
Qed.

Lemma heaps_bisim_consistent_rfun_obj : forall BR jst st,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_rfun_obj BR.
Proof.
    introv Hbic Hbi1 Hbi2.
    lets Hx : heaps_bisim_consistent_rfun Hbic Hbi1 Hbi2 ___.
    eauto_js. eauto_js.
    injects. reflexivity.
Qed.

Lemma heaps_bisim_consistent_rfun_env : forall BR jst st,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_rfun_env BR.
Proof.
    introv Hbic Hbi1 Hbi2.
    lets Hx : heaps_bisim_consistent_rfun Hbic Hbi1 Hbi2 ___.
    eauto_js. eauto_js.
    injects. reflexivity.
Qed.

Lemma heaps_bisim_consistent_store_incl_preserved : forall BR jst st st',
    st \c st' ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR jst st'.
Proof.
    introv Hni Hbi.
    inverts Hbi.
    constructor; auto.

    introv Hrel Hjb Hlb.
    lets Hx : heaps_bisim_consistent_rnoghost Hrel ___. eauto_js.
    eapply heaps_bisim_consistent_bisim_obj; try eassumption. 
    apply index_binds in Hx.
    destruct Hx as (?obj&Hb1).
    lets Hb2 : (incl_binds _ _ _ _ Hni Hb1). 
    binds_determine. assumption.

    introv Hrel Hjb Hlb.
    lets Hx : heaps_bisim_consistent_rnoghost Hrel ___. eauto_js.
    eapply heaps_bisim_consistent_bisim_env; try eassumption. 
    apply index_binds in Hx.
    destruct Hx as (?obj&Hb1).
    lets Hb2 : (incl_binds _ _ _ _ Hni Hb1). 
    binds_determine. assumption.

    introv Hrel Hbinds.
    lets Hx : heaps_bisim_consistent_rnoghost Hrel ___. eauto_js.
    applys heaps_bisim_consistent_getter_proxy; try eassumption.
    apply index_binds in Hx.
    destruct Hx as (?obj&Hb1).
    lets Hb2 : (incl_binds _ _ _ _ Hni Hb1). 
    binds_determine. assumption.

    introv Hrel Hbinds.
    lets Hx : heaps_bisim_consistent_rnoghost Hrel ___. eauto_js.
    applys heaps_bisim_consistent_setter_proxy; try eassumption.
    apply index_binds in Hx.
    destruct Hx as (?obj&Hb1).
    lets Hb2 : (incl_binds _ _ _ _ Hni Hb1). 
    binds_determine. assumption.

    introv Hrel Hbinds.
    lets Hx : heaps_bisim_consistent_rnoghost Hrel ___. eauto_js.
    applys heaps_bisim_consistent_iarray; try eassumption.
    apply index_binds in Hx.
    destruct Hx as (?obj&Hb1).
    lets Hb2 : (incl_binds _ _ _ _ Hni Hb1). 
    binds_determine. assumption.

    unfolds heaps_bisim_rnoghost.
    prove_bag.
Qed.

Hint Resolve heaps_bisim_consistent_store_incl_preserved : js_ljs.

Lemma ctx_parent_ok_store_incl_preserved : forall BR st st',
    st \c st' ->
    ctx_parent_ok BR st ->
    ctx_parent_ok BR st'.
Proof.
    introv Hni Hok Hf.
    specializes Hok Hf.
    destruct_hyp Hok.
    jauto_js. 
Qed.

Hint Resolve ctx_parent_ok_store_incl_preserved : js_ljs.

Lemma state_invariant_store_incl_preserved : forall BR jst st st',
    st \c st' ->
    state_invariant BR jst st ->
    state_invariant BR jst st'.
Proof.
    introv Hni Hinv.
    inverts Hinv.
    constructor; jauto_js.
Qed.

(* Hint Resolve state_invariant_store_incl_preserved : js_ljs. *)
(*
Hint Extern 4 (state_invariant _ _ ?st') =>
    match goal with
    | H : state_invariant _ _ ?st |- _ =>
        not constr_eq st st';
        let Hsub := fresh "H" in
        asserts Hsub : (st \c st'); [prove_bag | applys state_invariant_store_incl_preserved Hsub; clear Hsub]
    end : js_ljs.
*)

Lemma includes_init_ctx_incl_preserved : forall c c',
    c' \c c ->
    includes_init_ctx c ->
    includes_init_ctx c'.
Proof.
    unfolds includes_init_ctx.
    prove_bag.
Qed.

Hint Resolve includes_init_ctx_incl_preserved : js_ljs.

Lemma execution_ctx_related_incl_preserved : forall BR jc c c',
    c' \c c ->
    execution_ctx_related BR jc c ->
    execution_ctx_related BR jc c'.
Proof.
    introv Hincl Hrel.
    inverts Hrel.
    constructor; jauto_js.
Qed.

Hint Resolve execution_ctx_related_incl_preserved : js_ljs.

Lemma prealloc_in_ctx_incl_preserved : forall BR c c',
    c' \c c ->
    prealloc_in_ctx BR c ->
    prealloc_in_ctx BR c'.
Proof.
    introv Hincl Hpre.
    unfolds prealloc_in_ctx.
    prove_bag.
Qed.

Hint Resolve prealloc_in_ctx_incl_preserved : js_ljs.

Lemma global_env_record_exists_ctx_incl_preserved : forall BR c c',
    c' \c c ->
    global_env_record_exists BR c ->
    global_env_record_exists BR c'.
Proof.
    introv Hincl Hpre.
    unfolds global_env_record_exists.
    prove_bag.
Qed.

Hint Resolve global_env_record_exists_ctx_incl_preserved : js_ljs.

Lemma context_invariant_ctx_incl_preserved : forall BR jc c c',
    c' \c c ->
    context_invariant BR jc c ->
    context_invariant BR jc c'.
Proof.
    introv Hincl Hinv.
    inverts Hinv.
    constructor; jauto_js.
Qed.

(* Hint Resolve state_invariant_ctx_incl_preserved : js_ljs. *)
Hint Extern 4 (context_invariant _ _ ?c') =>
    match goal with
    | H : context_invariant _ _ ?c |- _ =>
        not constr_eq c c';
        let Hsub := fresh "H" in
        asserts Hsub : (c' \c c); [prove_bag | applys context_invariant_ctx_incl_preserved Hsub; clear Hsub]
    end : js_ljs.

Section prefixes.

Local Open Scope char_scope.

Lemma init_ctx_percent_prefix : forall v s,
    binds LjsInitEnv.init_ctx s v -> exists s', s = String "%" s'.
Proof.
    introv Hmem.
(* TODO faster inversion
    repeat (inverts Hmem as Hmem; [skip | idtac]).
*)
    skip.
Qed.

Lemma prealloc_in_ctx_percent_prefix : forall jpre s,
    Mem (jpre, s) prealloc_in_ctx_list -> exists s', s = String "%" s'.
Proof.
    introv Hmem.
(* TODO faster
    repeat (inverts Hmem as Hmem; [eexists; reflexivity | idtac]).
    inverts Hmem.
*)
    skip.
Qed.

Lemma execution_ctx_related_add_nodollar_id_preserved : forall BR jc c s v ch,
    ch <> "$" ->
    execution_ctx_related BR jc c ->
    execution_ctx_related BR jc (c \(String ch s := v)).
Proof.
    introv Hdif Hrel.
    inverts Hrel.
    constructor;
    introv Hbinds; rew_binds_eq in Hbinds; destruct_hyp Hbinds; 
    try (introv Hbinds'; rew_binds_eq in Hbinds'; destruct_hyp Hbinds');
    tryfalse; eauto.
Qed.

Lemma includes_init_ctx_add_nopercent_id_preserved : forall c s v ch,
    ch <> "%" ->
    includes_init_ctx c ->
    includes_init_ctx (c \(String ch s := v)).
Proof. 
    unfolds includes_init_ctx.
    introv Hdif Hii Hbinds Hmem.
    lets (s'&EQs') : init_ctx_percent_prefix Hmem.
    substs.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds; tryfalse; eauto.
Qed.

Lemma prealloc_in_ctx_add_nopercent_id_preserved : forall BR c s v ch,
    ch <> "%" ->
    prealloc_in_ctx BR c ->
    prealloc_in_ctx BR (c \(String ch s := v)).
Proof.
    unfolds prealloc_in_ctx.
    introv Hdif Hpre Hmem Hbinds.
    lets (s'&EQs') : prealloc_in_ctx_percent_prefix Hmem. 
    substs.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds; tryfalse; eauto.
Qed.

Lemma global_env_record_exists_add_nopercent_id_preserved : forall BR c s v ch,
    ch <> "%" ->
    global_env_record_exists BR c ->
    global_env_record_exists BR (c \(String ch s := v)).
Proof.
    unfolds global_env_record_exists.
    introv Hdif Hgenv Hbinds.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds; tryfalse; eauto.
Qed.

Hint Resolve execution_ctx_related_add_nodollar_id_preserved : js_ljs.
Hint Resolve includes_init_ctx_add_nopercent_id_preserved : js_ljs.
Hint Resolve prealloc_in_ctx_add_nopercent_id_preserved : js_ljs.
Hint Resolve global_env_record_exists_add_nopercent_id_preserved : js_ljs.

Lemma context_invariant_add_nopercent_nodollar_id_preserved : forall BR jc c s v ch,
    context_invariant BR jc c->
    ch <> "%" -> ch <> "$" ->
    context_invariant BR jc (c \(String ch s := v)).
Proof.
    introv Hinv Hdif1 Hdif2.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Lemma execution_ctx_related_unadd_nodollar_id_preserved : forall BR jc c s v ch,
    ch <> "$" ->
    execution_ctx_related BR jc (c \(String ch s := v)) ->
    execution_ctx_related BR jc c.
Proof.
    introv Hdif Hrel.
    inverts Hrel.
    constructor;
    introv Hbinds;
    prove_bag. 
Qed.

Lemma includes_init_ctx_unadd_nopercent_id_preserved : forall c s v ch,
    ch <> "%" ->
    includes_init_ctx (c \(String ch s := v)) ->
    includes_init_ctx c.
Proof. 
    unfolds includes_init_ctx.
    introv Hdif Hii Hbinds Hmem.
    lets (s'&EQs') : init_ctx_percent_prefix Hmem.
    substs.
    eapply Hii; [idtac | eapply Hmem].
    rew_binds_eq.
    eauto.
Qed.

Lemma prealloc_in_ctx_unadd_nopercent_id_preserved : forall BR c s v ch,
    ch <> "%" ->
    prealloc_in_ctx BR (c \(String ch s := v)) ->
    prealloc_in_ctx BR c.
Proof.
    unfolds prealloc_in_ctx.
    introv Hdif Hpre Hmem Hbinds.
    lets (s'&EQs') : prealloc_in_ctx_percent_prefix Hmem. 
    substs.
    eapply Hpre. eapply Hmem.
    rew_binds_eq.
    eauto.
Qed.

Lemma global_env_record_exists_unadd_nopercent_id_preserved : forall BR c s v ch,
    ch <> "%" ->
    global_env_record_exists BR (c \(String ch s := v)) ->
    global_env_record_exists BR c.
Proof.
    unfolds global_env_record_exists.
    introv Hdif Hgenv Hbinds.
    apply Hgenv.
    rew_binds_eq.
    eauto.
Qed.

Hint Resolve execution_ctx_related_unadd_nodollar_id_preserved : js_ljs.
Hint Resolve includes_init_ctx_unadd_nopercent_id_preserved : js_ljs.
Hint Resolve prealloc_in_ctx_unadd_nopercent_id_preserved : js_ljs.
Hint Resolve global_env_record_exists_unadd_nopercent_id_preserved : js_ljs.

Lemma context_invariant_unadd_nopercent_nodollar_id_preserved : forall BR jc c s v ch,
    context_invariant BR jc (c \(String ch s := v)) ->
    ch <> "%" -> ch <> "$" ->
    context_invariant BR jc c.
Proof.
    introv Hinv Hdif1.
    inverts Hinv.
    constructor; jauto_js.
Qed.

End prefixes.

(* because coq does not accept global in sections *)
Hint Resolve execution_ctx_related_add_nodollar_id_preserved : js_ljs.
Hint Resolve includes_init_ctx_add_nopercent_id_preserved : js_ljs.
Hint Resolve prealloc_in_ctx_add_nopercent_id_preserved : js_ljs.
Hint Resolve global_env_record_exists_add_nopercent_id_preserved : js_ljs.
(*
Hint Resolve execution_ctx_related_unadd_nodollar_id_preserved : js_ljs.
Hint Resolve includes_init_ctx_unadd_nopercent_id_preserved : js_ljs.
Hint Resolve prealloc_in_ctx_unadd_nopercent_id_preserved : js_ljs.
Hint Resolve global_env_record_exists_unadd_nopercent_id_preserved : js_ljs.
*)
Hint Resolve context_invariant_add_nopercent_nodollar_id_preserved : js_ljs.
(* Hint Resolve state_invariant_unadd_nopercent_nodollar_id_preserved : js_ljs. *)

Lemma execution_ctx_related_union_preserved : forall BR jc c c',
    execution_ctx_related BR jc c ->
    execution_ctx_related BR jc c' ->
    execution_ctx_related BR jc (c \u c').
Proof.
    introv Hrel1 Hrel2.
    inverts Hrel1.
    inverts Hrel2.
    constructor;
    introv Hbinds;
    rewrite binds_union_eq in Hbinds;
    destruct_hyp Hbinds; eauto.
Qed.

Hint Resolve execution_ctx_related_union_preserved : js_ljs.

Lemma includes_init_ctx_union_preserved : forall c c',
    includes_init_ctx c ->
    includes_init_ctx c' -> 
    includes_init_ctx (c \u c').
Proof.
    introv Hii1 Hii2.
    unfolds includes_init_ctx.
    introv Hbinds Hmem.
    rewrite binds_union_eq in Hbinds.
    destruct_hyp Hbinds;
    prove_bag.
Qed.

Hint Resolve includes_init_ctx_union_preserved : js_ljs.

Lemma prealloc_in_ctx_union_preserved : forall BR c c',
    prealloc_in_ctx BR c ->
    prealloc_in_ctx BR c' -> 
    prealloc_in_ctx BR (c \u c').
Proof.
    introv Hpre1 Hpre2.
    unfolds prealloc_in_ctx.
    introv Hmem Hbinds.
    rewrite binds_union_eq in Hbinds.
    destruct_hyp Hbinds; prove_bag.
Qed.

Hint Resolve prealloc_in_ctx_union_preserved : js_ljs.

Lemma global_env_record_exists_union_preserved : forall BR c c',
    global_env_record_exists BR c ->
    global_env_record_exists BR c' -> 
    global_env_record_exists BR (c \u c').
Proof.
    unfolds prealloc_in_ctx.
    introv Hgenv1 Hgenv2 Hbinds.
    rewrite binds_union_eq in Hbinds.
    destruct_hyp Hbinds; prove_bag.
Qed.

Hint Resolve global_env_record_exists_union_preserved : js_ljs.

Lemma context_invariant_union_preserved : forall BR jc c c',
    context_invariant BR jc c ->
    context_invariant BR jc c' ->
    context_invariant BR jc (c \u c').
Proof.
    introv Hinv1 Hinv2.
    inverts Hinv1.
    inverts Hinv2.
    constructor; jauto_js.
Qed.

Hint Resolve context_invariant_union_preserved : js_ljs.

Lemma includes_init_ctx_init_ctx : forall c,
    includes_init_ctx LjsInitEnv.init_ctx.
Proof.
    introv Hsub.
    unfolds.
    introv Hb1 Hb2.
    determine.
    reflexivity.
Qed.

Hint Resolve includes_init_ctx_init_ctx : js_ljs.

Lemma execution_ctx_related_init_ctx : forall BR jc,
    execution_ctx_related BR jc LjsInitEnv.init_ctx.
Proof.
    constructor.
Admitted. (* TODO *)

Hint Resolve execution_ctx_related_init_ctx : js_ljs.

Lemma global_env_record_exists_init_ctx : forall BR,
    initBR \c BR ->
    global_env_record_exists BR LjsInitEnv.init_ctx.
Proof.
Admitted. (* TODO *)

Hint Resolve global_env_record_exists_init_ctx : js_ljs.

Lemma prealloc_in_ctx_init_ctx : forall BR,
    initBR \c BR ->
    prealloc_in_ctx BR LjsInitEnv.init_ctx.
Proof.
Admitted. (* TODO *)

Hint Resolve prealloc_in_ctx_init_ctx : js_ljs.

Lemma context_invariant_replace_ctx_sub_init : forall BR jc c c',
    c' \c LjsInitEnv.init_ctx -> 
    context_invariant BR jc c ->
    context_invariant BR jc c'.
Proof.
    introv Hii Hinv.
    inverts Hinv.
    constructor; jauto_js.
Qed.

(*Hint Resolve context_invariant_replace_ctx_sub_init : js_ljs.*)

Ltac sub_helper BR1 BR2 f :=
    not constr_eq BR1 BR2;
    let Hsub := fresh "H" in
    asserts Hsub : (BR1 \c BR2); [prove_bag | idtac];
    applys f Hsub;
    clear Hsub.

Lemma value_related_bisim_incl_preserved : forall BR1 BR2 jv v,
    BR1 \c BR2 ->
    value_related BR1 jv v ->
    value_related BR2 jv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js. 
Qed.

(* Hint Resolve value_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (value_related ?BR2 _ _) => 
    match goal with 
    | H : value_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 value_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 value_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma values_related_bisim_incl_preserved : forall BR1 BR2 jvs vs,
    BR1 \c BR2 ->
    values_related BR1 jvs vs ->
    values_related BR2 jvs vs.
Proof.
    introv Hs Hrel.
    unfolds values_related.
    inductions jvs gen Hrel; inverts Hrel.
    eapply Forall2_nil.
    eapply Forall2_cons.
    eauto_js.
    eauto.
Qed.

(* Hint Resolve value_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (values_related ?BR2 _ _) => 
    match goal with 
    | H : values_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 values_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 values_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma option_value_related_bisim_incl_preserved : forall BR1 BR2 jov ov,
    BR1 \c BR2 ->
    option_value_related BR1 jov ov ->
    option_value_related BR2 jov ov.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

(* Hint Resolve option_value_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (option_value_related ?BR2 _ _) => 
    match goal with 
    | H : option_value_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 option_value_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 option_value_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma resvalue_related_bisim_incl_preserved : forall BR1 BR2 jrv v,
    BR1 \c BR2 ->
    resvalue_related BR1 jrv v ->
    resvalue_related BR2 jrv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

(* Hint Resolve resvalue_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (resvalue_related ?BR2 _ _) => 
    match goal with 
    | H : resvalue_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 resvalue_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 resvalue_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma res_related_bisim_incl_preserved : forall BR1 BR2 jst st jr r,
    BR1 \c BR2 ->
    res_related BR1 jst st jr r ->
    res_related BR2 jst st jr r.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

(* Hint Resolve res_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (res_related ?BR2 _ _ _ _) => 
    match goal with 
    | H : res_related ?BR1 _ _ _ _ |- _ => sub_helper BR1 BR2 res_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 res_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma env_records_exist_bisim_incl_preserved : forall BR1 BR2 jc,
    BR1 \c BR2 ->
    env_records_exist BR1 jc ->
    env_records_exist BR2 jc.
Proof.
    introv Hs Hex.
    inverts Hex. 
    constructor; introv Hmem.
    specializes env_record_exist_variable_env Hmem. destruct_hyp env_record_exist_variable_env. jauto_js.
    specializes env_record_exist_lexical_env Hmem. destruct_hyp env_record_exist_lexical_env. jauto_js.
Qed.

(* Hint Resolve env_records_exist_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (env_records_exist ?BR2 _) => 
    match goal with 
    | H : env_records_exist ?BR1 _ |- _ => sub_helper BR1 BR2 env_records_exist_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 env_records_exist_bisim_incl_preserved
    end 
    : js_ljs.

Lemma prealloc_in_ctx_bisim_incl_preserved : forall BR1 BR2 c,
    BR1 \c BR2 ->
    prealloc_in_ctx BR1 c ->
    prealloc_in_ctx BR2 c.
Proof.
    introv Hs Hpre.
    unfolds prealloc_in_ctx.
    introv Hmem Hbinds.
    specializes Hpre Hmem Hbinds.
    destruct_hyp Hpre.
    jauto_js.
Qed.

(* Hint Resolve prealloc_in_ctx_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (prealloc_in_ctx ?BR2 _) => 
    match goal with 
    | H : prealloc_in_ctx ?BR1 _ |- _ => sub_helper BR1 BR2 prealloc_in_ctx_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 prealloc_in_ctx_bisim_incl_preserved
    end 
    : js_ljs.

Lemma global_env_record_exists_bisim_incl_preserved : forall BR1 BR2 c,
    BR1 \c BR2 ->
    global_env_record_exists BR1 c ->
    global_env_record_exists BR2 c.
Proof.
    introv Hs Hpre.
    unfolds global_env_record_exists. 
    introv Hbinds.
    specializes Hpre Hbinds.
    destruct_hyp Hpre.
    jauto_js.
Qed.

(* Hint Resolve global_env_record_exists_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (global_env_record_exists ?BR2 _) => 
    match goal with 
    | H : global_env_record_exists ?BR1 _ |- _ => sub_helper BR1 BR2 global_env_record_exists_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 global_env_record_exists_bisim_incl_preserved
    end 
    : js_ljs.

Lemma lexical_env_related_bisim_incl_preserved : forall BR1 BR2 jlenv v,
    BR1 \c BR2 ->
    lexical_env_related BR1 jlenv v ->
    lexical_env_related BR2 jlenv v.
Proof.
    introv Hs Hpre.
    induction Hpre; jauto_js 6.
Qed.

(* Hint Resolve lexical_env_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (lexical_env_related ?BR2 _ _) => 
    match goal with 
    | H : lexical_env_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 lexical_env_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 lexical_env_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma execution_ctx_related_bisim_incl_preserved : forall BR1 BR2 jc c,
    BR1 \c BR2 ->
    execution_ctx_related BR1 jc c ->
    execution_ctx_related BR2 jc c.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor.
    introv Hbinds. specializes execution_ctx_related_this_binding Hbinds. jauto_js.
    jauto_js.
    introv Hbinds. specializes execution_ctx_related_lexical_env Hbinds. jauto_js.
Qed.

(* Hint Resolve execution_ctx_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (execution_ctx_related ?BR2 _ _) => 
    match goal with 
    | H : execution_ctx_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 execution_ctx_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 execution_ctx_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma decl_env_record_vars_related_bisim_incl_preserved : forall BR1 BR2 jder props,
    BR1 \c BR2 ->
    decl_env_record_vars_related BR1 jder props -> 
    decl_env_record_vars_related BR2 jder props.
Proof.
    introv Hs Hrel.
    unfolds decl_env_record_vars_related.
    intro s. specializes Hrel s.
    destruct_hyp Hrel; ijauto_js.
Qed.

(* Hint Resolve decl_env_record_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (decl_env_record_vars_related ?BR2 _ _) => 
    match goal with 
    | H : decl_env_record_vars_related ?BR1 _ _ |- _ => 
        sub_helper BR1 BR2 decl_env_record_vars_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 decl_env_record_vars_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma decl_env_record_related_bisim_incl_preserved : forall BR1 BR2 jder obj,
    BR1 \c BR2 ->
    decl_env_record_related BR1 jder obj -> 
    decl_env_record_related BR2 jder obj.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor; jauto_js.
Qed.

(* Hint Resolve decl_env_record_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (decl_env_record_related ?BR2 _ _) => 
    match goal with 
    | H : decl_env_record_related ?BR1 _ _ |- _ => 
        sub_helper BR1 BR2 decl_env_record_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 decl_env_record_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma object_env_record_related_bisim_incl_preserved : forall BR1 BR2 jptr b ptr obj,
    BR1 \c BR2 ->
    object_env_record_related BR1 jptr b ptr obj -> 
    object_env_record_related BR2 jptr b ptr obj.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor; jauto_js.
Qed.

(* Hint Resolve object_env_record_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (object_env_record_related ?BR2 _ _ _ _) => 
    match goal with 
    | H : object_env_record_related ?BR1 _ _ _ _ |- _ => 
        sub_helper BR1 BR2 object_env_record_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 object_env_record_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma env_record_related_bisim_incl_preserved : forall BR1 BR2 jer obj,
    BR1 \c BR2 ->
    env_record_related BR1 jer obj ->
    env_record_related BR2 jer obj.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    eapply env_record_related_decl; jauto_js.
    eapply env_record_related_object; jauto_js.
Qed.

(* Hint Resolve env_record_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (env_record_related ?BR2 _ _) => 
    match goal with 
    | H : env_record_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 env_record_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 env_record_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma usercode_context_invariant_bisim_incl_preserved : forall BR1 BR2 jle c,
    BR1 \c BR2 ->
    usercode_context_invariant BR1 jle c ->
    usercode_context_invariant BR2 jle c.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor; eauto_js.
Qed.

Hint Extern 4 (usercode_context_invariant ?BR2 _ _) => 
    match goal with 
    | H : usercode_context_invariant ?BR1 _ _ |- _ => 
        sub_helper BR1 BR2 usercode_context_invariant_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 usercode_context_invariant_bisim_incl_preserved
    end 
    : js_ljs.

Lemma usercode_related_bisim_incl_preserved : forall BR1 BR2 jfb is jle v,
    BR1 \c BR2 ->
    usercode_related BR1 jfb is jle v ->
    usercode_related BR2 jfb is jle v.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor; eauto_js.
Qed.

Hint Extern 4 (usercode_related ?BR2 _ _ _ _) => 
    match goal with 
    | H : usercode_related ?BR1 _ _ _ _ |- _ => sub_helper BR1 BR2 usercode_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 usercode_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma option_usercode_related_bisim_incl_preserved : forall BR1 BR2 ojfb ois ojle ov,
    BR1 \c BR2 ->
    option_usercode_related BR1 ojfb ois ojle ov ->
    option_usercode_related BR2 ojfb ois ojle ov.
Proof.
    introv Hs Hrel.
    inverts Hrel;
    constructor; eauto_js.
Qed.

Hint Extern 4 (option_usercode_related ?BR2 _ _ _ _) => 
    match goal with 
    | H : option_usercode_related ?BR1 _ _ _ _ |- _ => 
        sub_helper BR1 BR2 option_usercode_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 option_usercode_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma object_prim_related_bisim_incl_preserved : forall BR1 BR2 jobj obj,
    BR1 \c BR2 ->
    object_prim_related BR1 jobj obj ->
    object_prim_related BR2 jobj obj.
Proof.
    introv Hs Hrel.
    inverts Hrel.
    constructor; eauto_js. 
Qed.

(* Hint Resolve object_prim_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (object_prim_related ?BR2 _ _) => 
    match goal with 
    | H : object_prim_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 object_prim_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 object_prim_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma attributes_data_related_bisim_incl_preserved : forall BR1 BR2 jattrsd attrsd,
    BR1 \c BR2 ->
    attributes_data_related BR1 jattrsd attrsd ->
    attributes_data_related BR2 jattrsd attrsd.
Proof.
    introv Hs Hrel.
    inverts Hrel; constructor; jauto_js.
Qed.

(* Hint Resolve attributes_data_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (attributes_data_related ?BR2 _ _) => 
    match goal with 
    | H : attributes_data_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 attributes_data_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 attributes_data_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma attributes_accessor_related_bisim_incl_preserved : forall BR1 BR2 jattrsa attrsa,
    BR1 \c BR2 ->
    attributes_accessor_related BR1 jattrsa attrsa ->
    attributes_accessor_related BR2 jattrsa attrsa.
Proof.
    introv Hs Hrel.
    inverts Hrel; econstructor; jauto_js.
Qed.

(* Hint Resolve attributes_accessor_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (attributes_accessor_related ?BR2 _ _) => 
    match goal with 
    | H : attributes_accessor_related ?BR1 _ _ |- _ => 
        sub_helper BR1 BR2 attributes_accessor_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 attributes_accessor_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma attributes_related_bisim_incl_preserved : forall BR1 BR2 jattrs attrs,
    BR1 \c BR2 ->
    attributes_related BR1 jattrs attrs ->
    attributes_related BR2 jattrs attrs.
Proof.
    introv Hs Hrel.
    inverts Hrel; constructor; jauto_js.
Qed.

(* Hint Resolve attributes_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (attributes_related ?BR2 _ _) => 
    match goal with 
    | H : attributes_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 attributes_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 attributes_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma object_properties_related_bisim_incl_preserved : forall BR1 BR2 jprops props,
    BR1 \c BR2 ->
    object_properties_related BR1 jprops props ->
    object_properties_related BR2 jprops props.
Proof.
    introv Hs Hrel.
    unfolds object_properties_related.
    intro s. specializes Hrel s.
    destruct_hyp Hrel; ijauto_js.
Qed.

(* Hint Resolve object_properties_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (object_properties_related ?BR2 _ _) => 
    match goal with 
    | H : object_properties_related ?BR1 _ _ |- _ => 
        sub_helper BR1 BR2 object_properties_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 object_properties_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma object_related_bisim_incl_preserved : forall BR1 BR2 jobj obj,
    BR1 \c BR2 ->
    object_related BR1 jobj obj ->
    object_related BR2 jobj obj.
Proof. 
    introv Hs Hrel.
    inverts Hrel.
    constructor; jauto_js.
Qed.

(* Hint Resolve object_related_bisim_incl_preserved : js_ljs. *)
Hint Extern 4 (object_related ?BR2 _ _) => 
    match goal with 
    | H : object_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 object_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 object_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma context_invariant_bisim_incl_preserved : forall BR1 BR2 jc c,
    BR1 \c BR2 ->
    context_invariant BR1 jc c ->
    context_invariant BR2 jc c.
Proof.
    introv Hs Hinv.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Hint Extern 4 (context_invariant ?BR2 _ _) => 
    match goal with 
    | H : context_invariant ?BR1 _ _ |- _ => sub_helper BR1 BR2 context_invariant_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 context_invariant_bisim_incl_preserved
    end 
    : js_ljs.

Lemma ref_base_type_related_bisim_incl_preserved : forall BR1 BR2 jrbt v,
    BR1 \c BR2 ->
    ref_base_type_related BR1 jrbt v ->
    ref_base_type_related BR2 jrbt v.
Proof.
    introv Hs Hrel.
    inverts Hrel; eauto_js.
Qed.

Hint Extern 4 (ref_base_type_related ?BR2 _ _) => 
    match goal with 
    | H : ref_base_type_related ?BR1 _ _ |- _ => sub_helper BR1 BR2 ref_base_type_related_bisim_incl_preserved
    | H : ?BR1 \c BR2 |- _ => sub_helper BR1 BR2 ref_base_type_related_bisim_incl_preserved
    end 
    : js_ljs.

Lemma context_invariant_lexical_env_related : forall BR jc c v,
    context_invariant BR jc c ->
    binds c "$context" v ->
    lexical_env_related BR (J.execution_ctx_lexical_env jc) v.
Proof.
    introv Hinv Hbinds.
    eapply context_invariant_execution_ctx_related; eassumption.
Defined.
(*
Lemma value_related_add_fact_preserved : forall BR jv v f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    value_related BR jv v ->
    value_related (\{f} \u BR) jv v.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel; eauto_js.
Qed.

Hint Resolve value_related_add_fact_preserved : js_ljs.

Lemma option_value_related_add_fact_preserved : forall BR jov ov f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    option_value_related BR jov ov ->
    option_value_related (\{f} \u BR) jov ov.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel; eauto_js.
Qed.

Hint Resolve option_value_related_add_fact_preserved : js_ljs.

Lemma object_prim_related_add_fact_preserved : forall BR jobj obj f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    object_prim_related BR jobj obj ->
    object_prim_related (\{f} \u BR) jobj obj.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel.
    constructor; eauto_js.
Qed.

Hint Resolve object_prim_related_add_fact_preserved : js_ljs.

Lemma attributes_data_related_add_fact_preserved : forall BR jattrsd attrsd f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    attributes_data_related BR jattrsd attrsd ->
    attributes_data_related (\{f} \u BR) jattrsd attrsd.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel.
    constructor; eauto_js.
Qed.

Hint Resolve attributes_data_related_add_fact_preserved : js_ljs.

Lemma attributes_accessor_related_add_fact_preserved : forall BR jattrsa attrsa f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    attributes_accessor_related BR jattrsa attrsa ->
    attributes_accessor_related (\{f} \u BR) jattrsa attrsa.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel.
    econstructor; eauto_js.
Qed.

Hint Resolve attributes_accessor_related_add_fact_preserved : js_ljs.

Lemma attributes_related_add_fact_preserved : forall BR jattrs attrs f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    attributes_related BR jattrs attrs ->
    attributes_related (\{f} \u BR) jattrs attrs.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel; eauto_js.
Qed.

Hint Resolve attributes_related_add_fact_preserved : js_ljs.

Lemma object_properties_related_add_fact_preserved : forall BR jprops props f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    object_properties_related BR jprops props ->
    object_properties_related (\{f} \u BR) jprops props.
Proof.
    introv Hdif1 Hdif2 Hrel.
    unfolds object_properties_related.
    intro s. specializes Hrel s.
    destruct_hyp Hrel; intuition jauto_js 8.
Qed.

Hint Resolve object_properties_related_add_fact_preserved : js_ljs.

Lemma object_related_add_fact_preserved : forall BR jobj obj f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    object_related BR jobj obj ->
    object_related (\{f} \u BR) jobj obj.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel.
    constructor; eauto_js.
Qed.

Hint Resolve object_related_add_fact_preserved : js_ljs.

Lemma decl_env_record_vars_related_add_fact_preserved : forall BR jder props f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    decl_env_record_vars_related BR jder props ->
    decl_env_record_vars_related (\{f} \u BR) jder props.
Proof.
    introv Hdif1 Hdif2 Hrel.
    unfolds decl_env_record_vars_related.
    intro s. specializes Hrel s.
    destruct_hyp Hrel; intuition jauto_js 8.
Qed.

Hint Resolve decl_env_record_vars_related_add_fact_preserved : js_ljs.

Lemma env_record_related_add_fact_preserved : forall BR jer obj f,
    (forall jptr ptr, f <> fact_js_obj jptr ptr) ->
    (forall jeptr ptr, f <> fact_js_env jeptr ptr) ->
    env_record_related BR jer obj ->
    env_record_related (\{f} \u BR) jer obj.
Proof.
    introv Hdif1 Hdif2 Hrel.
    inverts Hrel; eauto_js.
Qed.

Hint Resolve env_record_related_add_fact_preserved : js_ljs.
*)
Lemma ctx_parent_ok_new_fact_preserved : forall BR st f,
    (forall ptr v, f <> fact_ctx_parent ptr v) ->
    ctx_parent_ok BR st ->
    ctx_parent_ok (\{f} \u BR) st.
Proof.
    introv Hfact Hcp Hpar.
    lets Hfact' : Hfact ptr v.
    asserts Hpar' : (fact_ctx_parent ptr v \in BR).
    rew_in_eq in Hpar. destruct_hyp Hpar; tryfalse. assumption.
    specializes Hcp Hpar'.
    destruct_hyp Hcp; jauto_js.
Qed.

Hint Resolve ctx_parent_ok_new_fact_preserved : js_ljs.

Lemma ctx_parent_ok_modify_state_preserved : forall BR st ptr obj,
    (forall v, ~fact_ctx_parent ptr v \in BR) ->
    ctx_parent_ok BR st ->
    ctx_parent_ok BR (st \(ptr := obj)).
Proof.
    introv Hneg Hcpar Hbs.
    destruct (classic (ptr = ptr0)). {
        substs. specializes Hneg Hbs. tryfalse.
    }
    lets Hx : Hcpar Hbs.
    destruct_hyp Hx.
    prove_bag 9.
Qed.

Lemma ctx_parent_ok_modify_object_preserved_lemma : forall BR st ptr jptr obj,
    heaps_bisim_rfun BR ->
    fact_js_obj jptr ptr \in BR ->
    ctx_parent_ok BR st ->
    ctx_parent_ok BR (st \(ptr := obj)).
Proof.
    introv Hrfun Hfact Hcpar Hbs.
    lets (jeptr&obj'&Hfact'&Hx) : Hcpar Hbs.
    destruct (classic (ptr = ptr0)). {
        substs.
        specializes Hrfun Hfact Hfact' ___; try eauto_js.
        tryfalse.
    }
    destruct_hyp Hx.
    exists jeptr obj'.
    prove_bag 6.
Qed.

Lemma ctx_parent_ok_modify_object_preserved : forall BR jst st ptr jptr obj,
    heaps_bisim_consistent BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    ctx_parent_ok BR st ->
    ctx_parent_ok BR (st \(ptr := obj)).
Proof.
    introv Hbisim. destruct Hbisim. eauto using ctx_parent_ok_modify_object_preserved_lemma.
Qed.

Hint Resolve ctx_parent_ok_modify_object_preserved : js_ljs.

Lemma object_prim_related_map_properties_preserved : forall BR jobj obj F,
    object_prim_related BR jobj obj ->
    object_prim_related BR (J.object_map_properties jobj F) obj.
Proof.
    introv Hprim. 
    inverts Hprim. destruct jobj.
    constructor; eauto. 
Qed.

Hint Resolve object_prim_related_map_properties_preserved : js_ljs.

Lemma object_related_map_properties_preserved : forall BR jobj obj F,
    object_prim_related BR jobj obj ->
    object_properties_related BR (F (J.object_properties_ jobj)) (L.object_properties obj) ->
    object_related BR (J.object_map_properties jobj F) obj.
Proof.
    introv Hrel1 Hrel2. destruct jobj. 
    constructor; jauto_js.
Qed.

Hint Resolve object_related_map_properties_preserved : js_ljs.

(*
Lemma object_prim_related_object_new : forall BR jv v s obj,
    L.object_class obj = s ->
    L.object_extensible obj ->
    L.object_proto obj = v ->
    ~index (L.object_internal obj) "primval" ->
    value_related BR jv v ->
    object_prim_related BR (J.object_new jv s) obj.
Proof.
    introv Hcl Hext Hpro Hprim Hrel.
    constructor.
    rewrite Hcl. reflexivity.
    rewrite Hext. reflexivity. 
    rewrite Hpro. assumption.
    eauto_js.
Qed.

Hint Resolve object_prim_related_object_new : js_ljs.
*)

Lemma object_properties_related_new : forall BR,
    object_properties_related BR \{} \{}.
Proof. introv. unfolds. introv. left. split; eauto_js. Qed.

Hint Resolve object_properties_related_new : js_ljs. 

Lemma object_properties_related_update : forall BR jprops props jattrs attrs s,
    attributes_related BR jattrs attrs ->
    object_properties_related BR jprops props ->
    object_properties_related BR (jprops \(s := jattrs)) (props \(s := attrs)).
Proof.
    introv Hrel1 Hrel2.
    unfolds object_properties_related. intro s'.
    tests Eq : (s' = s). 
    right. jauto_js.
    specializes Hrel2 s'.
    destruct_hyp Hrel2; eauto_js. 
    repeat rewrite index_update_diff_eq; eauto.
    right. do 2 eexists.
    repeat rewrite binds_update_diff_eq; eauto.
Qed.

Hint Resolve object_properties_related_update : js_ljs.

Lemma heaps_bisim_consistent_new_object_preserved : forall BR jst st jptr jobj ptr obj,
    ~index jst jptr ->
    ~index st ptr ->
    object_related (\{fact_js_obj jptr ptr} \u BR) jobj obj ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_js_obj jptr ptr} \u BR) (jst \(jptr:=jobj)) (st \(ptr:=obj)).
Proof.
    introv Hjnindex Hnindex Horel Hbisim.
    inverts Hbisim.
    asserts Hsub : (BR \c \{fact_js_obj jptr ptr} \u BR). jauto_js.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    rew_binds_eq in Hbinds1. 
    rew_binds_eq in Hbinds2. 
    apply case_classic_l in Hbi.
    destruct_hyp Hbi.
    injects.
    destruct_hyp Hbinds1; tryfalse.
    destruct_hyp Hbinds2; tryfalse.
    assumption.
    destruct_hyp Hbinds1;
    destruct_hyp Hbinds2.
    jauto_js.
    false. jauto_js.
    false. jauto_js.
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds1. 
    rew_binds_eq in Hbinds2. 
    destruct_hyp Hbinds2. 
    false. jauto_js.
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects.
    reflexivity.
    false; jauto_js.
    false; jauto_js.
    jauto_js.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; tryfalse.
    jauto_js.
    (* rfun *)
    introv Hbi1 Hbi2 Hfp1 Hfp2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects.
    reflexivity.
    inverts Hfp1. false; jauto_js.
    inverts Hfp2. false; jauto_js.
    jauto_js.
    (* ltotal_inl *)
    introv Hindex.
    rew_index_eq in Hindex.
    destruct_hyp Hindex.
    lets Hth : heaps_bisim_consistent_ltotal_obj Hindex. 
    destruct_hyp Hth. jauto_js. 
    jauto_js.
    (* ltotal_inr *)
    introv Hindex.
    rew_index_eq in Hindex.
    lets Hth : heaps_bisim_consistent_ltotal_env Hindex. 
    destruct_hyp Hth. jauto_js. 
    (* lnoghost_inl *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi.
    injects. jauto_js.
    jauto_js.
    (* lnoghost_inr *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_index_eq. 
    jauto_js.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi.
    inverts Hfp. jauto_js.
    jauto_js.
Qed.

Hint Resolve heaps_bisim_consistent_new_object_preserved : js_ljs.

Lemma heaps_bisim_consistent_new_env_record_preserved : forall BR jst st jeptr jer ptr obj,
    ~index jst jeptr ->
    ~index st ptr ->
    env_record_related (\{fact_js_env jeptr ptr} \u BR) jer obj ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_js_env jeptr ptr} \u BR) (jst \(jeptr:=jer)) (st \(ptr:=obj)).
Proof.
    introv Hjnindex Hnindex Horel Hbisim.
    inverts Hbisim.
    asserts Hsub : (BR \c \{fact_js_env jeptr ptr} \u BR). jauto_js.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds1. 
    rew_binds_eq in Hbinds2. 
    destruct_hyp Hbinds2. 
    false. jauto_js.
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    rew_binds_eq in Hbinds1. 
    rew_binds_eq in Hbinds2. 
    apply case_classic_l in Hbi.
    destruct_hyp Hbi.
    injects.
    destruct_hyp Hbinds1; tryfalse.
    destruct_hyp Hbinds2; tryfalse.
    assumption.
    destruct_hyp Hbinds1;
    destruct_hyp Hbinds2.
    jauto_js.
    false. jauto_js.
    false. jauto_js.
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    rew_binds_eq in Hbinds. 
    destruct_hyp Hbinds.
    false. jauto_js.
    jauto_js.
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; tryfalse.
    jauto_js.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects.
    reflexivity.
    false; jauto_js.
    false; jauto_js.
    jauto_js.
    (* rfun *)
    introv Hbi1 Hbi2 Hfp1 Hfp2.
    rew_in_eq in Hbi1.
    rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects.
    reflexivity.
    inverts Hfp1. false; jauto_js.
    inverts Hfp2. false; jauto_js.
    jauto_js.
    (* ltotal_inl *)
    introv Hindex.
    rew_index_eq in Hindex.
    lets Hth : heaps_bisim_consistent_ltotal_obj Hindex. 
    destruct_hyp Hth. jauto_js. 
    (* ltotal_inr *) 
    introv Hindex.
    rew_index_eq in Hindex.
    destruct_hyp Hindex.
    lets Hth : heaps_bisim_consistent_ltotal_env Hindex. 
    destruct_hyp Hth. jauto_js. 
    jauto_js.
    (* lnoghost_inl *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_index_eq. 
    jauto_js.
    (* lnoghost_inr *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi.
    injects. jauto_js.
    jauto_js.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi.
    inverts Hfp. jauto_js.
    jauto_js.
Qed.

Hint Resolve heaps_bisim_consistent_new_env_record_preserved : js_ljs.

(* TODO move *)
Ltac binds_inv H :=
    repeat rewrite from_list_update, from_list_empty in H; (* TODO *)
    rew_bag_simpl in H;
    let rec f H :=
        match type of H with
        | binds ?M ?x ?v2 =>
            let He := fresh "H" in
            match M with
                | ?v => 
                    is_var v;
                    match goal with
                    | Heq : _ = v |- _ => 
                        puts He : H;
                        rewrite <- Heq in He; f He
                    | _ => 
                        match goal with
                        | Hz : binds M x v2 |- _ =>
                            not constr_eq Hz H; fail 1
                        | _ => idtac
                        end
                    end 
                | ?x' \:= ?v1 =>
                    lets He : (binds_single_bind_same_inv _ _ _ H);
                    (subst_hyp He || injects He); clear H 
                | \{} =>
                    lets He : (binds_empty _ _ H);
                    false
                | _ \(?x':=?v1) =>
                    not (constr_eq v1 v2);
                    lets He : (binds_update_same_inv _ _ _ _ H);
                    (subst_hyp He || injects He); clear H
                | _ \(?x':=?v1) =>
                    not (constr_eq v1 v2);
                    let Ha := fresh "H" in
                    asserts Ha : (x <> x'); [solve [eauto] | 
                    lets He : (binds_update_diff_inv _ _ _ _ _ Ha H);
                    clear H; clear Ha;
                    f He]
            end
        end in
    progress f H.

Ltac env_base M :=
    match M with
    | ?M1 \(_ := _) => env_base M1
    | _ => constr:M
    end.

Inductive binds_inv_done : forall {K V}, finmap K V -> K -> Prop := 
    binds_inv_done_intro : forall K V (m : finmap K V) k, binds_inv_done m k.

Tactic Notation "binds_inv" hyp(H) := binds_inv H.

Tactic Notation "binds_inv" := 
    match goal with
    | H : binds ?e _ _ |- _ => 
        not (is_var e);
        binds_inv H
    | H : binds ?v ?k _, Heq : ?M = ?v |- _ =>
        is_var v; not (is_hyp (binds_inv_done v k)); 
        let Hd := fresh "Hdone" in lets Hd : binds_inv_done_intro v k; 
        try binds_inv H
    end.

Lemma heaps_bisim_consistent_modify_env_record_preserved : forall BR jst st jeptr jer ptr obj,
    fact_js_env jeptr ptr \in BR ->
    env_record_related BR jer obj ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR (jst \(jeptr:=jer)) (st \(ptr:=obj)).
Proof.
    introv Hbi0 Horel Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_binds_eq in Hbinds1.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_js_obj fact_ptr_js_env. tryfalse.
    rewrite binds_update_diff_eq in Hbinds2 by eauto.
    eauto.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    destruct (classic (ptr = ptr0)) as [He1|He1].
    substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_js_env fact_ptr_js_env. injects.
    binds_inv. binds_inv. assumption.
    asserts He2 : (jeptr <> jeptr0).
    intro Heq. substs. eauto. 
    rewrite binds_update_diff_eq in Hbinds1 by eauto.
    rewrite binds_update_diff_eq in Hbinds2 by eauto.
    eauto.
    (* getter *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_getter_proxy fact_ptr_js_env. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* setter *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_setter_proxy fact_ptr_js_env. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* iarray *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_iarray fact_ptr_js_env. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* lfun_obj *)
    jauto_js.
    (* lfun_env *)
    jauto_js.
    (* rfun *)
    jauto_js.
    (* ltotal_obj *)
    introv Hind. 
    rew_index_eq in Hind.
    eauto.
    (* ltotal_env *)
    introv Hind.
    rew_index_eq in Hind.
    destruct_hyp Hind; eauto. 
    (* lnoghost_obj *)
    introv Hbi. rew_index_eq. eauto.
    (* lnoghost_env *)
    jauto_js.
    (* rnoghost *)
    jauto_js.
Qed.

Hint Resolve heaps_bisim_consistent_modify_env_record_preserved : js_ljs.

Lemma heaps_bisim_consistent_modify_object_preserved : forall BR jst st jptr jobj ptr obj,
    fact_js_obj jptr ptr \in BR ->
    object_related BR jobj obj ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR (jst \(jptr:=jobj)) (st \(ptr:=obj)).
Proof.
    introv Hbi0 Horel Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    destruct (classic (ptr = ptr0)) as [He1|He1].
    substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_js_obj fact_ptr_js_obj. injects.
    binds_inv. binds_inv. assumption.
    asserts He2 : (jptr <> jptr0).
    intro Heq. substs. eauto. 
    rewrite binds_update_diff_eq in Hbinds1 by eauto.
    rewrite binds_update_diff_eq in Hbinds2 by eauto.
    eauto.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_binds_eq in Hbinds1.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi0 Hbi fact_ptr_js_obj fact_ptr_js_env. tryfalse.
    rewrite binds_update_diff_eq in Hbinds2 by eauto.
    eauto.
    (* getter *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_getter_proxy fact_ptr_js_obj. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* setter *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_setter_proxy fact_ptr_js_obj. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* iarray *)
    introv Hbi Hbinds.
    asserts He : (ptr0 <> ptr).
    intro Heq. substs.
    lets Hx : heaps_bisim_consistent_rfun Hbi Hbi0 fact_ptr_iarray fact_ptr_js_obj. tryfalse. 
    rewrite binds_update_diff_eq in Hbinds by eauto.
    eauto.
    (* lfun_obj *)
    jauto_js.
    (* lfun_env *)
    jauto_js.
    (* rfun *)
    jauto_js.
    (* ltotal_obj *)
    introv Hind.
    rew_index_eq in Hind.
    destruct_hyp Hind; eauto. 
    (* ltotal_env *)
    introv Hind. 
    rew_index_eq in Hind.
    eauto.
    (* lnoghost_obj *)
    jauto_js.
    (* lnoghost_env *)
    introv Hbi. rew_index_eq. eauto.
    (* rnoghost *)
    jauto_js.
Qed.

Hint Resolve heaps_bisim_consistent_modify_object_preserved : js_ljs.

Lemma heaps_bisim_consistent_next_fresh_preserved : forall BR jst st,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR (J.state_next_fresh jst) st.
Proof.
    introv Hbisim. 
    inverts Hbisim.
    constructor; unfolds; eauto_js.
Qed.

Hint Resolve heaps_bisim_consistent_next_fresh_preserved : js_ljs.

Lemma heaps_bisim_consistent_add_getter_proxy_preserved : forall BR jst st ptr obj v,
    ~index st ptr ->
    getter_proxy obj v ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_getter_proxy ptr v} \u BR) jst (st \(ptr := obj)).
Proof.
    introv Hnindex Hproxy Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_obj; try eassumption. 
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_env; try eassumption. 
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. injects. binds_inv. assumption.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds. 
    false; eauto_js.
    eauto.    
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds.
    false; eauto_js.
    eauto.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds.
    false; eauto_js.
    eauto.
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* rfun *)
    introv Hbi1 Hbi2 Hfp1 Hfp2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2. 
    reflexivity.
    inverts Hfp1. false; eauto.
    inverts Hfp2. false; eauto.
    eauto.
    (* ltotal_obj *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_obj Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* ltotal_env *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_env Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* lnoghost_obj *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* lnoghost_env *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. inverts Hfp. prove_bag. 
    prove_bag.
Qed.

Hint Resolve heaps_bisim_consistent_add_getter_proxy_preserved : js_ljs.

Lemma heaps_bisim_consistent_add_setter_proxy_preserved : forall BR jst st ptr obj v,
    ~index st ptr ->
    setter_proxy obj v ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_setter_proxy ptr v} \u BR) jst (st \(ptr := obj)).
Proof.
    introv Hnindex Hproxy Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_obj; try eassumption. 
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_env; try eassumption. 
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds. 
    false; eauto_js.
    eauto.    
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. injects. binds_inv. assumption.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds.
    false; eauto_js.
    eauto.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds. 
    false; eauto_js.
    eauto.    
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* rfun *)
    introv Hbi1 Hbi2 Hfp1 Hfp2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2. 
    reflexivity.
    inverts Hfp1. false; eauto.
    inverts Hfp2. false; eauto.
    eauto.
    (* ltotal_obj *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_obj Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* ltotal_env *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_env Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* lnoghost_obj *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* lnoghost_env *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. inverts Hfp. prove_bag. 
    prove_bag.
Qed.

Hint Resolve heaps_bisim_consistent_add_setter_proxy_preserved : js_ljs.

Lemma heaps_bisim_consistent_add_iarray_preserved : forall BR jst st ptr obj vs,
    ~index st ptr ->
    iarray_object obj vs ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_iarray ptr vs} \u BR) jst (st \(ptr := obj)).
Proof.
    introv Hnindex Hproxy Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_obj; try eassumption. 
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds2.
    destruct_hyp Hbinds2. 
    false; eauto_js.
    specializes heaps_bisim_consistent_bisim_env; try eassumption. 
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds. 
    false; eauto_js.
    eauto.    
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds.
    false; eauto_js.
    eauto.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. injects. binds_inv. assumption.
    rew_binds_eq in Hbinds.
    destruct_hyp Hbinds. 
    false; eauto_js.
    eauto.    
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* rfun *)
    introv Hbi1 Hbi2 Hfp1 Hfp2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2. 
    reflexivity.
    inverts Hfp1. false; eauto.
    inverts Hfp2. false; eauto.
    eauto.
    (* ltotal_obj *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_obj Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* ltotal_env *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_env Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* lnoghost_obj *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* lnoghost_env *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    eauto.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. inverts Hfp. prove_bag. 
    prove_bag.
Qed.

Hint Resolve heaps_bisim_consistent_add_iarray_preserved : js_ljs.

Lemma heaps_bisim_consistent_add_ctx_parent_preserved : forall BR jst st ptr v,
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent (\{fact_ctx_parent ptr v} \u BR) jst st.
Proof.
    introv Hbisim.
    inverts Hbisim.
    constructor; unfolds.
    (* bisim_obj *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse.
    specializes heaps_bisim_consistent_bisim_obj; try eassumption. 
    jauto_js.
    (* bisim_env *)
    introv Hbi Hbinds1 Hbinds2.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; tryfalse. 
    specializes heaps_bisim_consistent_bisim_env; try eassumption. 
    jauto_js.
    (* getter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct Hbi; tryfalse.
    eauto_js.
    (* setter *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct Hbi; tryfalse.
    eauto_js.
    (* iarray *)
    introv Hbi Hbinds.
    rew_in_eq in Hbi.
    destruct Hbi; tryfalse.
    eauto_js.
    (* lfun_obj *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eauto]. 
    eauto.
    (* lfun_env *)
    introv Hbi1 Hbi2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects; try solve [false; eauto]. 
    eauto.
    (* rfun *)
    introv Hbi1 Hbi2 Hf1 Hf2.
    rew_in_eq in Hbi1. rew_in_eq in Hbi2.
    destruct_hyp Hbi1; destruct_hyp Hbi2; repeat injects.
    reflexivity.
    inverts Hf1. 
    inverts Hf2. 
    eauto. 
    (* ltotal_obj *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_obj Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* ltotal_env *)
    introv Hindex.
    lets Hx : heaps_bisim_consistent_ltotal_env Hindex.
    destruct_hyp Hx.
    jauto_js.
    (* lnoghost_obj *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; try solve [false; eapply Hdif1; reflexivity]. 
    eauto.
    (* lnoghost_env *)
    introv Hbi.
    rew_in_eq in Hbi.
    destruct_hyp Hbi; try solve [false; eapply Hdif2; reflexivity]. 
    eauto.
    (* rnoghost *)
    introv Hbi Hfp.
    rew_in_eq in Hbi.
    destruct_hyp Hbi. 
    inverts Hfp.
    eauto.
Qed.

Hint Resolve heaps_bisim_consistent_add_ctx_parent_preserved : js_ljs.

Lemma state_invariant_new_object_preserved : forall BR jst st jobj ptr obj,
    state_invariant BR jst st ->
    ~index st ptr ->
    object_related (\{fact_js_obj (fresh jst) ptr} \u BR) jobj obj ->
    state_invariant (\{fact_js_obj (fresh jst) ptr} \u BR) 
        (J.state_next_fresh (jst \(fresh jst:=jobj))) (st \(ptr:=obj)).
Proof.
    introv Hinv Hnindex Horel.
    inverts Hinv.
    constructor; jauto_js. 
Qed.

Hint Resolve state_invariant_new_object_preserved : js_ljs.

Lemma state_invariant_new_env_record_preserved : forall BR jst st jer ptr obj,
    ~index st ptr ->
    state_invariant BR jst st ->
    env_record_related (\{fact_js_env (fresh jst) ptr} \u BR) jer obj ->
    state_invariant (\{fact_js_env (fresh jst) ptr} \u BR)
        (J.state_next_fresh (jst \(fresh jst:=jer))) (st \(ptr:=obj)).
Proof.
    introv Hnindex Hinv Horel.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Hint Resolve state_invariant_new_env_record_preserved : js_ljs.

Lemma state_invariant_new_getter_proxy_preserved : forall BR jst st v ptr obj,
    ~index st ptr ->
    state_invariant BR jst st ->
    getter_proxy obj v ->
    state_invariant (\{fact_getter_proxy ptr v} \u BR) jst (st \(ptr:=obj)).
Proof.
    introv Hnindex Hinv Hinfo.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Hint Resolve state_invariant_new_getter_proxy_preserved : js_ljs.

Lemma state_invariant_new_setter_proxy_preserved : forall BR jst st v ptr obj,
    ~index st ptr ->
    state_invariant BR jst st ->
    setter_proxy obj v ->
    state_invariant (\{fact_setter_proxy ptr v} \u BR) jst (st \(ptr:=obj)).
Proof.
    introv Hnindex Hinv Hinfo.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Hint Resolve state_invariant_new_setter_proxy_preserved : js_ljs.

Lemma state_invariant_new_iarray_object_preserved : forall BR jst st vs ptr obj,
    ~index st ptr ->
    state_invariant BR jst st ->
    iarray_object obj vs ->
    state_invariant (\{fact_iarray ptr vs} \u BR) jst (st \(ptr:=obj)).
Proof.
    introv Hnindex Hinv Hinfo.
    inverts Hinv.
    constructor; jauto_js.
Qed.

Hint Resolve state_invariant_new_iarray_object_preserved : js_ljs.

Lemma state_invariant_new_exn_object_preserved : forall BR jst st ptr obj v,
    state_invariant BR jst st ->
    ~index st ptr ->
    js_exn_object obj v ->
    state_invariant BR jst (st \(ptr := obj)).
Proof.
    introv Hinv Hnindex Hexc.
    eapply state_invariant_store_incl_preserved; try eassumption. prove_bag.
Qed.

Hint Resolve state_invariant_new_exn_object_preserved : js_ljs.

Lemma state_invariant_modify_object_preserved : forall BR jst st jptr jobj ptr obj,
    fact_js_obj jptr ptr \in BR ->
    state_invariant BR jst st ->
    object_related BR jobj obj ->
    state_invariant BR (jst \(jptr:=jobj)) (st \(ptr:=obj)).
Proof.
    introv Hbi Hinv Horel.
    inverts Hinv.
    asserts Hjindex : (index jst jptr). 
    applys heaps_bisim_consistent_lnoghost_obj; try eassumption.
    constructor; jauto_js.
Qed.

Hint Extern 4 (state_invariant _ ?jst _) =>
    not is_evar jst; eapply state_invariant_modify_object_preserved : js_ljs.
(* Hint Resolve state_invariant_modify_object_preserved : js_ljs. *)

Lemma state_invariant_modify_env_record_preserved : forall BR jst st jeptr jer ptr obj obj0,
    fact_js_env jeptr ptr \in BR ->
    binds st ptr obj0 ->
    state_invariant BR jst st ->
    env_record_related BR jer obj ->
    L.object_internal obj0 \("parent"?) = L.object_internal obj \("parent"?) ->
    state_invariant BR (jst \(jeptr:=jer)) (st \(ptr:=obj)).
Proof.
    introv Hbi Hbinds Hinv Horel Hbindsp.
    inverts Hinv.
    asserts Hjindex : (index jst jeptr). 
    applys heaps_bisim_consistent_lnoghost_env; try eassumption.
    constructor; jauto_js.
    (* TODO *) skip.
Qed.

Hint Extern 4 (state_invariant _ ?jst _) =>
    not is_evar jst; eapply state_invariant_modify_env_record_preserved : js_ljs.
(* Hint Resolve state_invariant_modify_env_record_preserved : js_ljs. *)

Lemma state_invariant_next_fresh_commute_object_preserved : forall BR jst jptr jobj st,
    state_invariant BR (J.state_next_fresh (jst \(jptr := jobj))) st ->
    state_invariant BR (J.state_next_fresh jst \(jptr := jobj)) st.
Proof.
    introv Hinv. rewrite js_state_write_object_next_fresh_commute. assumption. 
Qed.

Hint Extern 4 (state_invariant _ ?jst _) =>
    not is_evar jst; eapply state_invariant_next_fresh_commute_object_preserved : js_ljs.
(* Hint Resolve state_invariant_next_fresh_commute_object_preserved : js_ljs. *)

Lemma state_invariant_double_write_preserved : forall BR jst jptr jobj jobj' st,
    state_invariant BR (jst \(jptr := jobj)) st ->
    state_invariant BR (jst \(jptr := jobj') \(jptr := jobj)) st.
Proof.
    introv Hinv. rew_bag_simpl. assumption. 
Qed.

Hint Extern 4 (state_invariant _ ?jst _) => (* TODO *)
    not is_evar jst; eapply state_invariant_double_write_preserved : js_ljs.
(* Hint Resolve state_invariant_double_write_preserved : js_ljs. *)

Lemma ctx_parent_ok_new_env_parent_preserved : forall BR st ptr jeptr obj v,
    fact_js_env jeptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "parent" v ->
    ctx_parent_ok BR st ->
    ctx_parent_ok (\{fact_ctx_parent ptr v} \u BR) st.
Proof.
    introv Hbs Hbinds1 Hbinds2 Hcp Hf.
    rew_in_eq in Hf.
    destruct_hyp Hf; repeat injects. { jauto_js. }
    specializes Hcp Hf. destruct_hyp Hcp. jauto_js.
Qed.

Hint Resolve ctx_parent_ok_new_env_parent_preserved : js_ljs.

Lemma state_invariant_new_env_parent_preserved : forall BR jst st v jeptr ptr obj,
    fact_js_env jeptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "parent" v ->
    state_invariant BR jst st ->
    state_invariant (\{fact_ctx_parent ptr v} \u BR) jst st.
Proof.
    introv Hbs Hbinds1 Hbinds2 Hinv.
    inverts Hinv.
    asserts Hsub : (BR \c \{fact_ctx_parent ptr v} \u BR). jauto_js.
    constructor; jauto_js.
Qed.

(* Hint Resolve state_invariant_new_env_parent_preserved : js_ljs. *)
Hint Extern 4 (state_invariant (\{fact_ctx_parent _ _} \u _) _ _) => 
    eapply state_invariant_new_env_parent_preserved : js_ljs.

Lemma env_record_exist_push_context_lemma : forall BR jc jeptr ptr,
    env_records_exist BR jc ->
    fact_js_env jeptr ptr \in BR ->
    env_records_exist BR
        (J.execution_ctx_with_lex jc (jeptr :: J.execution_ctx_lexical_env jc)).
Proof.
    introv Henv Hbisim.
    destruct Henv.
    destruct jc. simpls.
    constructor; simpls; introv Hmem. 
    iauto.
    inverts Hmem; iauto.  
Qed.

Hint Resolve env_record_exist_push_context_lemma : js_ljs.

Lemma execution_ctx_related_push_context_lemma : forall BR jc jeptr c ptr,
    lexical_env_related BR (jeptr :: J.execution_ctx_lexical_env jc) (L.value_object ptr) ->
    execution_ctx_related BR jc c ->
    execution_ctx_related BR
        (J.execution_ctx_with_lex jc (jeptr :: J.execution_ctx_lexical_env jc))
        (c\("$context":=L.value_object ptr)).
Proof.
    introv Hlrel Hrel.
    destruct Hrel.
    destruct jc.
    constructor; introv Hbinds; rew_binds_eq in Hbinds; destruct_hyp Hbinds; tryfalse; iauto.
Qed.

Hint Resolve execution_ctx_related_push_context_lemma : js_ljs.

Lemma context_invariant_push_context_lemma : forall BR jc jeptr ptr c,
    lexical_env_related BR (jeptr :: J.execution_ctx_lexical_env jc) (L.value_object ptr) ->
    fact_js_env jeptr ptr \in BR ->
    context_invariant BR jc c ->
    context_invariant BR 
        (J.execution_ctx_with_lex jc (jeptr :: J.execution_ctx_lexical_env jc))
        (c\("$context":=L.value_object ptr)).
Proof.
    introv Hlrel Hbisim Hinv.
    destruct Hinv.
    constructor; jauto_js.
Qed.

Hint Resolve context_invariant_push_context_lemma : js_ljs.

Lemma includes_init_ctx_add_init_ctx_preserved : forall c s v,
    binds LjsInitEnv.init_ctx s v ->
    includes_init_ctx c ->
    includes_init_ctx (c \(s := v)).
Proof.
    introv Hbinds Hincl.
    unfolds includes_init_ctx.
    introv Hbinds1 Hbinds2.
    rew_binds_eq in Hbinds1.
    destruct_hyp Hbinds1.
    binds_determine. reflexivity.
    eauto.
Qed.

Hint Resolve includes_init_ctx_add_init_ctx_preserved : js_ljs.

Lemma prealloc_in_ctx_add_init_ctx_preserved : forall BR c s v,
    binds LjsInitEnv.init_ctx s v ->
    initBR \c BR ->
    prealloc_in_ctx BR c ->
    prealloc_in_ctx BR (c \(s:=v)).
Proof.
    introv Hbinds Hincl Hpre.
    unfolds prealloc_in_ctx.
    introv Hpmem Hbinds1.
    rew_binds_eq in Hbinds1.
    destruct_hyp Hbinds1.
    forwards Hx : prealloc_in_ctx_init_ctx Hincl Hpmem Hbinds. assumption.
    eauto.
Qed.

Hint Resolve prealloc_in_ctx_add_init_ctx_preserved : js_ljs.

Lemma global_env_record_exists_add_init_ctx_preserved : forall BR c s v,
    binds LjsInitEnv.init_ctx s v ->
    initBR \c BR ->
    global_env_record_exists BR c ->
    global_env_record_exists BR (c \(s:=v)).
Proof.
    introv Hbinds Hincl Hpre.
    unfolds global_env_record_exists.
    introv Hbinds1.
    rew_binds_eq in Hbinds1.
    destruct_hyp Hbinds1.
    forwards Hx : global_env_record_exists_init_ctx Hincl Hbinds. assumption.
    eauto.
Qed.

Hint Resolve global_env_record_exists_add_init_ctx_preserved : js_ljs.

Lemma context_invariant_add_init_ctx_preserved : forall BR jc c s v,
    binds LjsInitEnv.init_ctx s v ->
    context_invariant BR jc c ->
    context_invariant BR jc (c \(s := v)).
Proof.
    introv Hbinds Hinv.
    lets Hpre : init_ctx_percent_prefix Hbinds.
    destruct_hyp Hpre.
    inverts Hinv.
    constructor; eauto_js.
Qed.

Lemma lexical_env_related_restore_lexical_env : forall BR BR' jlenv v,
    lexical_env_related BR jlenv v ->
    BR \c BR' ->
    lexical_env_related BR' jlenv v.
Proof.
    introv Hrel Hsub.
    induction Hrel as [|? ? ? ? ? Hbisim Hcpar].
    jauto_js.
    eapply lexical_env_related_cons; eauto_js.
Qed.

Hint Resolve lexical_env_related_restore_lexical_env : js_ljs.

Lemma execution_ctx_related_restore_lexical_env : forall BR BR' jc c,
    execution_ctx_related BR jc c ->
    BR \c BR' ->
    execution_ctx_related BR' jc c.
Proof.
    introv Hrel Hsub.
    destruct Hrel.
    constructor; jauto_js.
Qed.

Hint Resolve execution_ctx_related_restore_lexical_env : js_ljs.

Lemma js_exn_object_state_security_ok_preserved : forall st st' ptr v,
    L.state_security_ok st st' ->
    js_exn_object_ptr st ptr v ->
    js_exn_object_ptr st' ptr v.
Proof.
    introv Hsec Hexn.
    inverts Hexn as Hbinds Hexno.
    specializes Hsec Hbinds.
    destruct Hsec as (?obj&Hbinds'&Hsec).
    econstructor. eassumption.
    destruct Hsec.
    destruct Hexno.
    constructor. 
    skip. (* TODO *)
    skip. (* TODO *)
    skip. (* TODO *)
    forwards Hok : object_security_ok_attributes js_exn_object_exn.
    reflexivity.
    destruct Hok as (?attrs&Habinds'&Hconf&Hasec).
    inverts Hasec; tryfalse. assumption.
Qed.

Hint Resolve js_exn_object_state_security_ok_preserved : js_ljs.

Hint Extern 0 (L.state_security_ok ?st ?st) => apply (@L.state_security_ok_refl st) : js_ljs.

Hint Extern 0 (L.state_security_ok ?st1 ?st3) =>
    match goal with
    | H : L.state_security_ok st1 ?st2 |- _ => 
        apply (@L.state_security_ok_trans st2 st1 st3 H)
    | H : L.state_security_ok ?st2 st3 |- _ => 
        apply ((fun h1 h2 => @L.state_security_ok_trans st2 st1 st3 h2 h1) H)
    end : js_ljs.

Lemma context_invariant_prealloc_in_ctx_lemma : forall BR jc c s ptr jpre,
    context_invariant BR jc c ->
    Mem (jpre, s) prealloc_in_ctx_list ->
    binds c s (L.value_object ptr) ->
    fact_js_obj (J.object_loc_prealloc jpre) ptr \in BR.
Proof.
    introv Hinv Hmem Hbinds.
    lets Hx : context_invariant_prealloc_related Hinv Hmem Hbinds.
    destruct_hyp Hx.
    injects.
    assumption.
Qed.

Ltac context_invariant_prealloc :=
    match goal with
    | HC : context_invariant ?BR' _ _ |- fact_js_obj (J.object_loc_prealloc ?jpre) _ \in ?BR =>
        let Hsub := fresh "H" in 
        asserts Hsub : (BR' \c BR); [prove_bag | idtac];
        applys context_invariant_prealloc_in_ctx_lemma (context_invariant_bisim_incl_preserved Hsub HC);
            [solve [repeat (eapply Mem_here || eapply Mem_next)] | idtac]; (* TODO something faster *)
        clear Hsub 
    end.

Hint Extern 4 (fact_js_obj (J.object_loc_prealloc _) _ \in _) =>
    context_invariant_prealloc : js_ljs.

Lemma builtin_assoc : forall k BR jc c st st' i v r,
    context_invariant BR jc c ->
    L.red_exprh k c st (L.expr_basic (L.expr_id i)) (L.out_ter st' r) ->
    binds LjsInitEnv.init_ctx i v ->
    st = st' /\ r = L.res_value v.
Proof.
    introv Hinv Hlred Hmem.
    inverts Hlred.
    forwards Hic : context_invariant_includes_init_ctx Hinv __; eauto.
    substs; eauto.
Qed.

Lemma init_ctx_mem_assoc : forall i v,
    Mem (i, v) LjsInitEnv.ctx_items ->
    Assoc i v LjsInitEnv.ctx_items.
Proof.
Admitted. (* because they are all different *)

Lemma init_ctx_mem_binds : forall i v,
    Mem (i, v) LjsInitEnv.ctx_items ->
    binds LjsInitEnv.init_ctx i v.
Proof.
    introv Hmem.
    eapply from_list_binds_inv.
    eapply init_ctx_mem_assoc. assumption.
Qed.

Lemma object_prim_related_primval_none : forall BR jov obj,
    jov = None ->
    ~index (L.object_internal obj) "primval" ->
    option_value_related BR jov (L.object_internal obj\("primval"?)).
Proof.
    introv H Hi.
    substs.
    rewrite read_option_not_index_inv; jauto_js.
Qed.

Hint Resolve object_prim_related_primval_none : js_ljs.

Lemma object_prim_related_primval_some : forall BR jov obj jv v,
    jov = Some jv ->
    binds (L.object_internal obj) "primval" v ->
    value_related BR jv v ->
    option_value_related BR jov (L.object_internal obj\("primval"?)).
Proof.
    introv H Hi Hrel.
    substs.
    erewrite read_option_binds_inv; jauto_js.
Qed.

Hint Resolve object_prim_related_primval_some : js_ljs.

(* Prerequisites *)

Lemma ih_expr_leq : forall k k', (k' <= k)%nat -> ih_expr k -> ih_expr k'.
Proof.
    introv Hle He Hlt.
    apply He. omega.
Qed.

Lemma ih_stat_leq : forall k k', (k' <= k)%nat -> ih_stat k -> ih_stat k'.
Proof.
    introv Hle He Hlt.
    apply He. omega.
Qed.

Lemma ih_call_prealloc_leq : forall k k', (k' <= k)%nat -> ih_call_prealloc k -> ih_call_prealloc k'.
Proof.
    introv Hle He Hlt.
    apply He. omega.
Qed.

Lemma ih_expr_S : forall k, ih_expr (S k) -> ih_expr k.
Proof.
    introv He. eapply ih_expr_leq; try eassumption; omega.
Qed.

Lemma ih_stat_S : forall k, ih_stat (S k) -> ih_stat k.
Proof.
    introv He. eapply ih_stat_leq; try eassumption; omega.
Qed.

Lemma ih_call_prealloc_S : forall k, ih_call_prealloc (S k) -> ih_call_prealloc k.
Proof.
    introv He. eapply ih_call_prealloc_leq; try eassumption; omega.
Qed.

(* TODO move S5-only tactics! *)
Ltac ljs_inv_closure_ctx :=
    match goal with
    | H : L.closure_ctx (L.closure_intro _ _ _ _) _ _ |- _ =>
        let Hz := fresh "H" in
        inverts H as Hz; repeat (inverts Hz as Hz) (* crunching Zip *)
    end.

Ltac ljs_closure_body := 
    match goal with
    | H : L.red_exprh _ _ _ (L.expr_basic (L.closure_body (L.closure_intro _ _ _ ?e))) _ |- _ => 
        unfold L.closure_body in H; try (unfold e in H)
    end.

Ltac ljs_inv_closure_hyps :=
    match goal with
    | Hcctx : L.closure_ctx ?clo _ ?c |- _ => 
        let Hz := fresh "H" in
        let c' := fresh "c" in
        remember c as c';
        inverts Hcctx as Hz; repeat (inverts Hz as Hz); (* crunching Zip *)
        let EQc := match goal with H : _ = c |- _ => constr:H end in
        repeat rewrite from_list_update in EQc;
        repeat rewrite from_list_empty in EQc;
        rew_bag_simpl in EQc;
        let cdef0 := match type of EQc with ?cdef = _ => constr:cdef end in
        let rec to_binds cdef := 
            match cdef with
            | ?cdef' \( ?s := ?v ) =>
                let Hb := fresh "Hb" in
                assert (Hb : binds cdef0 s v) by prove_bag 100;
                rewrite EQc in Hb;
                to_binds cdef'
            | ?c1 => is_var c1; idtac
            | \{} => idtac
            end in 
        to_binds cdef0  
    end.

Ltac ljs_apply := progress repeat (ljs_inv_closure_hyps || ljs_closure_body).

Ltac ljs_context_invariant := 
    match goal with
    | |- context_invariant _ _ _ => 
        eassumption
    | |- context_invariant _ _ \{} =>
        eapply context_invariant_replace_ctx_sub_init; [solve [eapply empty_incl] | eassumption]
    | |- context_invariant _ _ (_ \(?s := ?v)) =>
        eapply context_invariant_add_nopercent_nodollar_id_preserved; 
        [idtac | solve [eauto] | solve [eauto]]; ljs_context_invariant
    | |- context_invariant _ _ (_ \(?s := ?v)) =>
        eapply context_invariant_add_init_ctx_preserved; [
        eapply init_ctx_mem_binds;
        solve [init_ctx_lookup] | idtac]; ljs_context_invariant
    end.

Ltac ljs_context_invariant_after_apply :=
    match goal with
    | Hlred : L.red_exprh _ ?c' ?st _ _, Hinv : context_invariant ?BR ?jc ?c, Heq : _ = ?c' |- _ =>
        is_var c'; not (is_hyp (context_invariant BR jc c'));
        let Hinv' := fresh "Hinv" in
        asserts Hinv' : (context_invariant BR jc c'); 
        [rewrite <- Heq; ljs_context_invariant
        |idtac]
    end.

Ltac apply_ih_expr := match goal with
    | H : ih_expr ?k', 
      HS : state_invariant ?BR ?jst ?st,
      HC' : context_invariant ?BR' ?jc ?c', 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        let HC := fresh "HC" in
        let Hih := fresh "IH" in
        let Hsec := fresh "Hsec" in
        let Hsub := fresh "H" in
        asserts Hle : (k < k')%nat; [math | idtac];
        asserts Hsub : (BR' \c BR); [prove_bag | idtac];
        asserts HC : (context_invariant BR jc c); 
            [applys context_invariant_bisim_incl_preserved Hsub; ljs_context_invariant | idtac]; 
        lets Hih : H Hle HC HS HR; lets Hsec : L.red_exprh_state_security_ok HR; 
        clear Hle; clear Hsub; clear HS; clear HR; clear HC
    end.

Ltac apply_ih_stat := match goal with
    | H : ih_stat ?k', 
      HS : state_invariant ?BR ?jst ?st,
      HC' : context_invariant ?BR' ?jc ?c', 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        let HC := fresh "HC" in
        let Hsec := fresh "Hsec" in
        let Hsub := fresh "H" in
        asserts Hle : (k < k')%nat; [math | idtac];
        asserts Hsub : (BR' \c BR); [prove_bag | idtac];
        asserts HC : (context_invariant BR jc c); 
            [applys context_invariant_bisim_incl_preserved Hsub; ljs_context_invariant | idtac]; 
        lets Hih : H Hle HC HS HR; lets Hsec : L.red_exprh_state_security_ok HR; 
        clear Hle; clear Hsub; clear HS; clear HR; clear HC
    end.

Ltac ljs_get_builtin :=
    match goal with
    | Hbinds : binds ?c (String (Ascii.Ascii true false true false false true false false) ?s) ?v, 
      Hinv : context_invariant _ _ ?c |- _ =>
        is_var v;
(*        not (first [constr_eq s "strict" | constr_eq s "this" | constr_eq s "context"]); *)
        let H1 := fresh in
        forwards H1 : context_invariant_includes_init_ctx Hinv Hbinds; [
        eapply init_ctx_mem_binds;
        unfold LjsInitEnv.ctx_items;
        solve [init_ctx_lookup] | 
        subst_hyp H1 ]
    | Hinv : context_invariant _ _ ?c ,
      H : L.red_exprh _ ?c ?st (L.expr_basic (E.make_builtin _)) _ |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        forwards (H1&H2) : builtin_assoc Hinv H; [
        eapply init_ctx_mem_binds;
        unfold LjsInitEnv.ctx_items;
        solve [init_ctx_lookup] | 
        clear H;
        subst_hyp H1; subst_hyp H2 ]
    end.

Lemma res_related_abort : forall BR jst jst' st jr r,
    res_related BR jst st jr r ->
    J.abort (J.out_ter jst' jr) ->
    L.res_is_control r.
Proof.
    introv Hrel Hab.
    inverts Hrel.
    inverts Hab. unfold J.res_is_normal in *. simpls. false.
    eapply L.res_is_control_exception.
    eapply L.res_is_control_break.
    eapply L.res_is_control_break.
    eapply L.res_is_control_break.
Qed.

Ltac ljs_abort_from_js := 
    match goal with
    | Hja : J.abort (J.out_ter ?jst ?jr), Hc : context [L.out_ter ?st ?r],
      Hrel : res_related _ ?jst ?st ?jr ?r |- _ => 
      not is_hyp (L.abort (L.out_ter st r));
      let H := fresh "H" in
      assert (H : L.abort (L.out_ter st r)); 
      [solve [applys L.abort_control (res_related_abort Hrel Hja)] | idtac] 
    end.

Hint Extern 0 (~ _) => solve [let H := fresh in intro H; inversion H].

Ltac ljs_propagate_abort :=
    match goal with
    | Habort : L.abort (L.out_ter ?st ?r), Hred : context [L.out_ter ?st ?r] |- _ =>
    match type of Hred with
    | L.red_exprh ?k ?c ?st0 ?ee (L.out_ter ?st' ?r') => 
        let H := fresh "H" in
        assert (H : L.red_exprh k c st0 ee (L.out_ter st r));
        [applys L.red_exprh_general_abort; solve [trivial] | idtac];
        let Hdet := fresh "H" in
        forwards Hdet : L.red_exprh_deterministic Hred H;
        injects Hdet;
        clear H Hred
    end
    end.

Ltac ljs_handle_abort := progress (repeat (ljs_propagate_abort || ljs_abort_from_js)); solve_jauto_js.

Ltac ih_leq :=
    match goal with
    | H : ih_expr ?k |- ih_expr ?k' => is_evar k'; eapply H
    | H : ih_expr ?k |- ih_expr ?k' => eapply ih_expr_leq; try eapply H; omega
    | H : ih_stat ?k |- ih_stat ?k' => is_evar k'; eapply H
    | H : ih_stat ?k |- ih_stat ?k' => eapply ih_stat_leq; try eapply H; omega
    | H : ih_call_prealloc ?k |- ih_call_prealloc ?k' => is_evar k'; eapply H
    | H : ih_call_prealloc ?k |- ih_call_prealloc ?k' => eapply ih_call_prealloc_leq; try eapply H; omega
    end.

(* TODO auto-clear the red_exprh hypothesis used *)
Ltac specializes_th H :=
    try unfold th_stat, th_spec, th_ext_expr_unary, th_ext_expr_binary in H;
    let needs_state := match type of H with
        | context [state_invariant _ _ _ -> _] => constr:true (* TODO better *)
        | _ => constr:false
    end in
    specializes H ___;
    try match goal with Hx : state_invariant _ _ _ |- state_invariant _ _ _ => eapply Hx end;
    try match goal with |- L.red_exprh _ _ _ _ _ => eassumption end;
    try match goal with 
    | Hx : context_invariant ?BR' _ _ |- context_invariant ?BR _ _ =>  
        let Hsub := fresh in
        asserts Hsub : (BR' \c BR); [prove_bag 10 | idtac];
        applys context_invariant_bisim_incl_preserved Hsub;
        ljs_context_invariant 
    end;
    try match goal with 
    | Hx : value_related ?BR' _ ?v |- value_related ?BR _ ?v =>
        let Hsub := fresh in
        asserts Hsub : (BR' \c BR); [prove_bag 10 | idtac];
        applys value_related_bisim_incl_preserved Hsub; eauto_js
    | Hx : resvalue_related ?BR' _ ?v |- resvalue_related ?BR _ ?v =>
        let Hsub := fresh in
        asserts Hsub : (BR' \c BR); [prove_bag 10 | idtac];
        applys resvalue_related_bisim_incl_preserved Hsub; eauto_js
    | Hx : lexical_env_related ?BR' _ ?v |- lexical_env_related ?BR _ ?v =>
        let Hsub := fresh in
        asserts Hsub : (BR' \c BR); [prove_bag 10 | idtac];
        applys lexical_env_related_bisim_incl_preserved Hsub; eauto_js
    | |- value_related _ _ ?v => not is_evar v; eauto_js
    | |- resvalue_related _ _ ?v => not is_evar v; eauto_js
    | |- lexical_env_related _ _ ?v => not is_evar v; eauto_js
    end;
    try ih_leq;
    match needs_state with
    | true => match goal with Hx : state_invariant _ _ _ |- _ => clear Hx end
    | false => idtac
    end.

Tactic Notation "forwards_th" ident(H) ":" constr(th) :=
    lets H : th;
    specializes_th H.

Tactic Notation "forwards_th" ":" constr(th) :=
    let H := fresh "H" in 
    forwards_th H : th.

Lemma res_related_invert_abort_lemma : forall BR jst st jr r,
    res_related BR jst st jr r ->
    (exists jrv v, 
        jr = J.res_intro J.restype_normal jrv J.label_empty /\
        r = L.res_value v /\ 
        resvalue_related BR jrv v) \/
    J.abort (J.out_ter jst jr) /\ L.abort (L.out_ter st r).
Proof.
    introv Hrel.
    inverts Hrel; ijauto_js.
Qed.

Ltac res_related_abort :=
    match goal with
    | H : res_related _ ?jst ?st ?jr ?r |- _ =>
        not is_hyp (J.abort (J.out_ter jst jr));
        let Hr := fresh "H" in
        forwards Hr : res_related_invert_abort_lemma H;
        destruct_hyp Hr; [clear H | idtac]
    end.

Ltac destr_concl_auto := destr_concl; res_related_abort; try ljs_handle_abort.

Ltac ljs_autoinject := 
    match goal with
    | H : L.value_object ?obj1 = L.value_object ?obj2 |- _ => injects H || (constr_eq obj1 obj2; clear H)
    end. 

Ltac ljs_op_inv :=
    match goal with
    | H : L.eval_unary_op ?op ?st ?v ?v' |- _ => 
        let H1 := fresh in inverts H as H1; try inverts H1
    | H : L.eval_binary_op ?op ?st ?v ?v1 ?v' |- _ => 
        let H1 := fresh in inverts H as H1; try inverts H1
    end.

Ltac ljs_fwd_op_inv := ljs_op_inv; [idtac].

Ltac ljs_autoforward := first [
    inv_top_fwd_ljs | ljs_fwd_op_inv | ljs_out_redh_ter | 
    apply_ih_stat | apply_ih_expr | ljs_autoinject | 
    binds_inv | binds_determine | ljs_get_builtin ].

Lemma js_red_expr_getvalue_lemma : forall jst jc je jo jsr,
    js_red_expr_getvalue jst jc je jo jsr ->
    J.red_spec jst jc (J.spec_expr_get_value je) jsr.
Proof.
    introv (Hgv1&Hgv2).
    inverts Hgv2; jauto_js.
Qed.

Hint Resolve js_red_expr_getvalue_lemma : js_ljs.
