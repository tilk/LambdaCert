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

(** The constructors for relating JS to S5 are used as hints. *)

Hint Constructors attributes_data_related : js_ljs.
Hint Constructors attributes_accessor_related : js_ljs. 
Hint Constructors attributes_related : js_ljs.
Hint Constructors value_related : js_ljs.
Hint Constructors resvalue_related : js_ljs.
Hint Constructors res_related : js_ljs.

(** The constructors of JSCert are used as hints, for automated building of
    the derivation trees for the semantics judgment. *)

Hint Constructors J.red_expr : js_ljs.
Hint Constructors J.red_stat : js_ljs.
Hint Constructors J.red_spec : js_ljs.
Hint Constructors J.abort : js_ljs.

(** Unfolding hints *)

Hint Extern 4 (js_exn_object _ _) => unfold js_exn_object : js_ljs.
Hint Extern 4 (res_related _ _ _ (J.res_throw _) _) => unfold J.res_throw : js_ljs.
Hint Extern 4 (JsPreliminary.regular_binary_op _) => unfold JsPreliminary.regular_binary_op : js_ljs.

(** Automatic deconstructing of ifs in goals *)

Hint Extern 11 => match goal with |- context [If _ then _ else _] => case_if end : js_ljs.

(* TODO logical hints - move? different database? *)

Hint Extern 1 (~(_ /\ _)) => rew_logic.

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
    unfold concl_ext_expr_value, concl_expr_getvalue, 
        concl_stat, concl_spec.
 
Tactic Notation "unfold_concl" "in" hyp(H) := 
    unfold concl_ext_expr_value, concl_expr_getvalue, 
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

Ltac js_abort_rel_contr := match goal with
    | Ha : J.abort (J.out_ter ?jst ?x), Hr : res_related _ ?jst _ ?x (L.res_value _) |- _ =>
        let Hisn := fresh "Hisn" in
        inverts Ha as Hisn; inverts Hr; unfold J.res_is_normal, J.res_type in Hisn; false
    end.

Hint Extern 10 => js_abort_rel_contr : js_ljs.
 
Ltac apply_ih_expr := match goal with
    | H : ih_expr ?k', HS : state_invariant _ _ _ ?c ?st, 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        let Hih := fresh "IH" in
        asserts Hle : (k < k')%nat; [omega | lets Hih : H Hle HS HR; clear Hle; clear HR]
    end.

Ltac apply_ih_stat := match goal with
    | H : ih_stat ?k', HS : state_invariant _ _ _ ?c ?st, 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        asserts Hle : (k < k')%nat; [omega | lets Hih : H Hle HS HR; clear Hle; clear HR]
    end.

Hint Extern 1 (J.regular_unary_op _) =>
    solve [let H := fresh "H" in intro H; unfolds in H; destruct_hyp H; inverts H] : js_ljs.

Tactic Notation "autoforwards" simple_intropattern(I) ":" constr(E) :=
    (forwards I : E; try eassumption; try omega); [idtac].

Ltac destr_concl := match goal with
    | H : concl_spec _ _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_stat _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_ext_expr_value _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_expr_getvalue _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    end.

Tactic Notation "jauto_js" integer(k) := repeat destr_concl; jauto_set; eauto with js_ljs bag typeclass_instances; 
    repeat (try unfold_concl; jauto_set; eauto k with js_ljs bag typeclass_instances).

Tactic Notation "jauto_js" := jauto_js 5.

Ltac solve_jauto_js := solve [jauto_js 50].

Ltac ijauto_js := repeat intuition jauto_js.

Ltac solve_ijauto_js := solve [ijauto_js; solve_jauto_js].

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

Hint Extern 20 => progress autorewrite with js_ljs.

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

(* Lemmas about invariants *)

Lemma heaps_bisim_consistent_nindex_preserved : forall BR jst st ptr obj,
    ~index st ptr ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR jst (st \( ptr := obj)).
Proof.
    introv Hni Hbi.
    inverts Hbi as Hbisim Hlfun Hrfun Hltotal Hlnoghost Hrnoghost.
    constructor; auto.
    unfolds heaps_bisim.
    introv Hrel Hjb Hlb.
    specializes Hrnoghost Hrel.
    eapply Hbisim; try eassumption.
    eapply binds_update_diff_inv; try eassumption; auto. 
    unfolds heaps_bisim_rnoghost.
    prove_bag.
Qed.

Lemma lexical_env_related_nindex_preserved : forall BR jst st ptr obj jle v v',
    ~index st ptr ->
    lexical_env_related BR jst st v' jle v ->
    lexical_env_related BR jst (st \( ptr := obj )) v' jle v.
Proof.
Admitted.

Lemma execution_ctx_related_nindex_preserved : forall BR jst jc c st ptr obj,
    ~index st ptr ->
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc c (st \( ptr := obj)).
Proof.
    introv Hni Hbi.
    inverts Hbi; constructor.
    auto.
    auto.
    intros. apply lexical_env_related_nindex_preserved; auto.
Qed.

Lemma state_invariant_nindex_preserved : forall BR jst jc c st ptr obj,
    ~index st ptr ->
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c (st \( ptr := obj )).
Proof.
    introv Hni Hinv.
    inverts Hinv.
    constructor.
    apply heaps_bisim_consistent_nindex_preserved; auto.
    apply execution_ctx_related_nindex_preserved; auto.
    assumption.
    assumption.
Qed.

Lemma state_invariant_fresh_preserved : forall BR jst jc c st obj,
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c (st \( fresh st := obj )).
Proof.
    introv Hinv.
    apply state_invariant_nindex_preserved; prove_bag.
Qed.

Hint Resolve state_invariant_fresh_preserved : js_ljs.

Lemma includes_init_ctx_incl_preserved : forall c c',
    c' \c c ->
    includes_init_ctx c ->
    includes_init_ctx c'.
Proof.
    unfolds includes_init_ctx.
    prove_bag.
Qed.

Lemma execution_ctx_related_incl_preserved : forall BR jst jc c c' st,
    c' \c c ->
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc c' st.
Proof.
    introv Hincl Hrel.
    inverts Hrel.
    constructor.
    prove_bag.
    prove_bag.
    intros.
    eapply execution_ctx_related_lexical_env. prove_bag. prove_bag. (* TODO auto depth for prove_bag *)
Qed.

Lemma state_invariant_ctx_incl_preserved : forall BR jst jc c c' st,
    c' \c c ->
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c' st.
Proof.
    introv Hincl Hinv.
    inverts Hinv.
    constructor.
    assumption.
    eapply execution_ctx_related_incl_preserved; eassumption.
    eapply includes_init_ctx_incl_preserved; eassumption.
    assumption.
Qed.

Hint Resolve state_invariant_ctx_incl_preserved : js_ljs.

Hint Extern 1 (_ <> _) => solve [let H := fresh in intro H; injects H; false]. 

Section prefixes.

Local Open Scope char_scope.

Lemma init_ctx_percent_prefix : forall v s,
    Mem (s, v) LjsInitEnv.ctx_items -> exists s', s = String "%" s'.
Proof.
    introv Hmem.
(*
    repeat (inverts Hmem as Hmem; [skip | idtac]).
*)
    skip.
Qed.

Lemma execution_ctx_related_add_nopercent_id_preserved : forall BR jst jc c st s v ch,
    ch <> "%" ->
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc (c \(String ch s := v)) st.
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

Lemma state_invariant_add_nopercent_id_preserved : forall BR jst jc c st s v ch,
    state_invariant BR jst jc c st ->
    ch <> "%" ->
    state_invariant BR jst jc (c \(String ch s := v)) st.
Proof.
    introv Hinv Hdif.
    inverts Hinv.
    constructor.
    assumption.
    eapply execution_ctx_related_add_nopercent_id_preserved; eassumption.
    eapply includes_init_ctx_add_nopercent_id_preserved; eassumption.
    assumption.
Qed.

Lemma execution_ctx_related_unadd_nopercent_id_preserved : forall BR jst jc c st s v ch,
    ch <> "%" ->
    execution_ctx_related BR jst jc (c \(String ch s := v)) st ->
    execution_ctx_related BR jst jc c st.
Proof.
    introv Hdif Hrel.
    inverts Hrel.
    constructor;
    introv Hbinds.
    prove_bag. 
    prove_bag. 
    introv Hbinds'. 
    eapply execution_ctx_related_lexical_env. prove_bag. prove_bag. (* TODO auto depth for prove_bag *)
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

Lemma state_invariant_unadd_nopercent_id_preserved : forall BR jst jc c st s v ch,
    state_invariant BR jst jc (c \(String ch s := v)) st ->
    ch <> "%" ->
    state_invariant BR jst jc c st.
Proof.
    introv Hinv Hdif.
    inverts Hinv.
    constructor.
    assumption.
    eapply execution_ctx_related_unadd_nopercent_id_preserved; eassumption.
    eapply includes_init_ctx_unadd_nopercent_id_preserved; eassumption.
    assumption.
Qed.

End prefixes.

Hint Resolve state_invariant_add_nopercent_id_preserved : js_ljs.
Hint Resolve state_invariant_unadd_nopercent_id_preserved : js_ljs.

(* TODO ? 
Lemma execution_ctx_related_union_preserved : forall BR jst jc c c' st,
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc c' st ->
    execution_ctx_related BR jst jc (c \u c') st.
Proof.
    introv Hrel1 Hrel2.
    inverts Hrel1.
    inverts Hrel2.
    constructor.
    introv Hbinds.
    rewrite binds_union_eq in Hbinds.
    destruct_hyp Hbinds; eauto.
    introv Hbinds.
    rewrite binds_union_eq in Hbinds.
    destruct_hyp Hbinds; eauto.
    introv Hbinds;
    rewrite binds_union_eq in Hbinds;
    destruct_hyp Hbinds;
    introv Hbinds';
    rewrite binds_union_eq in Hbinds';
    destruct_hyp Hbinds'.
    eauto.
    eauto.
    eapply lexical_env_related_union_preserved. eauto. eauto.
Qed.
*)

Lemma value_related_bisim_incl_preserved : forall BR1 BR2 jv v,
    BR1 \c BR2 ->
    value_related BR1 jv v ->
    value_related BR2 jv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js. 
Qed.

Hint Resolve value_related_bisim_incl_preserved : js_ljs.

Lemma resvalue_related_bisim_incl_preserved : forall BR1 BR2 jrv v,
    BR1 \c BR2 ->
    resvalue_related BR1 jrv v ->
    resvalue_related BR2 jrv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

Hint Resolve resvalue_related_bisim_incl_preserved : js_ljs.

Lemma res_related_bisim_incl_preserved : forall BR1 BR2 jst st jr r,
    BR1 \c BR2 ->
    res_related BR1 jst st jr r ->
    res_related BR2 jst st jr r.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

Hint Resolve res_related_bisim_incl_preserved : js_ljs.

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

Lemma ih_expr_S : forall k, ih_expr (S k) -> ih_expr k.
Proof.
    introv He. eapply ih_expr_leq; try eassumption; omega.
Qed.

Lemma ih_stat_S : forall k, ih_stat (S k) -> ih_stat k.
Proof.
    introv He. eapply ih_stat_leq; try eassumption; omega.
Qed.

(* TODO move S5-only tactics! *)
Ltac ljs_inv_value_is_closure :=
    match goal with
    | H : L.value_is_closure _ ?v _ |- _ => 
        unfold v in H; ljs_inv_value_is_closure 
    | H : L.value_is_closure _ (L.value_closure _) _ |- _ =>
        inverts H
    end.

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

Ltac ljs_apply := progress repeat (ljs_inv_value_is_closure || ljs_inv_closure_ctx || ljs_closure_body).

Ltac binds_inv H :=
    match type of H with
    | binds ?M ?x ?v2 =>
        let He := fresh "H" in
        match M with
        | ?x' \:= ?v1 =>
            lets He : (binds_single_bind_same_inv _ _ _ H);
            subst v2; clear H    
        | _ \(?x':=?v1) =>
            lets He : (binds_update_same_inv _ _ _ _ H);
            subst v2; clear H
        | _ \(?x':=?v1) =>
            let Ha := fresh "H" in
            asserts Ha : (x <> x'); [eauto | 
            lets He : (binds_update_diff_inv _ _ _ _ _ Ha H);
            clear H; clear Ha;
            binds_inv He]
        end
    end.

Tactic Notation "binds_inv" hyp(H) := binds_inv H.

Tactic Notation "binds_inv" := 
    match goal with
    | H : binds _ _ _ |- _ => binds_inv H
    end.

Lemma state_invariant_includes_init_ctx_lemma : forall BR jst jc c st i v v',
    state_invariant BR jst jc c st ->
    binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'.
Proof.
    introv Hinv.
    inverts Hinv.
    jauto.
Qed.

Lemma builtin_assoc : forall k BR jst jc c st st' i v r,
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (L.expr_id i)) (L.out_ter st' r) ->
    Mem (i, v) LjsInitEnv.ctx_items ->
    st = st' /\ r = L.res_value v.
Proof.
    introv Hinv Hlred Hmem.
    inverts Hlred.
    forwards Hic : state_invariant_includes_init_ctx_lemma Hinv; eauto.
    substs; eauto.
Qed.

Ltac ljs_get_builtin :=
    match goal with
    | Hbinds : binds ?c _ ?v, Hinv : state_invariant _ _ _ ?c ?st |- _ =>
        let H1 := fresh in
        forwards H1 : state_invariant_includes_init_ctx_lemma Hinv Hbinds; [
        unfold LjsInitEnv.ctx_items;
        solve [repeat (eapply Mem_here || apply Mem_next)] | 
        subst_hyp H1 ]
    | Hinv : state_invariant _ _ _ ?c ?st,
      H : L.red_exprh _ ?c ?st (L.expr_basic (E.make_builtin _)) _ |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        forwards (H1&H2) : builtin_assoc Hinv H; [
        unfold LjsInitEnv.ctx_items;
        solve [repeat (eapply Mem_here || apply Mem_next)] | 
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

Ltac ljs_handle_abort := progress (repeat (ljs_propagate_abort || ljs_abort_from_js)); solve_ijauto_js.

Ltac specialize_th_ext_expr_unary H :=
    match type of H with
    | th_ext_expr_unary _ ?e _ _ =>
    match goal with
    | H1 : state_invariant ?BR _ _ ?c ?st, H2 : value_related ?BR1 ?jv ?v,
      H3 : L.red_exprh _ ?c ?st (L.expr_app_2 ?e' ?vl) _ |- _ => 
        let Hsub := fresh "H" in
        asserts Hsub : (BR1 \c BR); [prove_bag |
        unify e e'; unify [v] vl;
        specializes H H1 (value_related_bisim_incl_preserved Hsub H2) H3; 
        clear H1; clear H3; clear Hsub]
    end
    end.

Ltac specialize_th_ext_expr_binary H :=
    match type of H with
    | th_ext_expr_binary _ ?e _ _ =>
    match goal with
    | H1 : state_invariant ?BR _ _ ?c ?st, H2 : value_related ?BR1 ?jv1 ?v1, H3 : value_related ?BR2 ?jv2 ?v2,
      H4 : L.red_exprh _ ?c ?st (L.expr_app_2 ?e' ?vl) _ |- _ => 
        let Hsub1 := fresh "H" in let Hsub2 := fresh "H" in 
        asserts Hsub1 : (BR1 \c BR); [prove_bag |
        asserts Hsub2 : (BR2 \c BR); [prove_bag |
        unify e e'; unify [v1; v2] vl;
        specializes H H1 (value_related_bisim_incl_preserved Hsub1 H2) 
            (value_related_bisim_incl_preserved Hsub2 H3) H4;
        clear H1; clear H4; clear Hsub1; clear Hsub2]]
    end
    end.

Ltac specialize_th_spec H :=
    match type of H with
    | th_spec _ ?e _ _ => 
    match goal with
    | H1 : L.red_exprh _ ?c ?st (L.expr_basic ?e') _, H2 : state_invariant _ _ _ ?c ?st |- _ => 
        unify e e';
        specializes H H2 H1;
        clear H2; clear H1
    end
    end.

Ltac specialize_th_stat H :=
    match type of H with
    | th_stat ?k ?jt => 
    match goal with
    | H1 : L.red_exprh k ?c ?st (L.expr_basic ?e') _, H2 : state_invariant _ _ _ ?c ?st |- _ => 
        unify (js_stat_to_ljs jt) e';
        specializes H H2 H1;
        clear H2; clear H1 
    end 
    end.

Ltac ih_expr_leq :=
    match goal with
    | H : ih_expr ?k |- ih_expr ?k' => is_evar k'; eapply H
    | H : ih_expr ?k |- ih_expr ?k' => eapply ih_expr_leq; try eapply H; omega
    end.

Ltac forwards_th Hth := let H := fresh "H" in 
    (forwards H : Hth;
    first [is_var H; (specialize_th_spec H || specialize_th_stat H || 
           specialize_th_ext_expr_unary H || specialize_th_ext_expr_binary H) | idtac];
    try ih_expr_leq); 
    [idtac].

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

Ltac ljs_autoforward :=
    inv_fwd_ljs || ljs_out_redh_ter || ljs_get_builtin || apply_ih_expr.

(** ** Lemmas about operators *)

(* TODO *)

(** ** Lemmas about the environment *)

(* TODO *)

(** ** Lemmas about specification functions *)

(** *** spec_expr_get_value_conv spec_to_boolean 
    It corresponds to [to_bool] in the desugaring. *)

Lemma red_spec_to_boolean_unary_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privToBoolean J.spec_to_boolean 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv IHe Hinv Hvrel Hlred.
    inverts red_exprh Hlred.
    ljs_apply.

    rewrite from_list_update in H8.
    repeat rewrite from_list_empty in H8. (* TODO *)
    rew_bag_simpl in H8. 

    repeat ljs_autoforward.
    binds_inv.

    inverts Hvrel; try injects; jauto_js.
    cases_if; 
    simpl; unfold J.convert_number_to_bool; cases_if; jauto_js.
    cases_if; 
    simpl; unfold J.convert_string_to_bool; cases_if; jauto_js.
    destruct b; injects; jauto_js.
Qed.

Lemma red_spec_to_number_unary_ok : forall k,
    ih_expr k ->
    th_ext_expr_unary k LjsInitEnv.privToNumber J.spec_to_number
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
Admitted.

Lemma red_spec_to_boolean_ok : forall k je, 
    ih_expr k ->
    th_spec k (E.to_bool (js_expr_to_ljs je))
              (J.spec_expr_get_value_conv J.spec_to_boolean je) 
              (fun _ _ _ _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
                  r = L.res_value (L.value_bool b)).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    ljs_get_builtin.

    repeat inv_internal_fwd_ljs.
    ljs_out_redh_ter.

    apply_ih_expr.

    destr_concl; try ljs_handle_abort.

    repeat inv_internal_fwd_ljs.
    forwards_th red_spec_to_boolean_unary_ok.

    destr_concl.
    res_related_invert.
    resvalue_related_invert.
    jauto_js. left. jauto_js.
    jauto_js. right. jauto_js.
Qed.
