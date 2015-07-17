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

(** ** Statements *)

(** *** debugger *)

Lemma red_stat_debugger_ok : forall k,
    th_stat k (J.stat_debugger).
Proof.
    introv Hcinv Hinv Hlred.
    repeat inv_fwd_ljs.
    jauto_js.
Qed.

(** *** block *)

Lemma stat_block_ejs_last_lemma : forall jts jt,
    E.js_stat_to_ejs (J.stat_block (jts & jt)) = 
        E.expr_seq (E.js_stat_to_ejs (J.stat_block jts)) (E.js_stat_to_ejs jt).
Proof.
    intros. 
    unfolds E.js_stat_to_ejs. 
    unfolds E.expr_seqs.
    rewrite_all list_map_tlc.
    rew_list.
    reflexivity.
Qed.

Lemma red_stat_block_ok : forall jts k, 
    ih_stat k -> 
    th_stat k (J.stat_block jts).
Proof.
    induction jts using list_rev_ind;
    introv IH Hcinv Hinv Hlred.
    inv_fwd_ljs.
    jauto_js.
    unfolds js_stat_to_ljs.
    rewrite stat_block_ejs_last_lemma in *.
    inv_fwd_ljs.
    ljs_out_redh_ter.
    specializes IHjts (ih_stat_S IH). 

    specializes_th IHjts.
    destr_concl_auto.

    inv_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_stat. 

    destr_concl.
    res_related_invert; repeat inv_fwd_ljs; 
    ijauto_js.
Qed.

(** *** with *)

Lemma red_stat_with_ok : forall k je jt,
    ih_expr k ->
    ih_stat k ->
    th_stat k (J.stat_with je jt).
Proof.
    introv IHe IHt Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_object_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th Hx : state_invariant_new_env_record_object_lemma; 
    eauto_js. (* TODO *)
    destruct_hyp Hx.
    repeat ljs_autoforward.
    destr_concl.
    jauto_js 15.
Qed.

(** *** expression statement *)

Lemma red_stat_expr_ok : forall k je, 
    ih_expr k ->
    th_stat k (J.stat_expr je).
Proof.
    introv IH Hcinv Hinv Hlred.
    inverts red_exprh Hlred.
    apply_ih_expr.
    jauto_js.
Qed.

(** *** if *)

Lemma red_stat_if2_ok : forall k je jt1 jt2,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt1 (Some jt2)).
Proof.
    introv IHt IHe Hcinv Hinv Hlred.
    inverts red_exprh Hlred.
    ljs_out_redh_ter.

    forwards_th : red_spec_to_boolean_ok. 

    destr_concl; try ljs_handle_abort.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs. 
    apply_ih_stat.
    jauto_js.
Qed.

Lemma red_stat_if1_ok : forall k je jt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt None).
Proof.
    introv IHt IHe Hcinv Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    forwards_th : red_spec_to_boolean_ok.
 
    destr_concl; try ljs_handle_abort.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs.
    inv_literal_ljs.
    jauto_js.
Qed.

Lemma red_stat_if_ok : forall k je jt ojt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt ojt).
Proof.
    introv IHt IHe.
    destruct ojt.
    applys red_stat_if2_ok; eassumption.
    applys red_stat_if1_ok; eassumption.
Qed.

(** *** while *)

(* TODO move *)
Lemma string_append_right_empty : forall s, s ++ "" = s.
Proof.
    induction s. auto. simpl. rewrite IHs. reflexivity.
Qed.

Lemma string_append_right_injective : forall s1 s2 s, s ++ s1 = s ++ s2 -> s1 = s2.
Proof.
    induction s. auto. introv Heq. injects. auto.
Qed.

(* TODO move *)
Lemma js_label_to_ejs_injective_label : forall s jl1 jl2,
    E.js_label_to_ejs s jl1 = E.js_label_to_ejs s jl2 -> jl1 = jl2.
Proof.
    introv Heq.
    destruct jl1; destruct jl2; unfolds E.js_label_to_ejs; 
    apply string_append_right_injective in Heq; auto; tryfalse. 
    injects. reflexivity.
Qed.

Inductive label_set_hyp jls s : L.res -> L.res -> Prop := 
| label_set_hyp_break : forall jl v, 
    Mem jl jls -> 
    label_set_hyp jls s (L.res_break (E.js_label_to_ejs s jl) v) (L.res_value v)
| label_set_hyp_nomatch : forall jl v,
    ~Mem jl jls -> 
    label_set_hyp jls s (L.res_break (E.js_label_to_ejs s jl) v) (L.res_break (E.js_label_to_ejs s jl) v)
| label_set_hyp_fallthru : forall r,
    (forall jl v, r <> L.res_break (E.js_label_to_ejs s jl) v) ->
    label_set_hyp jls s r r.

Lemma label_set_invert_lemma : forall jls k c st0 s ee st r,
    L.red_exprh k c st0 (L.expr_basic (E.ejs_to_ljs (E.js_label_set_to_labels s jls ee))) (L.out_ter st r) ->
    exists r',
    L.red_exprh k c st0 (L.expr_basic (E.ejs_to_ljs ee)) (L.out_ter st r') /\
    label_set_hyp jls s r' r.
Proof.
    induction jls;
    introv Hlred.
    jauto_set. eassumption. 
    destruct (classic (forall jl v, r <> L.res_break (E.js_label_to_ejs s jl) v)).
    eapply label_set_hyp_fallthru; auto.
    rew_logic in H. destruct H as (jl&H).
    rew_logic in H. destruct H as (v&H).
    rew_logic in H. substs. 
    eapply label_set_hyp_nomatch. trivial. 

    inverts Hlred as Hlred' Hlred''.
    ljs_out_redh_ter.
    specializes IHjls Hlred'. clear Hlred'.
    destruct IHjls as (r'&IHred&IHjls).
    eexists.
    splits.
    inverts Hlred'';
    (eapply L.red_exprh_le; [eassumption | omega]).

    clear IHred.
    inverts IHjls as HypIH; inverts Hlred'' as Hfff.

    eapply label_set_hyp_break. apply Mem_next. assumption.
    
    eapply label_set_hyp_nomatch. intro Hmem.
    inverts Hmem. eapply Hfff. reflexivity. tryfalse.

    apply js_label_to_ejs_injective_label in Hfff. substs. 
    eapply label_set_hyp_break. apply Mem_here.

    apply label_set_hyp_fallthru.
    introv Hr. substs. eapply HypIH. reflexivity.

    false. eapply HypIH. reflexivity.
Qed.

(* TODO move *)
Fixpoint list_pairs {A:Type} (l : list A) :=
    match l with
    | h1::t1 =>
        match t1 with
        | h2::t2 => (h1,h2)::list_pairs t1
        | _ => []
        end
    | _ => []
    end.

Fixpoint init {A : Type} (l : list A) :=
    match l with
    | [] => []
    | [h] => []
    | h :: t => h :: init t
    end.

Lemma init_lemma : forall A l (a a' : A), 
    init (a :: a' :: l) = a :: init (a' :: l).
Proof. auto. Qed.

Inductive First {A : Type} : list A -> A -> Prop :=
    | First_here : forall a t, First (a :: t) a.

Inductive Last {A : Type} : list A -> A -> Prop :=
    | Last_here : forall a, Last [a] a
    | Last_next : forall a h1 h2 t, Last (h2 :: t) a -> Last (h1 :: h2 :: t) a.

Definition while_step k c e1 e2 e3 st2 v2 st1 v1 : Prop := 
    exists st' st'' v v',
    L.red_exprh k c st1 (L.expr_basic e1) (L.out_ter st' (L.res_value L.value_true)) /\
    L.red_exprh k c st' (L.expr_basic e2) (L.out_ter st'' (L.res_value v)) /\
    L.red_exprh k c st'' (L.expr_basic e3) (L.out_ter st2 (L.res_value v')) /\
    v2 = L.overwrite_value_if_empty v1 v.

Definition while_final k c e1 e2 e3 st r st' v : Prop := 
    (exists v', L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st r) /\
        r = L.res_exception v') \/
    (exists s v', L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st (L.res_break s v')) /\
        r = L.res_break s (L.overwrite_value_if_empty v v')) \/
    L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st (L.res_value L.value_false)) /\
        r = L.res_value v \/
    exists st'',
    L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st'' (L.res_value L.value_true)) /\ (
    (exists v', L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st r) /\ 
        r = L.res_exception v') \/
    (exists s v', L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st (L.res_break s v')) /\ 
        r = L.res_break s (L.overwrite_value_if_empty v v')) \/
    exists st''' v', 
    L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st''' (L.res_value v')) /\ (
    (exists v'', L.red_exprh k c st''' (L.expr_basic e3) (L.out_ter st r) /\ 
        r = L.res_exception v'') \/
    (exists s v'', L.red_exprh k c st''' (L.expr_basic e3) (L.out_ter st (L.res_break s v'')) /\
        r = L.res_break s (L.overwrite_value_if_empty v (L.overwrite_value_if_empty v' v''))))). 

Inductive while_unroll k c e1 e2 e3 st r : L.store -> L.value -> Prop :=
| while_unroll_final : forall st0 v0, 
    while_final k c e1 e2 e3 st r st0 v0 -> 
    while_unroll k c e1 e2 e3 st r st0 v0
| while_unroll_step : forall st0 v0 st' v',
    while_step k c e1 e2 e3 st' v' st0 v0 ->
    while_unroll k c e1 e2 e3 st r st' v' ->
    while_unroll k c e1 e2 e3 st r st0 v0.

Hint Extern 4 (L.red_exprh _ ?c ?st ?e ?r) =>
    match goal with
    | H : L.red_exprh _ c st e _ |- _ => 
        eapply L.red_exprh_le; [eapply H | omega]
    end.

Lemma ljs_out_ter_cases : forall st r, (exists v, r = L.res_value v) \/ L.abort (L.out_ter st r).
Proof. intros. destruct r; iauto. Qed.
Ltac ljs_cases_res ee := 
    match goal with
    | H : L.red_exprh _ _ _ ee (L.out_ter ?st ?r) |- _ =>
        is_var r;
        let H := fresh "H" in let v := fresh "v" in
        destruct (ljs_out_ter_cases st r) as [(v&H)|H]; [subst r | idtac] 
    end.

Ltac ljs_abort_inv := 
    match goal with
    | H : L.abort (L.out_ter _ _ ) |- _ => 
        let H' := fresh "H" in
        inverts H as H'; inverts H'
    end.

Lemma while_step_overwrite_lemma : forall k c e1 e2 e3 st v st0 v0 v',
    while_step k c e1 e2 e3 st v st0 v0 ->
    while_step k c e1 e2 e3 st (L.overwrite_value_if_empty v' v) st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hstep.
    unfolds while_step.
    destruct_hyp Hstep.
    repeat eexists; eauto.
    rewrite overwrite_value_if_empty_assoc. reflexivity.
Qed.

Lemma while_final_overwrite_value_lemma : forall k c e1 e2 e3 st st0 v v0 v',
    while_final k c e1 e2 e3 st (L.res_value v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_value (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse; iauto.
Qed.

Lemma while_unroll_overwrite_value_lemma : forall k c e1 e2 e3 st st0 v v0 v',
    while_unroll k c e1 e2 e3 st (L.res_value v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_value (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hwhile. 
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_overwrite_value_lemma.
    (* step *)
    eapply while_unroll_step.
    eauto using while_step_overwrite_lemma.
    assumption.
Qed.

Lemma while_final_overwrite_break_lemma : forall k c e1 e2 e3 st st0 v v0 v' s,
    while_final k c e1 e2 e3 st (L.res_break s v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_break s (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof. 
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse.
    right. left. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
    right. right. right. eexists. split. eassumption. 
        right. left. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
    right. right. right. eexists. split. eassumption. right. right. do 2 eexists. split. eassumption.
        right. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
Qed.

Lemma while_unroll_overwrite_break_lemma : forall k c e1 e2 e3 st st0 v v0 v' s,
    while_unroll k c e1 e2 e3 st (L.res_break s v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_break s (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hwhile. 
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_overwrite_break_lemma.
    (* step *)
    eapply while_unroll_step.
    eauto using while_step_overwrite_lemma.
    assumption.
Qed.

Lemma while_final_exception_lemma : forall k c e1 e2 e3 st st0 v v0 v1,
    while_final k c e1 e2 e3 st (L.res_exception v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_exception v) st0 v1.
Proof.
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse.
    iauto.
    right. right. right. eexists. split. eassumption. left. iauto.
    right. right. right. eexists. split. eassumption. 
        right. right. do 2 eexists. split. eassumption. left. iauto. 
Qed.

Lemma while_step_exception_lemma : forall k c e1 e2 e3 st v st0 v0 v0',
    while_step k c e1 e2 e3 st v st0 v0 -> exists v',
    while_step k c e1 e2 e3 st v' st0 v0'.
Proof.
    introv Hstep.
    unfolds while_step.
    destruct_hyp Hstep.
    repeat eexists; eauto. 
Qed.

Lemma while_unroll_exception_lemma : forall k c e1 e2 e3 st st0 v v0 v1,
    while_unroll k c e1 e2 e3 st (L.res_exception v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_exception v) st0 v1.
Proof.
    introv Hwhile.
    gen v1.
    inductions Hwhile; intros.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_exception_lemma.
    (* step *)
    forwards Hl : while_step_exception_lemma. eassumption.
    destruct Hl as (v_arb&Hl).
    eapply while_unroll_step; [apply Hl | eapply IHHwhile].
Qed.

Lemma while_final_leq_lemma : forall k k' c e1 e2 e3 st r st0 v0,
    while_final k c e1 e2 e3 st r st0 v0 ->
    (k' >= k)%nat -> 
    while_final k' c e1 e2 e3 st r st0 v0.
Proof.
    introv Hfinal Hleq.
    unfolds while_final.
    destruct_hyp Hfinal; repeat (eexists || iauto || right).
Qed.

Lemma while_step_leq_lemma : forall k k' c e1 e2 e3 st v st0 v0,
    while_step k c e1 e2 e3 st v st0 v0 ->
    (k' >= k)%nat -> 
    while_step k' c e1 e2 e3 st v st0 v0.
Proof.
    introv Hstep Hleq.
    unfolds while_step.
    destruct_hyp Hstep; repeat eexists; iauto.
Qed.

Lemma while_unroll_leq_lemma : forall k k' c e1 e2 e3 st r st0 v0,
    while_unroll k c e1 e2 e3 st r st0 v0 ->
    (k' >= k)%nat -> 
    while_unroll k' c e1 e2 e3 st r st0 v0.
Proof.
    introv Hwhile Hleq.
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eapply while_final_leq_lemma. eassumption. omega.
    (* step *)
    eapply while_unroll_step.
    eapply while_step_leq_lemma. eassumption. omega.
    eauto.
Qed.

(* TODO: move to utils *)
Definition freeze (P : Prop) : Prop := P.
Lemma freeze_intro : forall (P : Prop), P -> freeze P. Proof. auto. Qed. 
Lemma freeze_elim : forall (P : Prop), freeze P -> P. Proof. auto. Qed.

Opaque freeze. 

Ltac freeze E := apply freeze_intro in E.
Ltac unfreeze E := apply freeze_elim in E.

Definition ejs_while_body_closure c ee1 ee2 ee3 := L.value_closure 
        (L.closure_intro (to_list c) (Some "#while_loop") [] 
            (E.while_body (E.ejs_to_ljs ee1) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3))).

Lemma ejs_while_body_lemma : forall k c c' st0 ee1 ee2 ee3 st r,
    c = (c' \("#while_loop" := ejs_while_body_closure c' ee1 ee2 ee3)) ->
    L.red_exprh k c st0 (L.expr_basic (E.while_body (E.ejs_to_ljs ee1) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3)))
        (L.out_ter st r) ->
    while_unroll k c (E.to_bool (E.ejs_to_ljs ee1)) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3) st r st0 L.value_empty.
Proof.
    introv Hctx Heq.
    asserts Hbinds : (binds c "#while_loop" (ejs_while_body_closure c' ee1 ee2 ee3)).
    substs. prove_bag.
    unfolds ejs_while_body_closure.
    freeze Hctx. 
    inv_ljs_stop (L.expr_basic (E.to_bool (E.ejs_to_ljs ee1))).
    inv_ljs_stop (L.expr_basic (E.ejs_to_ljs ee1)).
    inv_ljs_stop (L.expr_basic (E.ejs_to_ljs ee2)).
    gen st0 st r.
    induction_wf IH : lt_wf k.
    introv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.
    inv_internal_ljs. 
    (* condition true *)
    inv_fwd_ljs.
    ljs_out_redh_ter.
    inv_internal_ljs.
    (* body returns a value *)
    inv_fwd_ljs.
    repeat ljs_out_redh_ter.
    ljs_cases_res (L.expr_basic (E.ejs_to_ljs ee3)).
    (* after returns a value *)
    repeat ljs_autoforward.
    inverts red_exprh H0. (* TODO! *)
    (* ljs_apply. *) (*ljs_inv_value_is_closure;*) ljs_inv_closure_ctx; ljs_closure_body. (* TODO *)
    rewrite from_list_empty in H6.
    repeat rew_bag_simpl in H6.
    unfreeze Hctx.
    rewrite <- Hctx in H6.
    freeze Hctx.
    specializes IH H6. omega.
    eapply while_unroll_step.
    repeat eexists. eauto. eauto. eauto.
    inv_internal_ljs. 
    rewrite overwrite_value_if_empty_left_empty.
    eapply while_unroll_overwrite_value_lemma in IH.
    rewrite overwrite_value_if_empty_right_empty in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.
    eapply while_unroll_exception_lemma in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.
    rewrite overwrite_value_if_empty_left_empty.
    eapply while_unroll_overwrite_break_lemma in IH.
    rewrite overwrite_value_if_empty_right_empty in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.    
    (* after aborted *)
    apply while_unroll_final. right. right. right. eexists. split. eauto. right. right. do 2 eexists. split. eauto.
    ljs_abort_inv; repeat inv_fwd_ljs.
    iauto.
    right. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto.
    (* body aborted *)
    apply while_unroll_final. right. right. right. eexists. split. eauto.
    ljs_abort_inv.
    left. eexists. eauto.
    right. left. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto. 
    (* condition false *)
    inv_fwd_ljs.
    apply while_unroll_final. unfolds. iauto. 
    (* condition aborted *)
    apply while_unroll_final.
    ljs_abort_inv.
    left. iauto.
    right. left. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto.
Qed.

Lemma exprjs_while_lemma : forall k c c' st0 ee1 ee2 ee3 st r,
    c = c'\("#while_loop" := ejs_while_body_closure c' ee1 ee2 ee3) ->
    L.red_exprh k c' st0 (L.expr_basic (E.ejs_to_ljs (E.expr_while ee1 ee2 ee3))) (L.out_ter st r) ->
    exists k', 
    while_unroll k' c (E.to_bool (E.ejs_to_ljs ee1)) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3) st r st0 L.value_empty /\ 
    (k' < k) % nat.
Proof.
    introv Hctx Hlred.
    substs.
    repeat inv_fwd_ljs.
    binds_inv.
    inverts H7. (* TODO *)

    unfolds L.add_closure.
    (* ljs_apply. *) (*ljs_inv_value_is_closure;*) ljs_inv_closure_ctx; ljs_closure_body. (* TODO *)
    rewrite from_list_empty in H8. (* TODO *)
    rew_bag_simpl in H8.
    eexists. split.
    eapply ejs_while_body_lemma. reflexivity. eassumption.
    omega.
Qed.

Definition while_body_closure c je jt := ejs_while_body_closure c (E.js_expr_to_ejs je) (E.js_stat_to_ejs jt).

Definition js_labelset_stat_to_ljs jls jt :=
    E.ejs_to_ljs (E.js_label_set_to_labels "%continue" jls (E.js_stat_to_ejs jt)).

Definition js_expr_to_bool_ljs je := E.to_bool (js_expr_to_ljs je).

Lemma red_stat_while_lemma : forall k k' jls je jt v jrv,
    ih_stat k ->
    ih_expr k ->
    (k' < k)%nat ->
    forall BR jst jc c st st' r r', 
    while_unroll k' c (js_expr_to_bool_ljs je) (js_labelset_stat_to_ljs jls jt) L.expr_undefined st' r' st v ->
    label_set_hyp jls "%break" r' r ->
    resvalue_related BR jrv v ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' jst' jr,
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    J.red_stat jst jc (J.stat_while_1 jls je jt jrv) (J.out_ter jst' jr) /\ 
    res_related BR' jst' st' jr r.
Proof.
    introv IHt IHe Hlt Hwhile.
    inductions Hwhile gen jrv jst BR;
    introv Hlabel_brk Haccum Hcinv Hinv.
    (* final *)
    destruct H as [Hwf|[Hwf|[Hwf|(?st&Hcond&Hwf1)]]]; try destruct_hyp Hwf.
    (* condition throws *)
    forwards_th : red_spec_to_boolean_ok.
    inverts Hlabel_brk. 
    destr_concl. tryfalse.
    jauto_js.
    (* condition breaks, IMPOSSIBLE *)
    forwards_th : red_spec_to_boolean_ok.
    destr_concl. tryfalse.
    res_related_invert; tryfalse.
    (* condition false *)
    forwards_th : red_spec_to_boolean_ok.
    inverts Hlabel_brk.
    destr_concl.   
    injects.
    jauto_js. 
    eauto_js. 
    (* condition true *)
    forwards_th : red_spec_to_boolean_ok.
    destr_concl; try js_abort_rel_contr; [idtac].
    injects.
    destruct Hwf1 as [Hwf|[Hwf|(?st&?v&Hstat&Hwf1)]]; try destruct_hyp Hwf.
    (* statement throws *) 
    apply label_set_invert_lemma in Hwf0.
    destruct Hwf0 as (r''&Hlred&Hlabel_cont). (* TODO add tactic *)
    apply_ih_stat.
    destr_concl. 
    inverts Hlabel_brk.
    inverts Hlabel_cont.
    res_related_invert. 
    jauto_js 15.
    (* statement breaks *)
    apply label_set_invert_lemma in Hwf0.
    destruct Hwf0 as (r''&Hlred&Hlabel_cont). (* TODO add tactic *)
    apply_ih_stat.
    destr_concl.
    inverts Hlabel_cont. 
    (* continue with wrong label *)
    inverts Hlabel_brk.
    res_related_invert.
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. intro. jauto_js.
    eapply J.red_stat_while_5_not_break. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    autorewrite with js_ljs.
    skip. (* eapply J.red_stat_while_6_abort. *) (* TODO SPECIFICATION PROBLEM! ASK ALAN *)
    (* not continue *)
    inverts Hlabel_brk.
    (* actual break *)
    res_related_invert.
    jauto_js 15. 
    (* break with wrong label *)
    res_related_invert.
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_5_not_break. intro. jauto_js. (* intro. jauto_set. apply H6. eauto with js_ljs. *)
    autorewrite with js_ljs.
    skip. (* eapply J.red_stat_while_6_abort. *) (* TODO SPECIFICATION PROBLEM! ASK ALAN *)
    (* only return remains *)
    res_related_invert; tryfalse.
    jauto_js 15.
    (* statement returns a value *)
    apply label_set_invert_lemma in Hstat.
    destruct Hstat as (r''&Hlred&Hlabel_cont). (* TODO add tactic *) 
    apply_ih_stat. 
    destr_concl. 
    inverts Hlabel_cont. 
    (* statement continued *)
    destruct_hyp Hwf1; inv_ljs.
    (* statement not continued *)
    destruct_hyp Hwf1; inv_ljs.
    (* step *)
    destruct H as (?st&?st&?v&?v&Hcond&Hstat&Hafter&EQv').
    substs.
    inverts Hafter. 
    apply label_set_invert_lemma in Hstat.
    destruct Hstat as (?r&Hstat&Hlabel_cont).
    forwards_th : red_spec_to_boolean_ok.
    destr_concl. 
    injects.
    apply_ih_stat.
    destr_concl.
    inverts Hlabel_cont.
    (* statement continued *)
    res_related_invert.
    forwards_th : IHHwhile. 
    eassumption.
    eauto_js.
    jauto_js 8.
    (* statement not continued *)
    res_related_invert.
    forwards_th : IHHwhile. 
    eassumption.
    eauto_js.
    jauto_js 15.
    res_related_invert. eauto_js. (* TODO *)
Qed.

Lemma red_stat_while_ok : forall k jls je jt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_while jls je jt).
Proof.
    introv IHt IHe Hcinv Hinv Hlred.
    unfolds js_stat_to_ljs. simpls. 
    apply label_set_invert_lemma in Hlred.
    destruct Hlred as (r'&Hlred&Hlabel).
    apply (exprjs_while_lemma eq_refl) in Hlred.
    sets_eq c' : (c\("#while_loop" := ejs_while_body_closure c (E.js_expr_to_ejs je)
        (E.js_label_set_to_labels "%continue" jls (E.js_stat_to_ejs jt)) E.expr_undefined)). 
    asserts Hcinv' : (context_invariant BR jc c'). substs. jauto_js. 
    destruct Hlred as (k'&Hwhile&Hk).
    lets Hlemma : red_stat_while_lemma IHt IHe Hk Hwhile Hlabel.
    specializes Hlemma resvalue_related_empty Hcinv' Hinv. (* TODO TLC lets too small ;) *)
    destruct_hyp Hlemma.
    substs.
    jauto_js.
Qed.
 
(** *** switch *)

Lemma red_stat_switch_nodefault_ok : forall k ls je cl,
    ih_stat k -> 
    ih_expr k -> 
    th_stat k (J.stat_switch ls je (J.switchbody_nodefault cl)).
Proof.
    introv IHt IHe Hcinv Hinv Hlred.
    unfolds js_stat_to_ljs. simpls.
    apply label_set_invert_lemma in Hlred.
    destruct Hlred as (r'&Hlred&Hlabel).
    repeat ljs_autoforward.
    rewrite_all list_map_tlc in *.
    destr_concl. 
    repeat ljs_autoforward.
    skip. (* TODO *)
    (* TODO better tactic for abort through label sets? *)
    ljs_abort_from_js. ljs_propagate_abort. 
    inverts Hlabel; ljs_abort_inv; res_related_invert; tryfalse.
    jauto_js. 
Qed.

Lemma red_stat_switch_withdefault_ok : forall k ls je cl1 cl2 sts,
    ih_stat k -> 
    ih_expr k -> 
    th_stat k (J.stat_switch ls je (J.switchbody_withdefault cl1 sts cl2)).
Proof.
Admitted.

Lemma red_stat_switch_ok : forall k ls je sb,
    ih_stat k -> 
    ih_expr k -> 
    th_stat k (J.stat_switch ls je sb).
Proof.
    introv IHt IHe. 
    destruct sb.
    applys red_stat_switch_nodefault_ok; assumption.
    applys red_stat_switch_withdefault_ok; assumption.
Qed.

(** *** return *)

Lemma red_stat_return_ok : forall k oje,
    ih_expr k ->
    th_stat k (J.stat_return oje).
Proof.
    introv IHe Hcinv Hinv Hlred.
    inverts red_exprh Hlred.
    ljs_out_redh_ter.
    destruct oje as [je|].
    apply_ih_expr.
    inv_internal_ljs.
    jauto_js.
    injects.
    jauto_js.
    jauto_js.
    ljs_abort.
    simpls.
    inv_literal_ljs.
    inv_internal_fwd_ljs.
    jauto_js.
Qed.

(** *** break *)

Lemma red_stat_break_ok : forall k jl,
    th_stat k (J.stat_break jl).
Proof.
    introv Hcinv Hinv Hlred.
    repeat inv_fwd_ljs.
    jauto_js.
Qed.

(** *** continue *)

Lemma red_stat_continue_ok : forall k jl,
    th_stat k (J.stat_continue jl).
Proof.
    introv Hcinv Hinv Hlred.
    repeat inv_fwd_ljs.
    jauto_js.
Qed.

(** *** label *)

Lemma red_stat_label_ok : forall k s jt,
    ih_stat k ->
    th_stat k (J.stat_label s jt).
Proof.
    introv IHt Hcinv Hinv Hlred.
    repeat inv_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_stat.

    destr_concl.
    res_related_invert;
    repeat inv_fwd_ljs;
    unfolds E.js_label_to_ejs;
    repeat inv_fwd_ljs;
    try solve [jauto_js].
    destruct jl;
    inv_internal_ljs; try injects;
    jauto_js.
    destruct (classic (s = s0)).
    substs. false. eapply H6. jauto_js. (* TODO *)
    jauto_js.
Qed. 

(** *** try-catch-finally *)

(* TODO move *)
Ltac js_exn_object_ptr_invert :=
    match goal with
    | H : js_exn_object_ptr _ _ _ |- _ => inverts H
    end.

Lemma js_exn_object_extract_lemma : forall obj v st oattr,
    js_exn_object obj v ->
    L.object_property_is st obj "%js-exn" oattr ->
    oattr = Some (L.attributes_data_of (L.attributes_data_intro v false false false)).
Proof.
    introv Hex Hpis.
    destruct Hex.
    inverts Hpis; try (false; prove_bag).
    binds_determine. reflexivity. 
Qed.

Ltac js_exn_object_extract :=
    match goal with
    | Hex : js_exn_object ?obj _, Hpis : L.object_property_is _ ?obj "%js-exn" _ |- _ =>
        let H := fresh in
        lets H : js_exn_object_extract_lemma Hex Hpis;
        destruct_hyp H;
        clear Hpis
    end.

Lemma red_stat_try_catch_ok : forall k jt1 jt2 s,
    ih_stat k ->
    th_stat k (J.stat_try jt1 (Some (s, jt2)) None).
Proof.
    introv IHt Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl.
    inv_ljs.
    res_related_invert; solve [false; jauto] || jauto_js.  
    res_related_invert.
    repeat ljs_autoforward.
    inverts red_exprh H6. (* TODO *)
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : state_invariant_new_env_record_decl_lemma. 
    eassumption.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    js_exn_object_ptr_invert.
    asserts Ha : (ptr0 <> fresh st0). { intro. substs. eapply fresh_index. prove_bag. } (* TODO *)
    binds_inv. binds_determine.
    js_exn_object_extract.
    repeat ljs_autoforward.
    inverts Hx0. (* TODO *)
    forwards_th Hx : decl_env_add_mutable_binding_lemma.
    prove_bag. 
    eapply js_state_next_fresh_binds_env_record_preserved. eapply binds_update_same.
    eassumption.
    jauto_js. 
    destruct_hyp Hx.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    jauto_js 8.
Qed.

Lemma red_stat_try_catch_finally_ok : forall k jt1 jt2 jt3 s,
    ih_stat k ->
    th_stat k (J.stat_try jt1 (Some (s, jt2)) (Some jt3)).
Proof.
Admitted. (*
    introv IHt Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl.
    inv_fwd_ljs. 
    inverts red_exprh H1. (* TODO *) (* try-catch *)
    {
    repeat ljs_autoforward.
    
    res_related_invert; tryfalse.
    destr_concl.
    inverts H0.


Qed.
*)

Lemma red_stat_try_finally_ok : forall k jt1 jt2,
    ih_stat k ->
    th_stat k (J.stat_try jt1 None (Some jt2)).
Proof.
    introv IHt Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl.
    repeat ljs_autoforward.
    inv_fwd_ljs.
    repeat ljs_autoforward.
    destr_concl.
    inv_ljs;
    res_related_invert;
    res_related_invert;
    try ljs_abort;
    jauto_js 6.
Qed.

(** *** throw *)

Lemma red_stat_throw_ok : forall k je,
    ih_expr k ->
    th_stat k (J.stat_throw je).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.
    destr_concl; try ljs_handle_abort.
    repeat ljs_autoforward. 
    forwards_th H : priv_js_error_lemma.
    destruct_hyp H.
    repeat ljs_autoforward.
    jauto_js.
Qed.
