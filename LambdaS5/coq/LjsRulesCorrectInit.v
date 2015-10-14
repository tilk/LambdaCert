Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
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

Fixpoint suffixes T (l : list T) :=
    match l with
    | nil => nil
    | h::t => l::suffixes t
    end.

Definition head_not_in_tail T (l : list T) := 
    match l with
    | [] => True
    | h::t => ~Mem h t
    end.

Definition all_different T (l : list T) := Forall (@head_not_in_tail T) (suffixes l).

Lemma Mem_map_lemma : forall A B a (l : list A) (f : A -> B),
    Mem a l -> Mem (f a) (map f l).
Proof.
    hint Mem_here, Mem_next.
    introv Hmem. induction Hmem; rew_map; iauto.
Qed.

Lemma all_different_mem_assoc : forall A B (a:A) (b:B) l,
    all_different (map fst l) ->
    Mem (a, b) l ->
    Assoc a b l.
Proof.
    introv Had Hmem.
    induction l as [|(a'&b') l].
    + inverts Hmem.
    + inverts Hmem as Hmem.
      - eapply Assoc_here.
      - rew_map in Had. inverts Had as Hhn Had. simpl in Hhn.
        specializes IHl Had Hmem.
        asserts Hamem : (Mem (fst (a,b)) (map fst l)). { applys~ Mem_map_lemma. } simpl in Hamem.
        destruct (classic (a = a')) as [HEq|HEq]. 
        * subst a. tryfalse.
        * applys~ Assoc_next.
Qed.

Fixpoint nats k :=
    match k with
    | S k' => k'::nats k'
    | 0 => nil
    end.

Definition nats_asc k := rev (nats k).

Lemma store_items_is_nats_list : exists k, map fst LjsInitEnv.store_items = nats_asc k.
Proof.
    sets_eq l : (map fst LjsInitEnv.store_items).
    unfolds LjsInitEnv.store_items.
    rewrite <- list_map_tlc in EQl.
    simpl in EQl.
    exists (S (List.last l 0)).
    substs. reflexivity.
Qed.

Lemma nats_less : forall k k', Mem k (nats k') -> (k < k')%nat.
Proof.
    introv H. inductions H; destruct k'; tryfalse; injects.
    + math.
    + specializes IHMem ___. reflexivity. math. 
Qed.

Lemma all_different_nats : forall k, all_different (nats k).
Proof.
    induction k.
    + eapply Forall_nil.
    + simpl. eapply Forall_cons.
      - applys contrapose_intro nats_less. math.
      - assumption.
Qed.

Lemma Mem_last_eq : forall A (x y:A) l,
    Mem x (l&y) = ((x = y) \/ (Mem x l)).
Proof.
    introv. rewrite Mem_app_or_eq.
    asserts_rewrite (Mem x [y] = (x=y)). {
        rewrite Mem_cons_eq. rewrite Mem_nil_eq. extens. iff*.
    }
    extens. iff*.
Qed.

Lemma Mem_last_cons : forall A (x y:A) l, Mem x (l&y) = Mem x (y::l).
Proof.
    introv. rewrite Mem_last_eq. rewrite Mem_cons_eq. reflexivity.
Qed.

Lemma head_not_in_tail_last : forall T x y (l : list T),
    x <> y -> head_not_in_tail (x :: l) -> head_not_in_tail (x :: l & y).
Proof.
    introv Hdiff. eapply contrapose_intro. rewrite Mem_last_cons. intro H.
    inverts* H.
Qed.

Lemma all_different_last : forall T x (l : list T), 
    all_different l -> head_not_in_tail (x :: l) -> all_different (l & x).
Proof.
    introv Had Hht.
    induction l.
    + applys~ Forall_cons.
    + inverts Had as Hnt Had. 
      specializes IHl Had __. applys contrapose_intro Mem_next Hht.
      rew_list. applys~ Forall_cons.
      applys~ head_not_in_tail_last. applys contrapose_intro Hht. intro. substs. apply Mem_here.
Qed.

Lemma all_different_rev : forall T (l : list T), all_different l -> all_different (rev l).
Proof.
    introv Had.
    induction l as [|x l]; rew_rev.
    + assumption.
    + inverts Had as Hnt Had. specializes IHl Had.
      applys~ all_different_last. applys contrapose_intro Hnt.
      intro H. apply Mem_rev in H. rew_rev in H. assumption.
Qed. 

Lemma all_different_nats_asc : forall k, all_different (nats_asc k).
Proof.
    introv. unfolds nats_asc. applys all_different_rev. applys all_different_nats.
Qed.

Lemma all_different_store_items :
    all_different (map fst LjsInitEnv.store_items).
Proof.
    lets H : store_items_is_nats_list.
    destruct H as (?&H). rewrite H.
    apply all_different_nats_asc.
Qed.

Lemma init_store_mem_binds : forall k obj,
    Mem (k, obj) LjsInitEnv.store_items ->
    binds LjsInitEnv.init_store k obj.
Proof.
    introv Hmem.
    eapply from_list_binds_inv.
    applys~ all_different_mem_assoc. apply all_different_store_items.
Qed.

Lemma init_heaps_bisim_obj_ok : heaps_bisim_obj initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    introv Hb1 Hb2.
    destruct Hx1.
    apply from_list_binds in Hb2.
Admitted. (* TODO *)

Lemma init_heaps_bisim_env_ok : heaps_bisim_env initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    introv Hb1 Hb2.
Admitted. (* TODO *)

Lemma init_heaps_bisim_lfun_obj_ok : heaps_bisim_lfun_obj initBR.
Proof.
    introv Hf1 Hf2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; tryfalse; repeat injects.
    determine. reflexivity.
Qed.

Lemma init_heaps_bisim_lfun_env_ok : heaps_bisim_lfun_env initBR.
Proof.
    introv Hf1 Hf2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; tryfalse; repeat injects.
    reflexivity.
Qed.

Lemma init_heaps_bisim_rfun_ok : heaps_bisim_rfun initBR.
Proof.
    introv Hf1 Hf2 Hfp1 Hfp2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; inverts Hfp1; inverts Hfp2; try false_invert.
    + reflexivity.
    + rewrite <- flip_eq in H1x1, H2x1. determine. reflexivity.
Qed.

Lemma init_heaps_bisim_ltotal_obj_ok : heaps_bisim_ltotal_obj initBR JsInit.state_initial.
Proof.
    introv Hidx.
Admitted. (* TODO *)

Lemma init_heaps_bisim_ltotal_env_ok : heaps_bisim_ltotal_env initBR JsInit.state_initial.
Proof.
    introv Hidx.
    (* TODO simpler? *)
    unfolds JsInit.state_initial. simpls.
    unfolds JsCertExt.env_record_indom. simpls.
    unfolds JsInit.env_record_heap_initial.
    rewrite heap_indom_to_libbag_eq in Hidx. rew_heap_to_libbag in Hidx.
    rew_index_eq in Hidx. rew_logic in Hidx. substs.
    eexists. unfold initBR. rew_in_eq. eapply Mem_next. eapply Mem_here.
Qed.

Lemma init_heaps_bisim_lnoghost_obj_ok : heaps_bisim_lnoghost_obj initBR JsInit.state_initial.
Proof.
Admitted. (* TODO *)

Lemma init_heaps_bisim_lnoghost_env_ok : heaps_bisim_lnoghost_env initBR JsInit.state_initial.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    (* TODO simpler? *)
    unfolds JsInit.state_initial. simpl.
    unfolds JsCertExt.env_record_indom. simpl.
    unfolds JsInit.env_record_heap_initial. 
    rewrite heap_indom_to_libbag_eq. rew_heap_to_libbag. prove_bag.
Qed.

Lemma init_heaps_bisim_rnoghost_ok : heaps_bisim_rnoghost initBR LjsInitEnv.init_store.
Proof.
    introv Hf Hfp. lets Hx : initBR_members Hf.
    unfolds LjsInitEnv.init_store. rewrite index_binds_eq.
    destruct_hyp Hx; inverts Hfp.
Admitted. (* TODO *)

Lemma init_heaps_bisim_consistent_ok :
    heaps_bisim_consistent initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    constructor.
    + apply init_heaps_bisim_obj_ok.
    + apply init_heaps_bisim_env_ok.
    + introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse.
    + apply init_heaps_bisim_lfun_obj_ok.
    + apply init_heaps_bisim_lfun_env_ok.
    + apply init_heaps_bisim_rfun_ok.
    + apply init_heaps_bisim_ltotal_obj_ok.
    + apply init_heaps_bisim_ltotal_env_ok.
    + apply init_heaps_bisim_lnoghost_obj_ok.
    + apply init_heaps_bisim_lnoghost_env_ok.
    + apply init_heaps_bisim_rnoghost_ok.
Qed.

Lemma init_state_invariant_ok :
    state_invariant initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    constructor. 
    + apply init_heaps_bisim_consistent_ok.
    + skip.
    + skip. (* TODO *)
Qed.

Lemma env_records_exist_initial : env_records_exist_env initBR J.lexical_env_initial.
Proof.
    unfolds J.lexical_env_initial.
    introv Hm. inverts Hm; try false_invert. jauto_js.
Qed.

Lemma init_context_invariant_ok : forall b,
    context_invariant initBR (J.execution_ctx_initial b) LjsInitEnv.init_ctx.
Proof.
    constructor.
    + prove_bag.
    + apply execution_ctx_related_init_ctx.
    + apply includes_init_ctx_init_ctx.
    + constructor; apply env_records_exist_initial.
Qed.
