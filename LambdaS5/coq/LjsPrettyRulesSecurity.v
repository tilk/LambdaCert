Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesIndexed.
Require Import LjsPrettyRulesIndexedAux.
Require Import LjsPrettyRulesIndexedInvert.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import JsNumber.
Import List.ListNotations.

Open Scope list_scope.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.
Implicit Type attrs : attributes.

Inductive attributes_security_ok : attributes -> attributes -> Prop := 
| attributes_security_ok_accessor : forall acc,
    attributes_security_ok (attributes_accessor_of acc) (attributes_accessor_of acc)
| attributes_security_ok_data_unwritable : forall data,
    !attributes_data_writable data ->
    attributes_security_ok (attributes_data_of data) (attributes_data_of data)
| attributes_security_ok_data_writable : forall data data',
    attributes_data_writable data ->
    attributes_data_enumerable data = attributes_data_enumerable data' ->
    attributes_data_configurable data = attributes_data_configurable data' ->
    attributes_security_ok (attributes_data_of data) (attributes_data_of data')
.

Record object_security_ok obj obj' : Prop := {
    object_security_ok_class :
        object_class obj = object_class obj';
    object_security_ok_code :
        object_code obj = object_code obj';
    object_security_ok_proto : 
        !object_extensible obj -> object_proto obj = object_proto obj';
    object_security_ok_extensible : 
        !object_extensible obj -> !object_extensible obj';
    object_security_ok_properties : 
        !object_extensible obj -> forall s, index (object_properties obj') s -> index (object_properties obj) s;
    object_security_ok_attributes : forall s attrs,
        binds (object_properties obj) s attrs -> 
        !attributes_configurable attrs -> 
        exists attrs',
        binds (object_properties obj') s attrs' /\ 
        !attributes_configurable attrs' /\
        attributes_security_ok attrs attrs'
}.

Definition state_security_ok st st' : Prop :=
    forall ptr obj,
    binds st ptr obj -> exists obj',
    binds st' ptr obj' /\
    object_security_ok obj obj'.

Lemma attributes_security_ok_refl : refl attributes_security_ok.
Proof.
    intro attrs.
    destruct attrs as [()|()].
    destruct attributes_data_writable.
    apply attributes_security_ok_data_writable; auto.
    apply attributes_security_ok_data_unwritable; auto.
    apply attributes_security_ok_accessor.
Qed.

Lemma object_security_ok_refl : refl object_security_ok.
Proof.
    intro obj.
    destruct obj.
    destruct object_attrs.
    constructor; eauto using attributes_security_ok_refl.
Qed.

Lemma state_security_ok_refl : refl state_security_ok.
Proof.
    intro st. unfolds. eauto using object_security_ok_refl.
Qed.

Lemma attributes_security_ok_trans : trans attributes_security_ok.
Proof.
    introv Hs1 Hs2.
    inverts Hs1; inverts Hs2.
    apply attributes_security_ok_accessor.
    apply attributes_security_ok_data_unwritable; auto.
    rew_refl in *; tryfalse.
    apply attributes_security_ok_data_writable; auto.
    apply attributes_security_ok_data_writable; auto; eapply eq_trans; eauto.
Qed.

Lemma object_security_ok_trans : trans object_security_ok.
Proof.
    introv Hs1 Hs2.
    inverts Hs1. inverts Hs2.
    constructor. 
    eapply eq_trans; eauto.
    eapply eq_trans; eauto.
    intro. apply (eq_trans (object_proto y)); eauto. 
    eauto.
    eauto.
    introv Hbinds1 Hc1.
    specializes object_security_ok_attributes0 Hbinds1 Hc1.
    destruct object_security_ok_attributes0 as (?attrs&Hbinds2&Hc2&Hok1).
    specializes object_security_ok_attributes1 Hbinds2 Hc2.
    destruct object_security_ok_attributes1 as (?attrs&Hbinds3&Hc3&Hok2).
    jauto_set; eauto. applys attributes_security_ok_trans Hok1 Hok2.
Qed.

Lemma state_security_ok_trans : trans state_security_ok.
Proof.
    introv Hs1 Hs2.
    unfolds state_security_ok.
    introv Hbinds1.
    specializes Hs1 Hbinds1.
    destruct Hs1 as (?obj&Hbinds2&Hok1).
    specializes Hs2 Hbinds2.
    destruct Hs2 as (?obj&Hbinds3&Hok2).
    jauto_set; eauto. applys object_security_ok_trans Hok1 Hok2.
Qed.

Local Ltac ljs_inv := 
    match goal with
    | H : red_exprh _ _ _ ?e _ |- _=>
        match e with
        | expr_basic _ => fail 1
        | _ => inverts red_exprh H; tryfalse
        end
    end.

Local Ltac apply_hyp H1 :=
    match goal with
    | H : red_exprh _ _ _ _ _ |- _ => apply H1 in H
    end.

Local Ltac state_security_ok_trans :=
    match goal with
    | H : state_security_ok ?st _ |- state_security_ok ?st _ => applys state_security_ok_trans H; clear H
    end.

Local Hint Resolve attributes_security_ok_refl.
Local Hint Resolve object_security_ok_refl.

Lemma state_security_ok_set_attributes : forall st ptr obj s attrs pa v,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_pattr_writable attrs pa ->
    attributes_pattr_valid pa v ->
    state_security_ok st (st \(ptr := set_object_property obj s (set_attributes_pattr attrs pa v))).
Proof.
    introv Hbinds Habinds Hwritable Hvalid Hbinds'.
    destruct (classic (ptr = ptr0)).
    + subst. binds_determine. eexists. split. prove_bag. destruct obj. constructor; eauto.
      - introv Hnext Hidx. destruct (classic (s = s0)).
        * subst. prove_bag.
        * unfolds set_object_property. eapply index_update_diff_inv; eauto.
      - introv Hbinds Hattrs. rew_refl in Hattrs. destruct (classic (s = s0)).
        * subst. binds_determine. inverts Hwritable as HHH; tryfalse;
          destruct data; unfolds set_object_property.
          { eexists. rew_refl. splits. prove_bag. prove_bag. applys~ attributes_security_ok_data_writable. }
          { eexists. rew_refl. splits. prove_bag. prove_bag. applys~ attributes_security_ok_data_writable. }
        * unfolds set_object_property. eexists. rew_refl. prove_bag.
    + prove_bag.
Qed.

Lemma state_security_ok_new_attributes : forall st ptr obj s p v,
    binds st ptr obj ->
    ~index (object_properties obj) s ->
    object_extensible obj ->
    attributes_pattr_valid p v ->
    state_security_ok st (st \(ptr := set_object_property obj s (new_attributes_pattr p v))).
Proof.
    introv Hbinds Habinds Hextensible Hvalid Hbinds'.
    destruct (classic (ptr = ptr0)).
    + subst. binds_determine. eexists. split. prove_bag. destruct obj. constructor; eauto.
      - introv Hnext Hidx. rew_refl in Hnext. tryfalse.
      - introv Hbinds Hattrs. destruct (classic (s = s0)).
        * subst. false. eapply Habinds. prove_bag.
        * unfolds set_object_property. prove_bag.
    + prove_bag.
Qed.

Lemma state_security_ok_set_object_oattr : forall st ptr obj oa v,
    binds st ptr obj ->
    object_oattr_modifiable obj oa ->
    object_oattr_valid oa v ->
    state_security_ok st (st \(ptr := set_object_oattr obj oa v)).
Proof.
    introv Hbinds Hmodifiable Hvalid Hbinds'.
    destruct (classic (ptr = ptr0)).
    + subst. binds_determine. eexists. split. prove_bag. destruct obj. constructor; eauto.
      - destruct object_attrs. destruct oa; inverts Hmodifiable; reflexivity.
      - destruct object_attrs. destruct oa; inverts Hmodifiable; reflexivity.
      - rew_refl. unfolds object_extensible. introv Hnext. destruct object_attrs. destruct oa; try reflexivity.
        inverts Hmodifiable. simpls. tryfalse.
      - rew_refl. unfolds object_extensible. introv Hnext. destruct object_attrs. destruct oa; try assumption.
        inverts Hmodifiable. simpls. tryfalse.
    + prove_bag.
Qed.

Lemma state_security_ok_new_object : forall st obj,
    state_security_ok st (st \(fresh st := obj)).
Proof.
    introv Hbinds.
    destruct (classic (ptr = fresh st)).
    + subst. eexists. split. prove_bag. false. eapply fresh_index. eapply index_binds_inv. eassumption.
    + lets Hnindex : (fresh_index st). eexists. split. prove_bag. eapply object_security_ok_refl.
Qed.

Lemma state_security_ok_delete_object_property : forall st ptr obj s attrs,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_configurable attrs ->
    state_security_ok st (st \(ptr := delete_object_property obj s)).
Proof.
    introv Hbinds Habinds Hconfig Hbinds'.
    destruct (classic (ptr = ptr0)).
    + subst. binds_determine. eexists. split. prove_bag. destruct obj. constructor; eauto.
      - introv Hnext Hidx. destruct (classic (s = s0)).
        * subst. prove_bag.
        * eapply index_remove_notin_inv; try apply Hidx. unfolds LibBag.notin. rew_in_eq. eauto. (* TODO *)
      - introv Hbinds Hattrs. destruct (classic (s = s0)).
        * subst. binds_determine. rew_refl in Hattrs. tryfalse.
        * eexists. splits. eapply binds_remove_notin. { unfolds LibBag.notin. rew_in_eq. eauto. }
          eassumption. assumption. eauto.
    + prove_bag.
Qed.

Local Ltac many_step IHk := 
    ljs_inv; ljs_out_redh_ter; apply_hyp IHk; ljs_inv; try assumption; state_security_ok_trans.

Lemma red_exprh_eval_many_state_security_ok : forall k K,
    (forall c st st' r l,
        red_exprh k c st (K l) (out_ter st' r) -> state_security_ok st st') ->
    (forall c st st' r e,
        red_exprh k c st e (out_ter st' r) -> state_security_ok st st') ->
    forall l1 l2 c st st' r,
    red_exprh k c st (expr_eval_many_1 l1 l2 K) (out_ter st' r) ->
    state_security_ok st st'.
Proof.
    introv Hcont IHk. induction l1; introv Hred.
    + ljs_inv. eauto.
    + many_step IHk.
      specializes~ IHl1 ___.
Qed.

Local Ltac eval_many_magic IHk := 
    match goal with
    | H : red_exprh _ _ _ (expr_eval_many_1 _ _ _) _ |- _ =>
        let H' := fresh in
        (lets H' : red_exprh_eval_many_state_security_ok IHk H; clear H); [introv H | idtac]
    end.

Local Ltac state_security_magic IHk := repeat (ljs_out_redh_ter || eval_many_magic IHk || 
                   ljs_inv || apply_hyp IHk || 
                   state_security_ok_trans || apply state_security_ok_refl).

Lemma state_security_ok_object : forall k,
    (forall c st st' r e,
        red_exprh k c st e (out_ter st' r) -> state_security_ok st st') ->
    forall l1 l2 obj c st st' r,
    red_exprh k c st (expr_object_2 l1 l2 obj) (out_ter st' r) ->
    state_security_ok st st'.
Proof.
    introv IHk. induction l1; [induction l2 | idtac]; introv Hred.
    + ljs_inv. applys* state_security_ok_new_object.
    + ljs_inv; do 4 (many_step IHk); do 2 ljs_inv; eauto.
    + ljs_inv. many_step IHk. do 2 ljs_inv. eauto.
Qed.

Lemma red_exprh_state_security_ok : forall k c st st' r e,
    red_exprh k c st e (out_ter st' r) ->
    state_security_ok st st'.
Proof.
    intro k.
    induction k;
    introv Hred. 
    inverts Hred.
    destruct e;
    inverts red_exprh Hred;
    try solve [apply state_security_ok_refl];
    try match goal with
    | H : context [ expr_object_1 _ _ ] |- _ => fail 1
    | _ => state_security_magic IHk
    end.
    + do 4 (many_step IHk). do 2 ljs_inv.
      applys* state_security_ok_object.
    + applys* state_security_ok_set_attributes.
    + applys* state_security_ok_new_attributes.
    + applys* state_security_ok_set_object_oattr.
    + applys* state_security_ok_delete_object_property.
    + skip.
    + applys* state_security_ok_new_object.
Qed.
