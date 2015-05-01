Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesIndexed.
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
    try apply state_security_ok_refl.
    skip.
    repeat ljs_inv. 
(* TODO *)
Admitted.
