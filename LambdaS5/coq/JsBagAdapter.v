Require Import Utils.
Require Import JsSyntax.
Require Import JsPreliminary.
Import LibStream.
Require Import LibBagExt.
Import LibBag.

Implicit Type jst : state.
Implicit Type jc : execution_ctx.
Implicit Type jv : value.
Implicit Type jptr : object_loc.
Implicit Type jobj : object.
Implicit Type jer : env_record.
Implicit Type jeptr : env_loc.

Module Import JsCertExt.

Definition state_fresh_object_loc jst := object_loc_normal (LibStream.stream_head (state_fresh_locations jst)).

Definition state_fresh_env_record_loc jst : env_loc := LibStream.stream_head (state_fresh_locations jst).

Definition state_next_fresh jst :=
    match jst with
    | state_intro oh eh (LibStream.stream_intro _ fl) el => state_intro oh eh fl el
    end.

Definition env_record_indom S L :=
    Heap.indom (state_env_record_heap S) L.

Definition state_fresh_ok jst := LibStream.always 
    (fun fl => ~object_indom jst (object_loc_normal (LibStream.stream_head fl)) /\ 
        ~env_record_indom jst (LibStream.stream_head fl)) 
    (state_fresh_locations jst).

End JsCertExt.

Section Instances.

Variables (A B : Type).

Global Instance binds_heap_inst : BagBinds A B (Heap.heap A B) :=
    { binds := @Heap.binds _ _ }.

Global Instance index_heap_inst : BagIndex (Heap.heap A B) A :=
    { index := @Heap.indom _ _ }.

Global Instance dom_heap_inst : BagDom (Heap.heap A B) (set A) :=
    { dom := @Heap.dom _ _ }.

Global Instance update_heap_inst : BagUpdate A B (Heap.heap A B) :=
    { update := @Heap.write _ _ }.

Global Instance dom_index_eq_inst : Dom_index_eq.
Admitted. (* TODO *)

Global Instance index_binds_eq_inst : Index_binds_eq.
Admitted. (* TODO *)

Global Instance binds_update_eq_inst : Binds_update_eq.
Admitted. (* TODO *)

End Instances.

Section StateInstances.

Global Instance binds_object_state_inst : BagBinds object_loc object state :=
    { binds := object_binds }.

Global Instance binds_env_record_state_inst : BagBinds env_loc env_record state :=
    { binds := env_record_binds }.

Global Instance index_object_state_inst : BagIndex state object_loc :=
    { index := object_indom }.

Global Instance index_env_record_state_inst : BagIndex state env_loc :=
    { index := env_record_indom }.

Global Instance update_object_state_inst : BagUpdate object_loc object state :=
    { update := object_write }.

Global Instance update_env_record_state_inst : BagUpdate env_loc env_record state :=
    { update := env_record_write }.

Global Instance fresh_object_state_inst : BagFresh object_loc state :=
    { fresh := state_fresh_object_loc }.

Global Instance fresh_env_record_state_inst : BagFresh env_loc state :=
    { fresh := state_fresh_env_record_loc }.

Global Instance index_binds_eq_object_state_inst : Index_binds_eq (T := state) (A := object_loc).
Proof. 
    constructor. introv. 
    applys (index_binds_eq (T := Heap.heap object_loc object)).
Qed.

Global Instance index_binds_eq_env_record_state_inst : Index_binds_eq (T := state) (A := env_loc).
Proof. 
    constructor. introv. 
    applys (index_binds_eq (T := Heap.heap env_loc env_record)).
Qed.

Global Instance binds_update_eq_object_state_inst : Binds_update_eq (T := state) (A := object_loc).
Proof.
    constructor. introv.
    destruct M.
    applys (binds_update_eq (T := Heap.heap object_loc object)).
Qed.

Global Instance binds_update_eq_env_record_state_inst : Binds_update_eq (T := state) (A := env_loc).
Proof.
    constructor. introv.
    destruct M.
    applys (binds_update_eq (T := Heap.heap env_loc env_record)).
Qed.

End StateInstances.

Lemma js_state_fresh_ok_next_fresh_preserved : forall jst, 
    state_fresh_ok jst -> state_fresh_ok (state_next_fresh jst).
Proof.
    introv Hfok.
    unfolds state_fresh_ok.
    destruct jst.
    simpls.
    inverts Hfok.
    eauto.
Qed.

Lemma js_state_fresh_ok_next_fresh_update_object_preserved : forall jst jobj,
    state_fresh_ok jst -> state_fresh_ok (state_next_fresh (jst \(fresh jst := jobj))).
Proof. 
Admitted. (* TODO *)

Lemma js_state_fresh_ok_next_fresh_update_env_record_preserved : forall jst jer,
    state_fresh_ok jst -> state_fresh_ok (state_next_fresh (jst \(fresh jst := jer))).
Proof. 
Admitted. (* TODO *)

Lemma js_object_alloc_lemma : forall jst jobj,
    (fresh jst, state_next_fresh (jst \(fresh jst := jobj))) =
    JsPreliminary.object_alloc jst jobj.
Proof.
    introv.
    destruct jst. destruct state_fresh_locations.
    reflexivity.
Qed.

Lemma js_object_fresh_index : forall jst,
    state_fresh_ok jst ->
    ~LibBag.index jst (@fresh object_loc _ _ jst).
Proof.
    introv Hfok.
    destruct jst. destruct state_fresh_locations.
    inverts Hfok as Hfok (Hfok1&Hfok2). eauto.
Qed.

Lemma js_env_record_fresh_index : forall jst,
    state_fresh_ok jst ->
    ~index jst (@fresh env_loc _ _ jst).
Proof.
    introv Hfok.
    destruct jst. destruct state_fresh_locations.
    inverts Hfok as Hfok (Hfok1&Hfok2). eauto.
Qed.

Lemma js_state_next_fresh_index_object_preserved_eq : forall jst jptr,
    index (state_next_fresh jst) jptr = index jst jptr.
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed.

Lemma js_state_next_fresh_index_env_record_preserved_eq : forall jst jeptr,
    index (state_next_fresh jst) jeptr = index jst jeptr.
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed.

Lemma js_state_next_fresh_binds_object_preserved_eq : forall jst jptr jobj,
    binds (state_next_fresh jst) jptr jobj = binds jst jptr jobj.
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed.

Lemma js_state_next_fresh_binds_env_record_preserved_eq : forall jst jeptr jer,
    binds (state_next_fresh jst) jeptr jer = binds jst jeptr jer.
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed.

Lemma js_state_next_fresh_index_object_preserved : forall jst jptr,
    index jst jptr ->
    index (state_next_fresh jst) jptr.
Proof. introv. rewrite js_state_next_fresh_index_object_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_index_env_record_preserved : forall jst jeptr,
    index jst jeptr ->
    index (state_next_fresh jst) jeptr.
Proof. introv. rewrite js_state_next_fresh_index_env_record_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_binds_object_preserved : forall jst jptr jobj,
    binds jst jptr jobj ->
    binds (state_next_fresh jst) jptr jobj.
Proof. introv. rewrite js_state_next_fresh_binds_object_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_binds_env_record_preserved : forall jst jeptr jer,
    binds jst jeptr jer ->
    binds (state_next_fresh jst) jeptr jer.
Proof. introv. rewrite js_state_next_fresh_binds_env_record_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_index_object_preserved_inv : forall jst jptr,
    index (state_next_fresh jst) jptr ->
    index jst jptr.
Proof. introv. rewrite js_state_next_fresh_index_object_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_index_env_record_preserved_inv : forall jst jeptr,
    index (state_next_fresh jst) jeptr ->
    index jst jeptr.
Proof. introv. rewrite js_state_next_fresh_index_env_record_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_binds_object_preserved_inv : forall jst jptr jobj,
    binds (state_next_fresh jst) jptr jobj ->
    binds jst jptr jobj.
Proof. introv. rewrite js_state_next_fresh_binds_object_preserved_eq. auto. Qed.

Lemma js_state_next_fresh_binds_env_record_preserved_inv : forall jst jeptr jer,
    binds (state_next_fresh jst) jeptr jer ->
    binds jst jeptr jer.
Proof. introv. rewrite js_state_next_fresh_binds_env_record_preserved_eq. auto. Qed.

Lemma js_state_write_object_binds_env_record_preserved_eq : forall jst jptr jobj jeptr jer,
    binds (jst \(jptr := jobj)) jeptr jer = binds jst jeptr jer.
Proof. destruct jst. reflexivity. Qed.

Lemma js_state_write_object_index_env_record_preserved_eq : forall jst jptr jobj jeptr,
    index (jst \(jptr := jobj)) jeptr = index jst jeptr.
Proof. destruct jst. reflexivity. Qed.

Lemma js_state_write_env_record_binds_object_preserved_eq : forall jst jptr jobj jeptr jer,
    binds (jst \(jeptr := jer)) jptr jobj = binds jst jptr jobj.
Proof. destruct jst. reflexivity. Qed.

Lemma js_state_write_env_record_index_object_preserved_eq : forall jst jptr jobj jeptr jer,
    index (jst \(jeptr := jer)) jptr = index jst jptr.
Proof. destruct jst. reflexivity. Qed.

Hint Rewrite 
    js_state_write_object_binds_env_record_preserved_eq
    js_state_write_env_record_binds_object_preserved_eq : rew_binds_eq.

Hint Rewrite 
    js_state_write_object_index_env_record_preserved_eq
    js_state_write_env_record_index_object_preserved_eq : rew_index_eq.
