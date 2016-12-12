Require Import Utils.
Require Import JsSyntax.
Require Import JsPreliminary.
Require Import JsCommon.
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
Implicit Type jattrs : attributes.

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

Context `{Comparable A} `{Inhab B}.

Global Instance binds_heap_inst : BagBinds A B (Heap.heap A B) :=
    { binds := @Heap.binds _ _ }.

Global Instance index_heap_inst : BagIndex (Heap.heap A B) A :=
    { index := @Heap.indom _ _ }.

Global Instance dom_heap_inst : BagDom (Heap.heap A B) (set A) :=
    { dom := @Heap.dom _ _ }.

Global Instance empty_heap_inst : BagEmpty (Heap.heap A B) :=
    { empty := @Heap.empty _ _ }.

Global Instance update_heap_inst : BagUpdate A B (Heap.heap A B) :=
    { update := @Heap.write _ _ }.

Global Instance read_heap_inst : (*Comparable A -> Inhab B ->*) BagRead A B (Heap.heap A B) :=
    { read := @Heap.read _ _ _ _ }.

Global Instance read_option_heap_inst : (* Comparable A ->*) BagReadOption A B (Heap.heap A B) :=
    { read_option := @Heap.read_option _ _ _ }.

Global Instance dom_index_eq_inst : Dom_index_eq.
Admitted. (* TODO *)

Global Instance index_binds_eq_inst : Index_binds_eq.
Admitted. (* TODO *)

Global Instance binds_empty_eq_inst : Binds_empty_eq.
Admitted. (* TODO *)

Global Instance binds_update_eq_inst : Binds_update_eq.
Admitted. (* TODO *)

Global Instance read_binds_eq_inst : Read_binds_eq.
Admitted. (* TODO *)

Global Instance read_option_binds_eq_inst : Read_option_binds_eq.
Admitted. (* TODO *)

Global Instance binds_double_inst : Binds_double.
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

Global Instance update_overwrite_object_state_inst : Update_overwrite (T := state) (A := object_loc).
Proof.
    constructor. introv. destruct M.
    lets H : (update_overwrite state_object_heap k x x').
    simpls. rewrite H. reflexivity.
Qed.

Global Instance update_overwrite_env_record_state_inst : Update_overwrite (T := state) (A := env_loc).
Proof.
    constructor. introv. destruct M.
    lets H : (update_overwrite state_env_record_heap k x x').
    simpls. rewrite H. reflexivity.
Qed.

End StateInstances.

Section Rewriting.

Variables (A B : Type).

Context `{Comparable A} `{Inhab B}.

Implicit Type a : A.
Implicit Type b : B.
Implicit Type m : Heap.heap A B.

Lemma heap_binds_to_libbag_eq : forall a b m, Heap.binds m a b = binds m a b.
Proof. reflexivity. Qed.

Lemma heap_indom_to_libbag_eq : forall a m, Heap.indom m a = index m a.
Proof. reflexivity. Qed.

Lemma heap_dom_to_libbag : forall m, Heap.dom m = dom m.
Proof. reflexivity. Qed.

Lemma heap_empty_to_libbag : Heap.empty (K := A) (V := B) = empty.
Proof. reflexivity. Qed.

Lemma heap_write_to_libbag : forall m a b, Heap.write m a b = m\(a:=b).
Proof. reflexivity. Qed.

Lemma heap_read_to_libbag : forall m a, Heap.read m a = m\(a).
Proof. reflexivity. Qed.

Lemma heap_read_option_to_libbag : forall m a, Heap.read_option m a = m\(a?).
Proof. reflexivity. Qed.

End Rewriting.

Lemma object_binds_to_libbag : forall jst jptr jobj, object_binds jst jptr jobj = binds jst jptr jobj.
Proof. reflexivity. Qed.
Lemma object_write_to_libbag : forall jst jptr jobj, object_write jst jptr jobj = jst\(jptr := jobj).
Proof. reflexivity. Qed.

Lemma env_record_binds_to_libbag : forall jst jeptr jer, env_record_binds jst jeptr jer = binds jst jeptr jer.
Proof. reflexivity. Qed.
Lemma env_record_write_to_libbag : forall jst jeptr jer, env_record_write jst jeptr jer = jst\(jeptr := jer).
Proof. reflexivity. Qed.

Lemma decl_env_record_binds_to_libbag : forall jder s jmut jv, 
    decl_env_record_binds jder s jmut jv = binds jder s (jmut, jv).
Proof. reflexivity. Qed.
Lemma decl_env_record_indom_to_libbag : forall jder s, 
    decl_env_record_indom jder s = index jder s.
Proof. reflexivity. Qed.
Lemma decl_env_record_write_to_libbag : forall jder s jmut jv, 
    decl_env_record_write jder s jmut jv = jder\(s := (jmut, jv)).
Proof. reflexivity. Qed.
Lemma decl_env_record_empty_to_libbag : decl_env_record_empty = \{}.
Proof. reflexivity. Qed.

Hint Rewrite 
    object_binds_to_libbag object_write_to_libbag
    env_record_binds_to_libbag env_record_write_to_libbag
    decl_env_record_binds_to_libbag decl_env_record_write_to_libbag
    decl_env_record_indom_to_libbag decl_env_record_empty_to_libbag 
    using (eauto with typeclass_instances) : rew_heap_to_libbag.

Hint Rewrite
    @heap_binds_to_libbag_eq @heap_indom_to_libbag_eq @heap_dom_to_libbag @heap_empty_to_libbag
    @heap_write_to_libbag @heap_read_to_libbag @heap_read_option_to_libbag
    using (eauto with typeclass_instances) : rew_heap_to_libbag.

Tactic Notation "rew_heap_to_libbag" :=
    autorewrite with rew_heap_to_libbag.
Tactic Notation "rew_heap_to_libbag" "in" hyp(H) :=
    autorewrite with rew_heap_to_libbag in H.
Tactic Notation "rew_heap_to_libbag" "in" "*" :=
    autorewrite with rew_heap_to_libbag in *.

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

Lemma js_state_fresh_ok_update_object_preserved : forall jst jptr jobj,
    index jst jptr -> state_fresh_ok jst -> state_fresh_ok (jst \(jptr := jobj)).
Proof.
Admitted. (* TODO *)

Lemma js_state_fresh_ok_update_env_record_preserved : forall jst jeptr jer,
    index jst jeptr -> state_fresh_ok jst -> state_fresh_ok (jst \(jeptr := jer)).
Proof.
Admitted. (* TODO *)

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
    JsCommon.object_alloc jst jobj.
Proof.
    introv.
    destruct jst. destruct state_fresh_locations.
    reflexivity.
Qed.

Lemma js_lexical_env_alloc_object_lemma : forall jst jlenv jptr b,
    (fresh jst :: jlenv, state_next_fresh (jst \(fresh jst := env_record_object jptr b))) = 
    JsCommon.lexical_env_alloc_object jst jlenv jptr b.
Proof.
    introv.
    destruct jst. destruct state_fresh_locations.
    reflexivity.
Qed.

Lemma js_lexical_env_alloc_decl_lemma : forall jst jlenv,
    (fresh jst :: jlenv, state_next_fresh (jst \(fresh jst := env_record_decl decl_env_record_empty))) = 
    JsCommon.lexical_env_alloc_decl jst jlenv.
Proof.
    introv.
    destruct jst. destruct state_fresh_locations.
    reflexivity.
Qed.

Lemma js_object_set_property_lemma : forall jst jptr jobj s jattrs,
    binds jst jptr jobj ->
    JsCommon.object_set_property jst jptr s jattrs 
        (jst \(jptr := object_map_properties jobj (fun jprops => jprops \(s := jattrs)))).
Proof.
    introv Hbinds. unfolds. unfolds. jauto.
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

Lemma js_state_write_env_record_index_object_preserved_eq : forall jst jptr jeptr jer,
    index (jst \(jeptr := jer)) jptr = index jst jptr.
Proof. destruct jst. reflexivity. Qed.

Lemma js_state_write_object_next_fresh_commute : forall jst jptr jobj,
    state_next_fresh jst \(jptr := jobj) = state_next_fresh (jst \(jptr := jobj)).
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed. 

Lemma js_state_write_env_record_next_fresh_commute : forall jst jeptr jer,
    state_next_fresh jst \(jeptr := jer) = state_next_fresh (jst \(jeptr := jer)).
Proof. destruct jst. destruct state_fresh_locations. reflexivity. Qed. 

Hint Rewrite 
    js_state_write_object_binds_env_record_preserved_eq
    js_state_write_env_record_binds_object_preserved_eq : rew_binds_eq.

Hint Rewrite 
    js_state_write_object_index_env_record_preserved_eq
    js_state_write_env_record_index_object_preserved_eq : rew_index_eq.
