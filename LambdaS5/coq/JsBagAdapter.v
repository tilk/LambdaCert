Require Import Utils.
Require Import LibBagExt.
Require Import JsSyntax.
Require Import JsPreliminary.

Section Instances.

Variables (A B : Type).

Global Instance binds_object_inst : BagBinds object_loc object state :=
    { binds := object_binds }.

Global Instance binds_env_record_inst : BagBinds env_loc env_record state :=
    { binds := env_record_binds }.

Global Instance binds_heap_inst : BagBinds A B (Heap.heap A B) :=
    { binds := @Heap.binds _ _ }.

Global Instance index_heap_inst : BagIndex (Heap.heap A B) A :=
    { index := @Heap.indom _ _ }.

Global Instance dom_heap_inst : BagDom (Heap.heap A B) (set A) :=
    { dom := @Heap.dom _ _ }.

Global Instance dom_index_eq_inst : Dom_index_eq.
Admitted. (* TODO *)

Global Instance index_binds_eq_inst : Index_binds_eq.
Admitted. (* TODO *)

End Instances.