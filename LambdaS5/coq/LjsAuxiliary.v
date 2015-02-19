Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.

Definition object_binds st ptr obj :=
    Heap.binds (object_heap st) ptr obj.

Definition object_indom st ptr :=
    Heap.indom (object_heap st) ptr.

Definition id_binds c i loc :=
    Heap.binds (value_heap c) i loc.

Definition id_indom c i :=
    Heap.indom (value_heap c) i.
