Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.

Definition object_binds st ptr obj :=
    Heap.binds (object_heap st) ptr obj.

Definition object_indom st ptr :=
    Heap.indom (object_heap st) ptr.

Definition value_binds st loc v :=
    Heap.binds (value_heap st) loc v.

Definition value_indom st loc :=
    Heap.indom (value_heap st) loc.

Definition id_binds c i loc :=
    Heap.binds (loc_heap c) i loc.

Definition id_indom c i :=
    Heap.indom (loc_heap c) i.
