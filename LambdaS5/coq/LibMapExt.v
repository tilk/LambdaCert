(* Should be integrated with LibMap *)
Set Implicit Arguments.
Generalizable Variables A B.
Require Import Utils.
Require Import LibTactics LibLogic LibReflect LibOption
  LibRelation LibLogic LibOperation LibEpsilon LibSet.
Require Export LibMap LibBagExt.


Definition read_option_impl A B (M:map A B) (k:A) := M k.

Instance read_option_inst : forall A B, BagReadOption A B (map A B) :=
    { read_option := @read_option_impl _ _ }.

Global Opaque read_option_inst.

Section Instances.

Transparent map binds_inst disjoint_inst read_option_inst empty_inst
    single_bind_inst union_inst remove_inst restrict_inst dom_inst.
 
Global Instance binds_double_inst : Binds_double (T := map A B).
Proof. 
    constructor. introv Hb. apply func_ext_1. intro x.
    unfold binds, binds_inst, binds_impl in Hb.
    sets_eq xo : (F x).
    destruct xo.
    specializes Hb x b.
    sets_eq xo' : (E x).
    destruct xo'.
    specializes Hb x b. symmetry in EQxo'.
    destruct Hb as (Hb1&Hb2).
    specializes Hb1 EQxo'. rewrite Hb1 in EQxo. tryfalse.
    reflexivity.
Qed.

(*
Global Instance incl_binds_eq_inst : Incl_binds_eq (T := map A B).
*)

Global Instance disjoint_binds_eq_inst : Disjoint_binds_eq (T := map A B).
Proof. 
    constructor. intros. simpl. 
Admitted. (* TODO *)

Global Instance read_option_binds_eq_inst : Read_option_binds_eq (T := map A B).
Proof. constructor. intros. reflexivity. Qed.

Global Instance binds_empty_eq_inst : Binds_empty_eq (T := map A B).
Proof. constructor. intros. cbv. rew_logic. split; intro; tryfalse. Qed.

Global Instance binds_single_bind_eq_inst : Binds_single_bind_eq (T := map A B).
Proof. 
    constructor. intros. cbv. rew_logic. 
    split; intro Hk; cases_if. injects Hk. auto.
    destruct Hk. substs. reflexivity.
    destruct Hk. substs. tryfalse.
Qed.

Global Instance binds_union_eq_inst : Binds_union_eq (T := map A B).
Proof.
    constructor. intros. simpl.
Admitted. (* TODO *)

(*
Global Instance binds_remove_eq_inst : Binds_remove_eq (T := map A B).
*)

(*
Global Instance binds_restrict_eq_inst : Binds_restrict_eq :=
    { binds_restrict_eq := @binds_restrict_eq_impl _ _ }.
*)

(*
Global Instance binds_update_eq_inst : Binds_update_eq :=
    { binds_update_eq := @binds_update_eq_impl _ _ }.
*)

Global Instance index_binds_eq_inst : Index_binds_eq (T := map A B).
Proof.
   constructor. intros. simpl. unfold dom_impl. rew_set. reflexivity. 
Qed.

End Instances.
