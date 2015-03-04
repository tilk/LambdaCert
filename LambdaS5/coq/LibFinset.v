(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite sets                                                             *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibList.
Require Import LibSet LibLogic LibEqual LibReflect LibOrder.
Generalizable Variable A.

(** DISCLAIMER: for the time being, this file only contains the
    operations for type fset, but not yet all the typeclasses 
    associated with it. A module signature is currently used to
    hide the implentation. *)

(* ********************************************************************** *)
(** * Abstract interface for finite sets *)
(*
Module Type FsetSig.

(** Definitions and operations on finite sets *)

Section Operations.
Variables (A:Type).

Parameter fset : Type -> Type.

Parameter to_list : fset A -> list A.
Parameter from_list : list A -> fset A.

End Operations.

(** Notations *)

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

Parameter union_inst : Comparable A -> BagUnion (fset A).
Parameter inter_inst : Comparable A -> BagInter (fset A).
Parameter remove_inst : Comparable A -> BagRemove (fset A) (fset A).
Parameter empty_inst : Comparable A -> BagEmpty (fset A).
Parameter in_inst : Comparable A -> BagIn A (fset A).
Parameter single_inst : Comparable A -> BagSingle A (fset A).
Parameter incl_inst : Comparable A -> BagIncl (fset A).
Parameter disjoint_inst : Comparable A -> BagDisjoint (fset A).

Existing Instances union_inst inter_inst remove_inst empty_inst in_inst
    single_inst incl_inst disjoint_inst.

(** Extensionality *)

Parameter fset_extens : forall (cmp : Comparable A) (E : fset A) (F : fset A), 
  E \c F -> F \c E -> E = F.

(** Semantics of basic operations *)

Parameter in_empty_eq_inst : forall (cmp : Comparable A), In_empty_eq.
Parameter in_single_eq_inst : forall (cmp : Comparable A), In_single_eq.
Parameter in_union_eq_inst : forall (cmp : Comparable A), In_union_eq.
Parameter in_inter_eq_inst : forall (cmp : Comparable A), In_inter_eq.
Parameter in_remove_eq_inst : forall (cmp : Comparable A), In_remove_eq.

Existing Instances in_empty_eq_inst in_single_eq_inst in_union_eq_inst
    in_inter_eq_inst in_remove_eq_inst.

Parameter mem_decidable : forall (cmp : Comparable A) (s:fset A) x,
   Decidable (x \in s).
Existing Instances mem_decidable.

End Properties.

End FsetSig.

Print Module Type FsetSig.

(* ********************************************************************** *)
(** * Implementation of finite sets *)

Module Export FsetImpl : FsetSig.
*)
(** Note: most of the material contained in this module will ultimately
    be moved into the TLC library in a file called LibFset. *)

Definition finset A := list A.

Section Operations.
Variables (A:Type).
 
Definition from_list (L : list A) : finset A := L.

Definition to_list (E : finset A) : list A := E.

End Operations.

(** Notations *)

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : finset A.

Global Instance union_inst : Comparable A -> BagUnion (finset A) :=
  { union := fun E F => E ++ List.filter (fun x => !LibList.mem_decide x E) F }. 

Global Instance inter_inst : Comparable A -> BagInter (finset A) :=
  { inter := fun E F => List.filter (fun x => LibList.mem_decide x F) E }.

Global Instance remove_inst : Comparable A -> BagRemove (finset A) (finset A) :=
  { remove := fun E F => List.filter (fun x => !LibList.mem_decide x F) E }.

Global Instance empty_inst : Comparable A -> BagEmpty (finset A) := 
  { empty := nil }.

Global Instance in_inst : Comparable A -> BagIn A (finset A) :=
  { is_in := fun x E => LibList.Mem x E }.

Global Instance single_inst : Comparable A -> BagSingle A (finset A) := 
  { single := fun x => x :: nil }.

Global Instance incl_inst : Comparable A -> BagIncl (finset A) :=
  { incl := fun E F => forall x, x \in E -> x \in F }.

Global Instance disjoint_inst : Comparable A -> BagDisjoint (finset A) :=
  { disjoint := fun E F => inter E F = empty }.

Lemma finset_extens_eq : forall (cmp : Comparable A) (E : finset A) F,
  (forall x, x \in E = x \in F) -> E = F.
Proof.
(* TODO *)
Admitted.

Lemma finset_extens : forall (cmp : Comparable A) (E : finset A)  F, 
  E \c F -> F \c E -> E = F.
Proof. intros. applys finset_extens_eq. extens*. Qed.

Global Instance in_empty_eq_inst : forall (cmp : Comparable A), In_empty_eq (A:=A) (T:=finset A).
Proof. constructor. simpl. intros. apply Mem_nil_eq. Qed.

Global Instance in_single_eq_inst : forall (cmp : Comparable A), In_single_eq (A:=A) (T:=finset A).
Proof. constructor. simpl. intros. rewrite Mem_cons_eq. rewrite Mem_nil_eq. rew_logic*. Qed.

Global Instance in_union_eq_inst : forall (cmp : Comparable A), In_union_eq (A:=A) (T:=finset A).
Proof. Admitted.

Global Instance in_inter_eq_inst : forall (cmp : Comparable A), In_inter_eq (A:=A) (T:=finset A).
Proof. Admitted.

Global Instance in_remove_eq_inst : forall (cmp : Comparable A), In_remove_eq (A:=A) (T:=finset A).
Proof. Admitted.

Lemma mem_decidable : forall (cmp : Comparable A) (s:finset A) x,
   Decidable (x \in s).
Proof.
  intros. applys decidable_make (LibList.mem_decide x s).
  skip.
Defined.

End Properties.
(*
End FsetImpl.
*)


(* ********************************************************************** *)
(** * Derivable properties about finite sets *)

(*

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

(** Properties of [in] *)

Lemma in_empty_elim : forall x,
  x \in \{} -> False.
Proof. introv H. rewrite~ in_empty in H. Qed.

Lemma in_singleton_self : forall x,
  x \in \{x}.
Proof. intros. rewrite~ in_singleton. Qed.

(** Properties of [union] *)

Lemma union_same : forall E,
  E \u E = E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_comm : forall E F,
  E \u F = F \u E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_assoc : forall E F G,
  E \u (F \u G) = (E \u F) \u G.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_empty_l : forall E,
  \{} \u E = E.
Proof.
  intros. apply fset_extens; 
   intros x; rewrite_all in_union.
    intros [ H | H ]. false. rewrite~ in_empty in H. auto.
    auto*.
Qed.

Lemma union_empty_r : forall E,
  E \u \{} = E.
Proof. intros. rewrite union_comm. apply union_empty_l. Qed.

Lemma union_comm_assoc : forall E F G,
  E \u (F \u G) = F \u (E \u G).
Proof.
  intros. rewrite union_assoc.
  rewrite (union_comm E F).
  rewrite~ <- union_assoc.
Qed.

(** Properties of [inter] *)

Lemma inter_same : forall E,
  E \n E = E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_comm : forall E F,
  E \n F = F \n E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_assoc : forall E F G,
  E \n (F \n G) = (E \n F) \n G.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_empty_l : forall E,
  \{} \n E = \{}.
Proof.
  intros. apply fset_extens; 
   intros x; rewrite_all in_inter.
    intros. false* in_empty_elim.
    intros. false* in_empty_elim. 
Qed.

Lemma inter_empty_r : forall E,
  E \n \{} = \{}.
Proof. intros. rewrite inter_comm. apply inter_empty_l. Qed.

Lemma inter_comm_assoc : forall E F G,
  E \n (F \n G) = F \n (E \n G).
Proof.
  intros. rewrite inter_assoc.
  rewrite (inter_comm E F).
  rewrite~ <- inter_assoc.
Qed.

(* Properties of [from_list] *)

Lemma from_list_nil : 
  from_list (@nil A) = \{}.
Proof. auto. Qed.

Lemma from_list_cons : forall x l,
  from_list (x::l) = \{x} \u (from_list l).
Proof. auto. Qed.

(* Properties of [disjoint] *)

Lemma disjoint_comm : forall E F,
  disjoint E F -> disjoint F E.
Proof. unfold disjoint. intros. rewrite~ inter_comm. Qed.

Lemma disjoint_in_notin : forall E F x,
  disjoint E F -> x \in E -> x \notin F.
Proof.
  unfold disjoint. introv H InE InF. applys in_empty_elim x.
  rewrite <- H. rewrite in_inter. auto.
Qed.

(** Properties of [notin] *)

Lemma notin_empty : forall x,
  x \notin \{}.
Proof. intros_all. rewrite~ in_empty in H. Qed.

Lemma notin_singleton : forall x y,
  x \notin \{y} <-> x <> y.
Proof. unfold notin. intros. rewrite* <- in_singleton. Qed.

Lemma notin_same : forall x,
  x \notin \{x} -> False.
Proof. intros. apply H. apply* in_singleton_self. Qed.

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof. unfold notin. intros. rewrite* in_union. Qed.

(** Properties of [subset] *)

Lemma subset_refl : forall E,
  E \c E.
Proof. intros_all. auto. Qed.

Lemma subset_empty_l : forall E,
  \{} \c E.
Proof. intros_all. rewrite* in_empty in H. Qed.

Lemma subset_union_weak_l : forall E F,
  E \c (E \u F).
Proof. intros_all. rewrite* in_union. Qed.

Lemma subset_union_weak_r : forall E F,
  F \c (E \u F).
Proof. intros_all. rewrite* in_union. Qed.

Lemma subset_union_2 : forall E1 E2 F1 F2,
  E1 \c F1 -> E2 \c F2 -> (E1 \u E2) \c (F1 \u F2).
Proof. introv H1 H2. intros x. do 2 rewrite* in_union. Qed.

(** Properties of [remove] *)

Lemma union_remove : forall E F G,
  (E \u F) \- G = (E \- G) \u (F \- G).
Proof.
  intros. apply fset_extens; intros x;
  repeat (first [ rewrite in_remove | rewrite in_union ]); auto*.
Qed.

End Properties.

*)