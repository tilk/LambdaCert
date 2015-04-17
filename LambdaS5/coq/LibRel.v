(* Heterogenous binary relations *)

Set Implicit Arguments.
Require Import Utils.
Require Import LibTactics LibLogic LibBool LibLogic LibProd LibSum LibSet LibBagExt.
Require Export LibOperation.
Generalizable Variables A B R.

Definition rel A B := A -> B -> Prop.

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance rel_inhab : forall A B, Inhab (rel A B).
Proof. intros. apply (prove_Inhab (fun _ _ => True)). Qed.

(* ---------------------------------------------------------------------- *)
(** ** Extensionality *)

Lemma rel_extensional : forall A B (R1 R2:rel A B),
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof. intros_all. apply~ prop_ext_2. Qed.

Instance rel_extensional_inst : forall A B, Extensional (rel A B).
Proof. intros. apply (Build_Extensional _ (@rel_extensional A B)). Defined.

(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Definition sequence {A B C} (R1 : rel A B) (R2 : rel B C) : rel A C := fun x y =>
    exists z, R1 x z /\ R2 z y.

Section Constructions2.
Variables (A B : Type).
Implicit Types R : rel A B.
Implicit Types a : A.
Implicit Types b : B.

Definition empty : rel A B := 
  fun a b => False.

Definition single : A -> B -> rel A B :=
  fun a b a' b' => a = a' /\ b = b'.

Definition flip R : rel B A :=
  fun b a => R a b.

Definition compl R : rel A B :=
  fun a b => ~R a b.

Definition union R1 R2 : rel A B :=
  fun a b => R1 a b \/ R2 a b. 

Definition inter R1 R2 : rel A B :=
  fun a b => R1 a b /\ R2 a b. 

Definition incl R1 R2 :=
  forall a b, R1 a b -> R2 a b.

Definition defined R := 
  forall a, exists b, R a b.

Definition functional R :=
  forall a b b', R a b -> R a b' -> b = b'.

Definition has_dom R (S1 : set A) (S2 : set B) :=
  forall a b, R a b -> a \in S1 /\ b \in S2.

End Constructions2.

(* ---------------------------------------------------------------------- *)
(** ** More on binary relations (to TLC? ) *)  

Section Binary.
Variables (A : Type).
Implicit Types R : rel A A.
Implicit Types x y z : A.

Definition id : rel A A := fun x y => x = y.

Fixpoint pow k (R : rel A A) : rel A A :=
  match k with
  | 0 => id
  | S k' => sequence R (pow k' R)
  end.

End Binary.

(* ---------------------------------------------------------------------- *)
(** ** Adapter to LibBag *)

Global Instance union_inst : BagUnion (rel A B) :=
  { union := @union _ _ }.

Global Instance inter_inst : BagInter (rel A B) :=
  { inter := @inter _ _ }.

Global Instance empty_inst : BagEmpty (rel A B) :=
  { empty := @empty _ _ }.

Global Instance single_inst : BagSingle (A * B) (rel A B) :=
  { single := uncurry2 (@single _ _) }.

Global Instance in_inst : BagIn (A * B) (rel A B) :=
  { is_in := fun p r => uncurry2 r p }.

Global Instance incl_inst : BagIncl (rel A B) :=
  { incl := @incl _ _ }.

Global Instance in_empty_eq_inst : In_empty_eq (T := rel A B).
Proof. constructor. introv. cbv. cases_let. auto. Qed.

Global Instance in_single_eq_inst : In_single_eq (T := rel A B).
Proof. 
    constructor. introv. cbv. repeat cases_let.
    rew_logic. splits; introv Heq.
    destruct_hyp Heq. reflexivity.
    injects Heq. auto.
Qed.

Global Instance in_union_eq_inst : In_union_eq (T := rel A B).
Proof. constructor. introv. cbv. cases_let. auto. Qed.

Global Instance in_inter_eq_inst : In_inter_eq (T := rel A B).
Proof. constructor. introv. cbv. cases_let. auto. Qed.

Global Instance in_double_inst : In_double (T := rel A B).
Proof. 
    constructor. introv Hr.
    apply rel_extensional.
    intros a b. applys Hr (a, b).
Qed.

Global Instance incl_in_eq_inst : Incl_in_eq (T := rel A B).
Proof. 
    constructor. introv. cbv. rew_logic. split; introv Hi.
    introv. cases_let. auto.
    intros a b. applys Hi (a, b).
Qed.    

Section Lemmas.
Variables (A B : Type).

Lemma in_implies_rel : forall (R : rel A B) a b, (a, b) \in R -> R a b.
Proof. auto. Qed.

Lemma in_flip_eq : forall (R : rel A B) a b, (b, a) \in flip R = (a, b) \in R.
Proof. introv. reflexivity. Qed.

Lemma in_flip : forall (R : rel A B) a b, (a, b) \in R -> (b, a) \in flip R.
Proof. introv. rewrite in_flip_eq. auto. Qed.

Lemma in_flip_inv : forall (R : rel A B) a b, (b, a) \in flip R -> (a, b) \in R.
Proof. introv. rewrite in_flip_eq. auto. Qed.

End Lemmas.

Hint Resolve in_flip : bag.
Hint Rewrite in_flip_eq : rew_in_eq.

Global Opaque union_inst inter_inst empty_inst in_inst single_inst incl_inst.
