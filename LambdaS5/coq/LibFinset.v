(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite sets                                                             *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibList.
Require Import LibRelation LibSet LibLogic LibEqual LibReflect LibOrder.
Require Import LibBagExt.
Generalizable Variables A B T U.

(* TODO MOVE!!!! to LibList later *)
Section PropProperties.

Hint Constructors Forall Mem Filters.

Lemma Filters_exists : forall A (P : A -> Prop) L, exists L', Filters P L L'.
Proof.
    introv. induction L. 
    eexists; eauto.
    destruct IHL.
    destruct (classic (P a));
    eexists; eauto.
Qed.

Lemma Filters_Forall : forall A (P : A -> Prop) L L', Filters P L L' -> Forall P L'.
Proof.
    introv Hfilt.
    induction Hfilt; auto.
Qed.

Lemma Filters_Mem : forall A (P : A -> Prop) L L', Filters P L L' -> forall x, P x -> Mem x L -> Mem x L'.
Proof.
    introv Hfilt.
    induction Hfilt; introv Hp Hmem; inverts Hmem; eauto; tryfalse.
Qed.

Lemma Filters_Mem_inv : forall A (P : A -> Prop) L L', Filters P L L' -> forall x, Mem x L' -> Mem x L.
Proof.
    introv Hfilt.
    induction Hfilt; introv Hmem; inverts Hmem; eauto.
Qed.

Lemma Forall_Mem : forall A (P : A -> Prop) L, Forall P L -> forall x, Mem x L -> P x.
Proof.
    introv Hforall Hmem.
    induction Hforall; inverts Hmem; auto.
Qed.

End PropProperties.


(** DISCLAIMER: for the time being, this file only contains the
    operations for type fset, but not yet all the typeclasses 
    associated with it. A module signature is currently used to
    hide the implentation. *)

(* ********************************************************************** *)
(** * Abstract interface for finite sets *)

Module Type FinsetSig.

(** Definitions and operations on finite sets *)

Section Definitions.
Variables (A:Type).

Parameter finset : Type -> Type.

Parameter to_list_impl : finset A -> list A.
Parameter from_list_impl : list A -> finset A.

Parameter in_impl : A -> finset A -> Prop.
Parameter empty_impl : finset A.
Parameter single_impl : A -> finset A.
Parameter union_impl : finset A -> finset A -> finset A.
Parameter inter_impl : finset A -> finset A -> finset A.
Parameter remove_impl : finset A -> finset A -> finset A.
Parameter incl_impl : finset A -> finset A -> Prop.
Parameter disjoint_impl : finset A -> finset A -> Prop.
Parameter card_impl : finset A -> nat.

(** Extensionality *)

(*
Parameter extens_impl : forall E E', 
  incl_impl E E' -> incl_impl E' E -> E = E'.
*)
Parameter in_double_impl : forall E E', (forall x, in_impl x E <-> in_impl x E') -> E = E'.

(** Semantics of basic operations *)

Parameter in_empty_eq_impl : forall x, in_impl x empty_impl = False.
Parameter in_single_eq_impl : forall x y, in_impl x (single_impl y) = (x = y).
Parameter in_union_eq_impl : forall x E1 E2, in_impl x (union_impl E1 E2) = (in_impl x E1 \/ in_impl x E2).
Parameter in_inter_eq_impl : forall x E1 E2, in_impl x (inter_impl E1 E2) = (in_impl x E1 /\ in_impl x E2).
Parameter in_remove_eq_impl : forall x E1 E2, in_impl x (remove_impl E1 E2) = (in_impl x E1 /\ ~in_impl x E2).

Parameter incl_in_eq_impl : forall E1 E2, incl_impl E1 E2 = (forall x, in_impl x E1 -> in_impl x E2).
Parameter disjoint_in_eq_impl : forall E1 E2, disjoint_impl E1 E2 = (forall x, in_impl x E1 -> ~in_impl x E2).

Parameter from_list_in_eq_impl : forall L x, in_impl x (from_list_impl L) = Mem x L.
Parameter to_list_in_eq_impl : forall E x, Mem x (to_list_impl E) = in_impl x E.

Parameter mem_decidable : forall (s : finset A) x, Decidable (in_impl x s).

End Definitions.

End FinsetSig.

(* ********************************************************************** *)
(** * Implementation of finite sets *)

Module Export FinsetImpl : FinsetSig.

Section Operations.
Variables (A:Type).

Definition finite (U : set A) :=
  exists L, forall x, x \in U -> Mem x L.

Definition finset := sig finite.

Implicit Types x : A.
Implicit Types E : finset.

Definition build_fset `(F:finite U) : finset := exist finite U F.

Lemma finite_empty : finite \{}.
Proof. exists (@nil A). intros x. rewrite in_empty_eq. auto_false. Qed.

Lemma singleton_finite : forall x, finite \{x}.
Proof.
  intros. exists (x::nil). intros y. 
  rewrite in_single_eq. intro_subst. constructor.
Qed.

Lemma union_finite : forall U V : set A,
  finite U -> finite V -> finite (U \u V).
Proof.
  introv [L1 E1] [L2 E2]. exists (L1 ++ L2). intros x.
  rewrite in_union_eq. rewrite Mem_app_or_eq. introv [H|H]; auto. 
Qed.

Lemma inter_finite : forall U V : set A,
  finite U -> finite V -> finite (U \n V).
Proof.
  introv [L1 E1] [L2 E2]. exists (L1 ++ L2). intros x.
  rewrite in_inter_eq. rewrite Mem_app_or_eq. auto*.
Qed.

Lemma remove_finite : forall U V : set A,
  finite U -> finite V -> finite (U \- V).
Proof.
  introv [L1 E1] [L2 E2]. exists L1. intros x.
  rewrite in_remove_eq. introv [H1 H2]; auto. 
Qed.

Definition in_impl x E := x \in proj1_sig E.
Definition empty_impl := build_fset finite_empty.
Definition single_impl x := build_fset (singleton_finite x). 
Definition union_impl E E' := build_fset (union_finite (proj2_sig E) (proj2_sig E')).
Definition inter_impl E E' := build_fset (inter_finite (proj2_sig E) (proj2_sig E')).
Definition remove_impl E E' := build_fset (remove_finite (proj2_sig E) (proj2_sig E')).
Definition incl_impl E E' := forall x, in_impl x E -> in_impl x E'.
Definition disjoint_impl E E' := forall x, in_impl x E -> ~in_impl x E'.

Definition listish (U : set A) :=
  exists L, forall x, Mem x L = is_in x U.

Lemma finite_listish : forall U, finite U -> listish U.
Proof.
    unfolds finite, listish.
    introv (L&Hl).
    lets (L'&Hl') : Filters_exists A (fun x => x \in U) L.
    exists L'.
    intro.
    rew_logic.
    apply iff_intro; intro H.
    clear Hl.
    apply Filters_Forall in Hl'.
    applys Forall_Mem Hl'; auto.
    applys Filters_Mem; eauto.
Qed.

Definition from_list_impl (L : list A) : finset := 
  fold_right (fun x acc => union_impl (single_impl x) acc) empty_impl L.

Definition to_list_impl E : list A := 
  proj1_sig (indefinite_description (finite_listish (proj2_sig E))).

Definition card_impl E := length (to_list_impl E).

Lemma in_double_eq_impl : forall E F,
  (forall x, in_impl x E = in_impl x F) -> E = F.
Proof.
  unfold mem. intros [U FU] [V FV] H. simpls.
  apply exist_eq. apply in_double_eq. auto.
Qed. 

Lemma extens_impl : forall E F,
  incl_impl E F -> incl_impl F E -> E = F.
Proof. intros. apply in_double_eq_impl. extens*. Qed.

Lemma in_double_impl : forall E E', (forall x, in_impl x E <-> in_impl x E') -> E = E'.
Proof. intros. apply in_double_eq_impl. intros. rew_logic. auto. Qed.

Lemma in_empty_eq_impl : forall x, in_impl x empty_impl = False.
Proof. unfold in_impl, empty_impl. simpl. intros. rewrite in_empty_eq. auto*. Qed.

Lemma in_single_eq_impl : forall x y, in_impl x (single_impl y) = (x = y).
Proof. unfold in_impl, single_impl. simpl. intros. rewrite in_single_eq. auto*. Qed.

Lemma in_union_eq_impl : forall x E1 E2, in_impl x (union_impl E1 E2) = (in_impl x E1 \/ in_impl x E2).
Proof. unfold in_impl, union_impl. simpl. intros. rewrite in_union_eq. auto*. Qed.

Lemma in_inter_eq_impl : forall x E1 E2, in_impl x (inter_impl E1 E2) = (in_impl x E1 /\ in_impl x E2).
Proof. unfold in_impl, inter_impl. simpl. intros. rewrite in_inter_eq. auto*. Qed.

Lemma in_remove_eq_impl : forall x E1 E2, in_impl x (remove_impl E1 E2) = (in_impl x E1 /\ ~in_impl x E2).
Proof. unfold in_impl, remove_impl. simpl. intros. rewrite in_remove_eq. auto*. Qed.

Lemma incl_in_eq_impl : forall E1 E2, incl_impl E1 E2 = (forall x, in_impl x E1 -> in_impl x E2).
Proof. auto. Qed.

Lemma disjoint_in_eq_impl : forall E1 E2, disjoint_impl E1 E2 = (forall x, in_impl x E1 -> ~in_impl x E2).
Proof. auto. Qed.

Lemma from_list_in_eq_impl : forall L x, in_impl x (from_list_impl L) = Mem x L.
Proof. 
  unfold from_list_impl.
  intros. rew_logic. 
  apply iff_intro;
  induction L;
  simpl; (rewrite in_empty_eq_impl, Mem_nil_eq || rewrite in_union_eq_impl, Mem_cons_eq); iauto.
Qed.

Lemma to_list_in_eq_impl : forall E x, Mem x (to_list_impl E) = in_impl x E.
Proof. 
  unfold to_list_impl, in_impl.
  intro E.
  sets_eq L : (indefinite_description (finite_listish (proj2_sig E))).
  exact (proj2_sig L).
Qed.

Lemma mem_decidable : forall E x,
   Decidable (in_impl x E).
Proof.
skip.
Defined.

End Operations.
End FinsetImpl.

Global Instance union_inst : BagUnion (finset A) :=
  { union := @FinsetImpl.union_impl _ }.

Global Instance inter_inst : BagInter (finset A) :=
  { inter := @FinsetImpl.inter_impl _ }.

Global Instance remove_inst : BagRemove (finset A) (finset A) :=
  { remove := @FinsetImpl.remove_impl _ }.

Global Instance empty_inst : BagEmpty (finset A) := 
  { empty := @FinsetImpl.empty_impl _ }.

Global Instance in_inst : BagIn A (finset A) :=
  { is_in := @FinsetImpl.in_impl _ }.

Global Instance single_inst : BagSingle A (finset A) := 
  { single := @FinsetImpl.single_impl _ }.

Global Instance incl_inst : BagIncl (finset A) :=
  { incl := @FinsetImpl.incl_impl _ }.

Global Instance disjoint_inst : BagDisjoint (finset A) :=
  { disjoint := @FinsetImpl.disjoint_impl _ }.

Global Instance card_inst : BagCard (finset A) :=  
  { card := @FinsetImpl.card_impl _ }.

Global Instance from_list_inst : BagFromList A (finset A) :=
  { from_list := @FinsetImpl.from_list_impl _ }.

Global Instance to_list_inst : BagToList A (finset A) :=
  { to_list := @FinsetImpl.to_list_impl _ }.

Global Instance in_empty_eq_inst : In_empty_eq (T := finset A) :=
  { in_empty_eq := @FinsetImpl.in_empty_eq_impl _ }.

Global Instance in_single_eq_inst : In_single_eq (T := finset A) :=
  { in_single_eq := @FinsetImpl.in_single_eq_impl _ }.

Global Instance in_union_eq_inst : In_union_eq (T := finset A) :=
  { in_union_eq := @FinsetImpl.in_union_eq_impl _ }.

Global Instance in_inter_eq_inst : In_inter_eq (T := finset A) :=
  { in_inter_eq := @FinsetImpl.in_inter_eq_impl _ }.

Global Instance in_remove_eq_inst : In_remove_eq (T := finset A) :=
  { in_remove_eq := @FinsetImpl.in_remove_eq_impl _ }.

Global Instance in_double_inst : In_double (T := finset A) :=
  { in_double := @FinsetImpl.in_double_impl _ }.

Global Instance incl_in_eq_inst : Incl_in_eq (T := finset A) :=
  { incl_in_eq := @FinsetImpl.incl_in_eq_impl _ }.

Global Instance disjoint_in_eq_inst : Disjoint_in_eq (T := finset A) :=
  { disjoint_in_eq := @FinsetImpl.disjoint_in_eq_impl _ }.

Global Instance from_list_in_eq_inst : From_list_in_eq (T := finset A) :=
  { from_list_in_eq := @FinsetImpl.from_list_in_eq_impl _ }.

Global Instance to_list_in_eq_inst : To_list_in_eq (T := finset A) :=
  { to_list_in_eq := @FinsetImpl.to_list_in_eq_impl _ }.

Global Opaque union_inst inter_inst remove_inst empty_inst in_inst
    single_inst incl_inst disjoint_inst card_inst from_list_inst
    to_list_inst.

Extraction Language Ocaml.

Extract Constant FinsetImpl.finset "'A" => "'A BatSet.t". 
Extract Constant FinsetImpl.from_list_impl => "fun l -> BatSet.of_list l".
Extract Constant FinsetImpl.to_list_impl => "fun s -> BatSet.to_list s".
Extract Constant FinsetImpl.empty_impl => "BatSet.empty".
Extract Constant FinsetImpl.single_impl => "fun x -> BatSet.singleton x".
Extract Constant FinsetImpl.union_impl => "fun s1 s2 -> BatSet.union s1 s2".
Extract Constant FinsetImpl.inter_impl => "fun s1 s2 -> BatSet.intersect s1 s2".
Extract Constant FinsetImpl.remove_impl => "fun s1 s2 -> BatSet.diff s1 s2".

(* ********************************************************************** *)
(** * Derivable properties about finite sets *)

(*

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

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