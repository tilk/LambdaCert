Require Import LibTactics LibList LibListSorted.
Require Import LibSet LibMap LibLogic LibEqual LibReflect LibOrder LibRelation.
Require Import LibFinset.
Generalizable Variable A R U B T.

Import ListNotations.
Open Scope list_scope.

(* TODO utitities *)
Definition rel_fst {A B} (R : binary A) : binary (A * B) := fun x y => R (fst x) (fst y).

(* TODO this should get to TLC LibBag later *)
Class BagReadOption A B T := { read_option : T -> A -> option B }. 
Class BagFresh A T := { fresh : T -> A }.

Notation "m \( x ?)" := (read_option m x)
  (at level 33, format "m \( x ?)") : container_scope.

Class ReadOptionBinds_eq `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds_eq : forall M k x, (M \(k?) = Some x) = binds M k x }.

Class ReadOptionBinds `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds : forall M k x, M \(k?) = Some x -> binds M k x }.

Class ReadOptionBinds_inv `{BagReadOption A B T} `{BagBinds A B T} :=
    { read_option_binds_inv : forall M k x, binds M k x -> M \(k?) = Some x }.

Class BindsUpdate_eq `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_eq : forall M k k' x x', 
        binds (M \(k' := x')) k x = (k = k' /\ x = x' \/ k <> k' /\ binds M k x) }.

Class BindsUpdate_same_eq `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same_eq : forall M k x x', binds (M \(k := x)) k x' = (x = x') }.

Class BindsUpdate_same `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same : forall M k x, binds (M \(k := x)) k x }.

Class BindsUpdate_same_inv `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_same_inv : forall M k x x', binds (M \(k := x)) k x' -> x = x' }.

Class BindsUpdate_diff `{BagBinds A B T} `{BagUpdate A B T} := 
    { binds_update_diff : forall M k k' x, k <> k' -> binds M k x -> binds (M \(k' := x)) k x }.

Instance read_option_binds_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    ReadOptionBinds_eq -> ReadOptionBinds.
Proof. constructor. introv I. rewrite <- read_option_binds_eq. assumption. Qed.

Instance read_option_binds_inv_from_read_option_binds_eq : 
    forall `{BagReadOption A B T} `{BagBinds A B T},
    ReadOptionBinds_eq -> ReadOptionBinds_inv.
Proof. constructor. introv I. rewrite read_option_binds_eq. assumption. Qed.

Instance binds_update_same_eq_from_binds_update_eq :
    forall `{BagBinds A B T} `{BagUpdate A B T},
    BindsUpdate_eq -> BindsUpdate_same_eq.
Proof. 
    constructor. intros. rewrite binds_update_eq. rew_logic. 
    apply iff_intro; iauto.
Qed.

Instance binds_update_same_from_binds_update_same_eq :
    forall `{BagBinds A B T} `{BagUpdate A B T},
    BindsUpdate_same_eq -> BindsUpdate_same.
Proof. constructor. intros. rewrite binds_update_same_eq. reflexivity. Qed.

Instance binds_update_same_inv_from_binds_update_same_eq :
    forall `{BagBinds A B T} `{BagUpdate A B T},
    BindsUpdate_same_eq -> BindsUpdate_same_inv.
Proof. constructor. introv I. rewrite binds_update_same_eq in I. assumption. Qed.

(* TODO this should get to TLC LibOrder *)
Class Minimal A := { minimal : A }.
Class PickGreater A := { pick_greater : A -> A }.

Class Minimal_lt `{Lt A} `{Minimal A} := { minimal_lt : forall a, lt minimal a }.
Class PickGreater_lt `{Lt A} `{PickGreater A} := { pick_greater_lt : forall a, lt a (pick_greater a) }.

Instance minimal_inst_nat : Minimal nat := 
    { minimal := 0 }.
Instance pick_greater_inst_nat : PickGreater nat := 
    { pick_greater := S }.

(* Map signature (for hiding the implementation *)

Module Type FinmapSig.
Section Definitions. 

Variables (A B : Type).

Parameter finmap : forall (A B : Type), Type.

Set Implicit Arguments.

Parameter from_list : list (A * B) -> finmap A B.
Parameter to_list : finmap A B -> list (A * B).

Parameter empty_impl : finmap A B.
Parameter single_bind_impl : A -> B -> finmap A B.
Parameter index_impl : finmap A B -> A -> Prop.
Parameter binds_impl : finmap A B -> A -> B -> Prop.
Parameter read_impl : Inhab B -> finmap A B -> A -> B.
Parameter read_option_impl : finmap A B -> A -> option B.
Parameter remove_impl : finmap A B -> finset A -> finmap A B.
Parameter update_impl : finmap A B -> A -> B -> finmap A B.
Parameter card_impl : finmap A B -> nat.
Parameter fresh_impl : Minimal A -> PickGreater A -> finmap A B -> A. (* TODO good typeclasses *)

Parameter read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Parameter binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).

End Definitions.
End FinmapSig.

(* Implementation *)

Module Export FinmapImpl : FinmapSig.
Section Definitions.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IA : Inhab A}.
Context {IB : Inhab B}.
Context {MMA : Minimal A}.
Context {PGA : PickGreater A}.
Context {ST : Lt_strict_total_order }.

Definition finite (M : map A B) :=
  exists (S : finset A), forall x, index M x -> x \in S.

Definition finmap := sig finite.

Implicit Types k : A.
Implicit Types x : B.
Implicit Types M : finmap.

Definition build_finmap `(F:finite U) : finmap := exist finite U F.

Lemma finite_empty : finite \{}.
Proof.
  exists (\{} : finset A). 
Admitted.

Lemma single_bind_finite : forall k x, finite (k \:= x).
Proof.
  intros. exists \{k}. intros y. 
Admitted.

Lemma union_finite : forall U V : map A B,
  finite U -> finite V -> finite (U \u V).
Proof.
  introv [S1 E1] [S2 E2]. exists (S1 \u S2). intros x.
  rewrite in_union_eq. 
Admitted.

Lemma remove_finite : forall U {S : set A}, finite U -> finite (U \- S).
Proof.
  introv [S1 E1]. exists S1. 
Admitted.

Set Implicit Arguments.

Lemma update_finite : forall U k x, finite U -> finite (U \(k := x)).
Proof.
  introv [S1 E1]. exists (S1 \u \{k}).
Admitted.

Definition empty_impl : finmap := build_finmap finite_empty.
Definition single_bind_impl k x : finmap := build_finmap (single_bind_finite k x).
Definition index_impl M k : Prop := index (proj1_sig M) k.
Definition binds_impl M k x : Prop := binds (proj1_sig M) k x.
Definition read_option_impl M k : option B := proj1_sig M k. (* TODO abstract it!!! change TLC *)
Definition read_impl M k : B := proj1_sig M \(k).
Definition remove_impl M (S : finset A) : finmap.
Admitted.
Definition update_impl M k x : finmap := build_finmap (update_finite k x (proj2_sig M)).
Definition fresh_impl : Minimal A -> PickGreater A -> finmap -> A.
Admitted.

Definition listish (U : map A B) := 
  exists L, forall k x, binds U k x = Mem (k, x) L.

Lemma finite_listish : forall U, finite U -> listish U.
Proof.
Admitted.

Definition from_list (L : list (A * B)) : finmap := 
  fold_right (fun p acc => let '(k, x) := p in update_impl acc k x) empty_impl L.

Definition to_list M := proj1_sig (indefinite_description (finite_listish (proj2_sig M))).

Definition card_impl M := length (to_list M).

Lemma read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Proof.
Admitted.

Lemma binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).
Proof.
    intros.
    rew_logic.
    apply iff_intro; intro H.
    skip.
Admitted.

End Definitions.
End FinmapImpl.

Section Instances.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IB : Inhab B}.
Context {ST : Lt_strict_total_order }.

Global Instance empty_inst : BagEmpty (finmap A B) :=
    { empty := @empty_impl _ _ }.

Global Instance single_bind_inst : Lt_strict_total_order -> BagSingleBind A B (finmap A B) :=
    { single_bind := @single_bind_impl _ _ }.

Global Instance index_inst : BagIndex (finmap A B) A :=
    { index := @index_impl _ _ }.

Global Instance binds_inst : BagBinds A B (finmap A B) :=
    { binds := @binds_impl _ _ }.

Global Instance read_inst : BagRead A B (finmap A B) :=
    { read := @read_impl _ _ _ }.

Global Instance read_option_inst : BagReadOption A B (finmap A B) :=
    { read_option := @read_option_impl _ _ }.

Global Instance remove_inst : BagRemove (finmap A B) (finset A) :=
    { remove := @remove_impl _ _ }.

Global Instance update_inst : BagUpdate A B (finmap A B) :=
    { update := @update_impl _ _ }.

Global Instance card_inst : BagCard (finmap A B) :=
    { card := @card_impl _ _ }.

Global Instance fresh_inst : Minimal A -> PickGreater A -> BagFresh A (finmap A B) :=
    { fresh := @fresh_impl _ _ _ _ }.

Global Instance read_option_binds_eq_inst : ReadOptionBinds_eq :=
    { read_option_binds_eq := @read_option_binds_eq_impl _ _ }.

Global Instance binds_update_eq_inst : BindsUpdate_eq :=
    { binds_update_eq := @binds_update_eq_impl _ _ }.

End Instances.

Global Opaque empty_inst single_bind_inst in_inst binds_inst read_inst
    read_option_inst remove_inst update_inst card_inst fresh_inst.

(* Extraction.
 * Ordering relation is ignored, because it does not extracts well.
 * Fortunately, hiding the implementation does not allow to actually observe the order.
 * Ordering is used on Coq side only for extensionality's sake. *)

Extraction Language Ocaml.

Extract Constant FinmapImpl.finmap "'A" "'B" => "('A, 'B) BatMap.t". 
Extract Constant FinmapImpl.from_list => "fun l -> BatMap.of_enum (BatList.enum l)".
Extract Constant FinmapImpl.to_list => "fun m -> BatMap.bindings m".
Extract Constant FinmapImpl.empty_impl => "BatMap.empty".
Extract Constant FinmapImpl.single_bind_impl => "fun k x -> BatMap.singleton k x".
Extract Constant FinmapImpl.read_impl => "fun m k -> BatMap.find k m".
Extract Constant FinmapImpl.read_option_impl => "fun m k -> try Some (BatMap.find k m) with Not_found -> None".
(* Extract Constant FinmapImpl.remove_impl => "fun m k -> BatMap.remove k m". *)
 Extract Constant FinmapImpl.remove_impl => "fun m s -> BatList.fold_right (BatMap.remove) (FinsetImpl.to_list s) m". 
Extract Constant FinmapImpl.update_impl => "fun m k x -> BatMap.add k x m".
Extract Constant FinmapImpl.card_impl => "fun m -> BatMap.cardinal m".
Extract Constant FinmapImpl.fresh_impl => "fun mm pg m -> if BatMap.is_empty m then mm else pg (fst (BatMap.max_binding m))".
