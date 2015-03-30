Require Import LibTactics LibList LibListSorted.
Require Import LibSet LibMap LibLogic LibEqual LibReflect LibOrder LibRelation.
Require Import LibMapExt LibFinset LibBagExt.
Require Import Utils.
Generalizable Variable A R U B T.

Import ListNotations.
Open Scope list_scope.

(* TODO utitities *)
Definition rel_fst {A B} (R : binary A) : binary (A * B) := fun x y => R (fst x) (fst y).



(* TODO this should get to TLC LibOrder *)
Class Minimal A := { minimal : A }.
Class PickGreater A := { pick_greater : A -> A }.

Class Minimal_lt `{Lt A} `{Minimal A} := { minimal_lt : forall a, lt minimal a }.
Class PickGreater_lt `{Lt A} `{PickGreater A} := { pick_greater_lt : forall a, lt a (pick_greater a) }.

Global Instance minimal_inst_nat : Minimal nat := 
    { minimal := 0 }.
Global Instance pick_greater_inst_nat : PickGreater nat := 
    { pick_greater := S }.

(* Map signature (for hiding the implementation *)

Module Type FinmapSig.
Section Definitions. 

Variables (A B : Type).

Parameter finmap : forall (A B : Type), Type.

Set Implicit Arguments.

Parameter from_list_impl : list (A * B) -> finmap A B.
Parameter to_list_impl : finmap A B -> list (A * B).

Parameter empty_impl : finmap A B.
Parameter single_bind_impl : A -> B -> finmap A B.
Parameter index_impl : finmap A B -> A -> Prop.
Parameter binds_impl : finmap A B -> A -> B -> Prop.
Parameter incl_impl : finmap A B -> finmap A B -> Prop.
Parameter disjoint_impl : finmap A B -> finmap A B -> Prop.
Parameter read_impl : Inhab B -> finmap A B -> A -> B.
Parameter read_option_impl : finmap A B -> A -> option B.
Parameter union_impl : finmap A B -> finmap A B -> finmap A B.
Parameter remove_impl : finmap A B -> finset A -> finmap A B.
Parameter restrict_impl : finmap A B -> finset A -> finmap A B.
Parameter update_impl : finmap A B -> A -> B -> finmap A B.
Parameter card_impl : finmap A B -> nat.
Parameter fresh_impl : Minimal A -> PickGreater A -> finmap A B -> A. (* TODO good typeclasses *)

Parameter binds_double_impl : forall M M', (forall k x, binds_impl M k x <-> binds_impl M' k x) -> M = M'.

Parameter incl_binds_eq_impl : forall M1 M2, incl_impl M1 M2 = forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Parameter disjoint_binds_eq_impl : forall M1 M2, 
    disjoint_impl M1 M2 = forall k x x', binds_impl M1 k x -> ~binds_impl M2 k x'.
Parameter read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Parameter binds_empty_eq_impl : forall k x, binds_impl empty_impl k x = False.
Parameter binds_single_bind_eq_impl : forall k k' x x', 
    binds_impl (single_bind_impl k' x') k x = (k = k' /\ x = x').
Parameter binds_union_eq_impl : forall M1 M2 k x,
    binds_impl (union_impl M1 M2) k x = (binds_impl M1 k x \/ ~index_impl M1 k /\ binds_impl M2 k x).
Parameter binds_remove_eq_impl : forall M S k x,
    binds_impl (remove_impl M S) k x = (binds_impl M k x /\ k \notin S).
Parameter binds_restrict_eq_impl : forall M S k x,
    binds_impl (restrict_impl M S) k x = (binds_impl M k x /\ k \in S).
Parameter binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).
Parameter index_binds_eq_impl : forall M k, index_impl M k = exists x, binds_impl M k x.
Parameter fresh_index_eq_impl : forall M c1 c2, index_impl M (fresh_impl c1 c2 M) = False.

Parameter from_list_binds_eq_impl : forall L k x, binds_impl (from_list_impl L) k x = Assoc k x L.
Parameter to_list_binds_eq_impl : forall M k x, Assoc k x (to_list_impl M) = binds_impl M k x.

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

Definition finite (M : map A B) :=
  exists (S : finset A), forall x, index M x -> x \in S.

Definition finmap := sig finite.

Implicit Types k : A.
Implicit Types x : B.
Implicit Types M : finmap.

Definition build_finmap `(F:finite U) : finmap := exist finite U F.

(* TODO: most properties should follow from finset and map properties.
   Nice prerequisite: lib-bag-ize LibMap. *)

Set Implicit Arguments.

Lemma finite_empty : finite \{}.
Proof.
  exists (\{} : finset A).
  introv. rew_index_eq. iauto.
Qed. 

Lemma single_bind_finite : forall k x, finite (k \:= x).
Proof.
  intros. exists \{k}. intros y. 
  rew_index_eq. rew_in_eq. auto.
Qed.

Lemma union_finite : forall U V : map A B,
  finite U -> finite V -> finite (U \u V).
Proof.
  introv [S1 E1] [S2 E2]. exists (S1 \u S2). intros x.
  rew_index_eq. rew_in_eq. iauto.
Qed.

Lemma remove_finite : forall U {S : set A}, finite U -> finite (U \- S).
Proof.
  introv [S1 E1]. exists S1. 
Admitted.

Lemma update_finite : forall U k x, finite U -> finite (U \(k := x)).
Proof.
  introv [S1 E1]. exists (S1 \u \{k}).
Admitted.

Definition empty_impl : finmap := build_finmap finite_empty.
Definition single_bind_impl k x : finmap := build_finmap (single_bind_finite k x).
Definition index_impl M k : Prop := index (proj1_sig M) k.
Definition binds_impl M k x : Prop := binds (proj1_sig M) k x.
Definition incl_impl M1 M2 : Prop := forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Definition disjoint_impl M1 M2 : Prop := forall k x x', binds_impl M1 k x -> ~binds_impl M2 k x'.
Definition read_option_impl M k : option B := proj1_sig M k. (* TODO abstract it!!! change TLC *)
Definition read_impl M k : B := proj1_sig M \(k).
Definition union_impl M1 M2 : finmap := build_finmap (union_finite (proj2_sig M1) (proj2_sig M2)).
Definition remove_impl M (S : finset A) : finmap.
Admitted.
Definition restrict_impl M (S : finset A) : finmap.
Admitted.
Definition update_impl M k x : finmap := build_finmap (update_finite k x (proj2_sig M)).
Definition fresh_impl : Minimal A -> PickGreater A -> finmap -> A.
Admitted.

Definition binds_double_impl : forall M M', (forall k x, binds_impl M k x <-> binds_impl M' k x) -> M = M'.
Admitted.

Definition listish (U : map A B) := 
  exists L, forall k x, binds U k x = Mem (k, x) L.

Lemma finite_listish : forall U, finite U -> listish U.
Proof.
Admitted.

Definition from_list_impl (L : list (A * B)) : finmap := 
  fold_right (fun p acc => let '(k, x) := p in update_impl acc k x) empty_impl L.

Definition to_list_impl M := proj1_sig (indefinite_description (finite_listish (proj2_sig M))).

Definition card_impl M := length (to_list_impl M).

Lemma read_option_binds_eq_impl : forall M k x, (read_option_impl M k = Some x) = binds_impl M k x.
Proof.
Admitted.

Lemma incl_binds_eq_impl : forall M1 M2, incl_impl M1 M2 = forall k x, binds_impl M1 k x -> binds_impl M2 k x.
Proof. unfold incl_impl. auto. Qed.
Lemma disjoint_binds_eq_impl : forall M1 M2, 
    disjoint_impl M1 M2 = forall k x x', binds_impl M1 k x -> ~binds_impl M2 k x'.
Proof. unfold disjoint_impl. auto. Qed.
Parameter binds_empty_eq_impl : forall k x, binds_impl empty_impl k x = False.
Parameter binds_single_bind_eq_impl : forall k k' x x', 
    binds_impl (single_bind_impl k' x') k x = (k = k' /\ x = x').
Parameter binds_union_eq_impl : forall M1 M2 k x,
    binds_impl (union_impl M1 M2) k x = (binds_impl M1 k x \/ ~index_impl M1 k /\ binds_impl M2 k x).
Parameter binds_remove_eq_impl : forall M S k x,
    binds_impl (remove_impl M S) k x = (binds_impl M k x /\ k \notin S).
Parameter binds_restrict_eq_impl : forall M S k x,
    binds_impl (restrict_impl M S) k x = (binds_impl M k x /\ k \in S).

Lemma binds_update_eq_impl : forall M k k' x x', 
    binds_impl (update_impl M k' x') k x = (k = k' /\ x = x' \/ k <> k' /\ binds_impl M k x).
Proof.
    intros.
    rew_logic.
    apply iff_intro; intro H.
    skip.
Admitted.

Parameter index_binds_eq_impl : forall M k, index_impl M k = exists x, binds_impl M k x.
Parameter fresh_index_eq_impl : forall M c1 c2, index_impl M (fresh_impl c1 c2 M) = False.

Parameter from_list_binds_eq_impl : forall L k x, binds_impl (from_list_impl L) k x = Assoc k x L.
Parameter to_list_binds_eq_impl : forall M k x, Assoc k x (to_list_impl M) = binds_impl M k x.

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

Global Instance incl_inst : BagIncl (finmap A B) :=
    { incl := @incl_impl _ _ }.

Global Instance disjoint_inst : BagDisjoint (finmap A B) :=
    { disjoint := @disjoint_impl _ _ }.

Global Instance read_inst : BagRead A B (finmap A B) :=
    { read := @read_impl _ _ _ }.

Global Instance read_option_inst : BagReadOption A B (finmap A B) :=
    { read_option := @read_option_impl _ _ }.

Global Instance union_inst : BagUnion (finmap A B) :=
    { union := @union_impl _ _ }.

Global Instance remove_inst : BagRemove (finmap A B) (finset A) :=
    { remove := @remove_impl _ _ }.

Global Instance restrict_inst : BagRestrict (finmap A B) (finset A) :=
    { restrict := @restrict_impl _ _ }.

Global Instance update_inst : BagUpdate A B (finmap A B) :=
    { update := @update_impl _ _ }.

Global Instance card_inst : BagCard (finmap A B) :=
    { card := @card_impl _ _ }.

Global Instance from_list_inst : BagFromList (A * B) (finmap A B) :=
    { from_list := @from_list_impl _ _ }.

Global Instance to_list_inst : BagToList (A * B) (finmap A B) :=
    { to_list := @to_list_impl _ _ }.

Global Instance fresh_inst : Minimal A -> PickGreater A -> BagFresh A (finmap A B) :=
    { fresh := @fresh_impl _ _ _ _ }.

Global Instance binds_double_inst : Binds_double :=
    { binds_double := @binds_double_impl _ _ }.

Global Instance incl_binds_eq_inst : Incl_binds_eq :=
    { incl_binds_eq := @incl_binds_eq_impl _ _ }.

Global Instance disjoint_binds_eq_inst : Disjoint_binds_eq :=
    { disjoint_binds_eq := @disjoint_binds_eq_impl _ _ }.

Global Instance read_option_binds_eq_inst : Read_option_binds_eq :=
    { read_option_binds_eq := @read_option_binds_eq_impl _ _ }.

Global Instance binds_empty_eq_inst : Binds_empty_eq := 
    { binds_empty_eq := @binds_empty_eq_impl _ _ }.

Global Instance binds_single_bind_eq_inst : Binds_single_bind_eq := 
    { binds_single_bind_eq := @binds_single_bind_eq_impl _ _ }.

Global Instance binds_union_eq_inst : Binds_union_eq :=
    { binds_union_eq := @binds_union_eq_impl _ _ }.

Global Instance binds_remove_eq_inst : Binds_remove_eq :=
    { binds_remove_eq := @binds_remove_eq_impl _ _ }.

Global Instance binds_restrict_eq_inst : Binds_restrict_eq :=
    { binds_restrict_eq := @binds_restrict_eq_impl _ _ }.

Global Instance binds_update_eq_inst : Binds_update_eq :=
    { binds_update_eq := @binds_update_eq_impl _ _ }.

Global Instance index_binds_eq_inst : Index_binds_eq :=
    { index_binds_eq := @index_binds_eq_impl _ _ }.

Global Instance fresh_index_eq_inst : 
    forall (c1 : Minimal A) (c2 : PickGreater A), Fresh_index_eq (A := A) (T := finmap A B) :=
    { fresh_index_eq := fun x => @fresh_index_eq_impl _ _ x _ _ }.

Global Instance from_list_binds_eq_impl : From_list_binds_eq :=
    { from_list_binds_eq := @from_list_binds_eq_impl _ _ }.

Global Instance to_list_binds_eq_impl : To_list_binds_eq :=
    { to_list_binds_eq := @to_list_binds_eq_impl _ _ }.

End Instances.

Global Opaque empty_inst single_bind_inst index_inst binds_inst 
    incl_inst disjoint_inst read_inst read_option_inst union_inst remove_inst 
    restrict_inst update_inst from_list_inst to_list_inst card_inst fresh_inst.

(* Extraction. *)

Extraction Language Ocaml.

Extract Constant FinmapImpl.finmap "'A" "'B" => "('A, 'B) BatMap.t". 
Extract Constant FinmapImpl.from_list_impl => "fun l -> BatMap.of_enum (BatList.enum l)".
Extract Constant FinmapImpl.to_list_impl => "fun m -> BatMap.bindings m".
Extract Constant FinmapImpl.empty_impl => "BatMap.empty".
Extract Constant FinmapImpl.single_bind_impl => "fun k x -> BatMap.singleton k x".
Extract Constant FinmapImpl.read_impl => "fun m k -> BatMap.find k m".
Extract Constant FinmapImpl.read_option_impl => "fun m k -> try Some (BatMap.find k m) with Not_found -> None".
Extract Constant FinmapImpl.union_impl => "fun m1 m2 -> BatMap.union m2 m1".
Extract Constant FinmapImpl.remove_impl => "fun m s -> BatList.fold_right (BatMap.remove) (FinsetImpl.to_list_impl s) m". 
Extract Constant FinmapImpl.restrict_impl => "fun m s -> BatList.fold_left (fun cc i -> BatMap.add i (BatMap.find i m) cc) BatMap.empty (FinsetImpl.to_list_impl s)".
Extract Constant FinmapImpl.update_impl => "fun m k x -> BatMap.add k x m".
Extract Constant FinmapImpl.card_impl => "fun m -> BatMap.cardinal m".
Extract Constant FinmapImpl.fresh_impl => "fun mm pg m -> if BatMap.is_empty m then mm else pg (fst (BatMap.max_binding m))".
