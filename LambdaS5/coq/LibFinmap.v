Require Import LibTactics LibList LibListSorted.
Require Import LibSet LibLogic LibEqual LibReflect LibOrder LibRelation.
Generalizable Variable A R B.

Import ListNotations.
Open Scope list_scope.

(* TODO utitities *)
Definition rel_fst {A B} (R : binary A) : binary (A * B) := fun x y => R (fst x) (fst y).

Class BagReadOption A B T := { read_option : T -> A -> option B }. 

Notation "m \( x ?)" := (read_option m x)
  (at level 33, format "m \( x ?)") : container_scope.

Module Type FinmapSig.
Section Definitions. 

Variables (A B : Type) (LTA : Lt A).

Parameter finmap : forall (A B : Type) {LTA : Lt A}, Type.

Set Implicit Arguments.

Parameter from_list : list (A * B) -> finmap A B.
Parameter to_list : finmap A B -> list (A * B).

Parameter empty_impl : finmap A B.
Parameter single_bind_impl : A -> B -> finmap A B.
Parameter in_impl : A -> finmap A B -> Prop.
Parameter binds_impl : finmap A B -> A -> B -> Prop.
Parameter read_impl : Inhab B -> finmap A B -> A -> B.
Parameter read_option_impl : finmap A B -> A -> option B.
Parameter remove_impl : finmap A B -> A -> finmap A B.
Parameter update_impl : finmap A B -> A -> B -> finmap A B.

End Definitions.
End FinmapSig.

Module Export FinmapImpl : FinmapSig.
Section Definitions.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IB : Inhab B}.
Context {ST : Lt_strict_total_order }.

Inductive finmap_i := finmap_intro {
    finmap_list : list (A * B);
    finmap_sorted : sorted (rel_fst lt) finmap_list 
}.

Definition finmap := finmap_i.

Implicit Types k : A.
Implicit Types x : B.
Implicit Types M : finmap.


Definition to_list := finmap_list.
Definition from_list (l : list (A * B)) : finmap.
Admitted.

Definition empty_impl : finmap := finmap_intro nil (sorted_nil _).
Definition single_bind_impl k x : finmap := finmap_intro [(k, x)] (sorted_one _ _).
Definition in_impl k M : Prop := exists x, Assoc k x (finmap_list M).
Definition binds_impl M k x : Prop := Assoc k x (finmap_list M).
Definition read_option_impl M k : option B.
Admitted.
Definition read_impl M k : B := LibList.assoc k (finmap_list M).
Program Definition remove_impl M k : finmap := finmap_intro (remove_assoc k (finmap_list M)) _.
Obligation 1.
Admitted. 
Definition update_impl M k x : finmap.
Admitted.

End Definitions.
End FinmapImpl.

Section Instances.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IB : Inhab B}.
Context {ST : Lt_strict_total_order }.

Global Instance empty_inst : BagEmpty (finmap A B) :=
    { empty := @empty_impl _ _ _ }.

Global Instance single_bind_inst : Lt_strict_total_order -> BagSingleBind A B (finmap A B) :=
    { single_bind := @single_bind_impl _ _ _ }.

Global Instance in_inst : BagIn A (finmap A B) :=
    { is_in := @in_impl _ _ _ }.

Global Instance binds_inst : BagBinds A B (finmap A B) :=
    { binds := @binds_impl _ _ _ }.

Global Instance read_inst : BagRead A B (finmap A B) :=
    { read := @read_impl _ _ _ _ }.

Global Instance read_option_inst : BagReadOption A B (finmap A B) :=
    { read_option := @read_option_impl _ _ _ }.

Global Instance remove_inst : BagRemove (finmap A B) A :=
    { remove := @remove_impl _ _ _ }.

Global Instance write_inst : BagUpdate A B (finmap A B) :=
    { update := @update_impl _ _ _ }.

End Instances.

(* Extraction.
 * Ordering relation is ignored, because it does not extracts well.
 * Fortunately, hiding the implementation does not allow to actually observe the order.
 * Ordering is used on Coq side only for extensionality's sake. *)

Extraction Language Ocaml.

Extract Constant FinmapImpl.finmap "'A" "'B" => "('A, 'B) BatMap.t". 
Extract Constant FinmapImpl.from_list => "fun _ l -> BatMap.of_enum (BatList.enum l)".
Extract Constant FinmapImpl.to_list => "fun _ m -> BatMap.bindings m".
Extract Constant FinmapImpl.empty_impl => "fun _ -> BatMap.empty".
Extract Constant FinmapImpl.single_bind_impl => "fun _ k x -> BatMap.singleton k x".
Extract Constant FinmapImpl.read_impl => "fun _ m k -> BatMap.find k m".
Extract Constant FinmapImpl.read_option_impl => "fun _ m k -> try Some (BatMap.find k m) with Not_found -> None".
Extract Constant FinmapImpl.remove_impl => "fun _ m k -> BatMap.remove k m".
Extract Constant FinmapImpl.update_impl => "fun _ m k x -> BatMap.add k x m".

