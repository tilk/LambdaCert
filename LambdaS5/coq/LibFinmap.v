Require Import LibTactics LibList LibListSorted.
Require Import LibSet LibLogic LibEqual LibReflect LibOrder LibRelation.
Generalizable Variable A R B.

Import ListNotations.
Open Scope list_scope.

(* TODO utitities *)
Definition rel_fst {A B} (R : binary A) : binary (A * B) := fun x y => R (fst x) (fst y).

(* TODO this should get to TLC LibBag later *)
Class BagReadOption A B T := { read_option : T -> A -> option B }. 
Class BagFresh A T := { fresh : T -> A }.

Notation "m \( x ?)" := (read_option m x)
  (at level 33, format "m \( x ?)") : container_scope.

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
Parameter card_impl : finmap A B -> nat.
Parameter fresh_impl : Minimal A -> PickGreater A -> finmap A B -> A. (* TODO good typeclasses *)

End Definitions.
End FinmapSig.

(* Implementation (based on sorted lists) *)

Module Export FinmapImpl : FinmapSig.
Section Definitions.

Variables (A B : Type).
Context {LTA : Lt A}.
Context {IA : Inhab A}.
Context {IB : Inhab B}.
Context {MMA : Minimal A}.
Context {PGA : PickGreater A}.
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
Definition card_impl M := length (finmap_list M).
Definition fresh_impl M : A := 
    match rev (finmap_list M) with 
    | nil => minimal
    | (k, x) :: _ => pick_greater k
    end.

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

Global Instance card_inst : BagCard (finmap A B) :=
    { card := @card_impl _ _ _ }.

Global Instance fresh_inst : Minimal A -> PickGreater A -> BagFresh A (finmap A B) :=
    { fresh := @fresh_impl _ _ _ _ _ }.

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
Extract Constant FinmapImpl.card_impl => "fun _ m -> BatMap.cardinal m".
Extract Constant FinmapImpl.fresh_impl => "fun _ mm pg m -> if BatMap.is_empty m then mm else pg (fst (BatMap.max_binding m))".
