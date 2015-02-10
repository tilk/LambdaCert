Set Implicit Arguments.
Generalizable All Variables.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import HeapUtils.
Require LibFset.
Require Import JsNumber.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require LibStream.
Open Scope list_scope.
Open Scope string_scope.
Open Scope char_scope.

Module Heap := HeapUtils.Heap.

Module Fset := LibFset.FsetImpl.

Fixpoint concat_list_heap {X Y : Type} (front : list (X * Y)) (back : Heap.heap X Y) : Heap.heap X Y :=
  match front with
  | nil => back
  | (key, val) :: tail => concat_list_heap tail (Heap.write back key val)
  end
.
Definition concat_heaps {X Y : Type} (front back : Heap.heap X Y) :=
  concat_list_heap (Heap.to_list front) back
.

Fixpoint zip_aux {X Y : Type} (lx : list X) (ly : list Y) (acc : list (X * Y)) : option (list (X * Y)) :=
  match lx with
  | nil =>
      match ly with
      | nil => Some acc
      | _ => None
      end
  | x_head :: x_tail =>
      match ly with
      | nil => None
      | y_head :: y_tail => zip_aux x_tail y_tail ((x_head, y_head) :: acc)
      end
  end
.
Definition zip_left {X Y : Type} (lx : list X) (ly : list Y) : option (list (X * Y)) :=
  zip_aux lx ly nil
.

Definition ascii_of_nat (a : nat) : ascii :=
  match (a mod 10) with
  | 0=>"0" | 1=>"1" | 2=>"2" | 3=>"3" | 4=>"4"
  | 5=>"5" | 6=>"6" | 7=>"7" | 8=>"8" | 9=>"9"
  | _=>"A"
  end
.

Parameter string_of_nat : nat -> string.

Import LibStream.

CoFixpoint nat_stream_from (k : nat) : LibStream.stream nat :=
  k ::: (nat_stream_from (S k)).

Definition id_stream_from k : LibStream.stream string :=
  map string_of_nat (nat_stream_from k). 

Definition prefixed_id_stream_from s k :=
  map (fun x => s ++ x) (id_stream_from k).

Fixpoint zipl_stream {A B : Type} (st : stream A) (l : list B) :=
    match st, l with
    | _, nil => nil
    | a ::: st', b :: l' => (a, b) :: zipl_stream st' l' 
    end.

Definition number_list_from {A : Type} k (l : list A) := zipl_stream (id_stream_from k) l.

(* this should go to TLC *)
Tactic Notation "cases_match_option" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [match ?B with Some _ => _ | None => _ end] => case_if_on B as Eq
  | K: context [match ?B with Some _ => _ | None => _ end] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_match_option" :=
  let Eq := fresh in cases_match_option as Eq.

Tactic Notation "cases_let" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [let '_ := ?B in _] => case_if_on B as Eq
  | K: context [let '_ := ?B in _] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_let" :=
  let Eq := fresh in cases_let as Eq.

Tactic Notation "injects" :=
    match goal with
    | H : _ = _ |- _ => injects H
    end.

