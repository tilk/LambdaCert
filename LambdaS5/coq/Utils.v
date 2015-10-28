Set Implicit Arguments.
Generalizable All Variables.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import JsNumber.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require LibStream.
Require Import LibEpsilon.
Open Scope list_scope.
Open Scope string_scope.
Open Scope char_scope.
Open Scope container_scope.

Fixpoint zipWith {X Y Z : Type} (f : X -> Y -> Z) (lx : list X) (ly : list Y) : option (list Z) :=
  match lx with
  | nil =>
      match ly with
      | nil => Some nil
      | _ => None
      end
  | x_head :: x_tail =>
      match ly with
      | nil => None
      | y_head :: y_tail => LibOption.map (fun l => f x_head y_head :: l) (zipWith f x_tail y_tail)
      end
  end
.

Definition zip {X Y : Type} := zipWith (fun (x : X) (y : Y) => (x,y)).

Inductive ZipWith {X Y Z : Type} (f : X -> Y -> Z) : list X -> list Y -> list Z -> Prop :=
  | ZipWith_nil : ZipWith f nil nil nil
  | ZipWith_cons : forall l1 l2 l3 x1 x2,
      ZipWith f l1 l2 l3 ->
      ZipWith f (x1 :: l1) (x2 :: l2) (f x1 x2 :: l3).

Definition Zip {X Y : Type} := ZipWith (fun (x : X) (y : Y) => (x,y)).

Lemma zipWith_ZipWith : forall X Y Z (f : X -> Y -> Z) lx ly lz, 
  zipWith f lx ly = Some lz -> ZipWith f lx ly lz.
Proof.
  induction lx; introv Hz;
  destruct ly;
  simpls;
  tryfalse.
  injects Hz.
  apply ZipWith_nil.
  sets_eq l : (zipWith f lx ly).
  destruct l; tryfalse.
  injects Hz.
  apply ZipWith_cons.
  auto.
Qed.

Lemma ZipWith_zipWith : forall X Y Z (f : X -> Y -> Z) lx ly lz, 
  ZipWith f lx ly lz -> zipWith f lx ly = Some lz.
Proof.
  introv Hz.
  induction Hz.
  reflexivity.
  simpl.
  rewrite IHHz.
  reflexivity.
Qed.

Lemma zip_Zip : forall X Y (lx : list X) (ly : list Y) lz, zip lx ly = Some lz -> Zip lx ly lz.
Proof. introv. apply zipWith_ZipWith. Qed.

Lemma Zip_zip : forall X Y (lx : list X) (ly : list Y) lz, Zip lx ly lz -> zip lx ly = Some lz.
Proof. introv. apply ZipWith_zipWith. Qed.

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
Hint Extern 0 (~ _) => solve [let H := fresh in intro H; inversion H].
Hint Extern 1 (?x <> _) => solve [intro; subst x; false]. 
Hint Extern 1 (_ = _) => reflexivity. 

Tactic Notation "cases_match_option" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [match ?B with Some _ => _ | None => _ end] => case_if_on B as Eq
  | K: context [match ?B with Some _ => _ | None => _ end] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_match_option" :=
  let Eq := fresh in cases_match_option as Eq.

Tactic Notation "cases_match_list" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [match ?B with _ :: _ => _ | nil => _ end] => case_if_on B as Eq
  | K: context [match ?B with _ :: _ => _ | nil => _ end] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_match_list" :=
  let Eq := fresh in cases_match_list as Eq.

Tactic Notation "cases_let" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [let '_ := ?B in _] => case_if_on B as Eq
  | K: context [let '_ := ?B in _] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_let" :=
  let Eq := fresh in cases_let as Eq.

Tactic Notation "cases_decide" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [decide ?B] => rewrite decide_def; cases_if as Eq
  | K: context [decide ?B] |- _ => rewrite decide_def in K; cases_if as Eq
  end.

Tactic Notation "cases_decide" :=
  let Eq := fresh in cases_decide as Eq.

Ltac cases_isTrue_after H := 
    ((apply eq_false_r in H; rewrite istrue_neg in H) || apply eq_true_r in H); rewrite istrue_isTrue in H.

Tactic Notation "cases_isTrue" "as" ident(Eq) :=
  match goal with
  | |- context [isTrue ?B] => case_if_on (isTrue B) as Eq; cases_isTrue_after Eq
  | K: context [isTrue ?B] |- _ => case_if_on (isTrue B) as Eq; cases_isTrue_after Eq
  end.

Tactic Notation "cases_isTrue" "in" "*" "as" ident(Eq) :=
  match goal with
  | K: context [isTrue ?B] |- _ => case_if_on (isTrue B) as Eq; cases_isTrue_after Eq
  | |- context [isTrue ?B] => case_if_on (isTrue B) as Eq; cases_isTrue_after Eq
  end.

Tactic Notation "cases_isTrue" "in" "*" :=
  let Eq := fresh in cases_isTrue in * as Eq.

Tactic Notation "cases_isTrue" :=
  let Eq := fresh in cases_isTrue as Eq.

Tactic Notation "injects" :=
    match goal with
    | H : _ = _ |- _ => injects H
    end.

Tactic Notation "not" tactic3(tac) := match True with _ => ((tac ; fail 1) || idtac) end.

Tactic Notation "if" tactic(t1) "then" tactic(t2) := match True with _ => (try (t1; fail 1); fail 1) || t2 end.

Tactic Notation "is_hyp" constr(t) := match goal with H : t |- _ => idtac end.

Ltac destruct_hyp H := match type of H with
    | _ \/ _ => destruct H as [H|H]; try destruct_hyp H
    | _ /\ _ => 
        let H1 := fresh H in let H2 := fresh H in 
        destruct H as (H1&H2); try destruct_hyp H1; try destruct_hyp H2
    | exists v, _ => let v := fresh v in destruct H as (v&H); try destruct_hyp H
    | ?x = _ => is_var x; subst x
    | _ = ?x => is_var x; subst x
    end.

Ltac option_neq_positivize := 
    match goal with
    | H : ?o <> None |- _  =>
       let x := fresh "x" in let H' := fresh in 
       set_eq x H' : o in H; destruct x; tryfalse; clear H; symmetry in H'; rename H' into H
    | H : None <> ?o  |- _  =>
       let x := fresh "x" in let H' := fresh in 
       set_eq x H' : o in H; destruct x; tryfalse; clear H; rename H' into H
    end.

(* TODO move to LibList *)
Section LogicList.
Variables A A1 A2 B C : Type.

Inductive NthDef : A -> nat -> list A -> A -> Prop :=
  | NthDef_nil : forall d k,
      NthDef d k nil d
  | NthDef_here : forall d l x,
      NthDef d 0 (x::l) x
  | NthDef_next : forall d y k l x,
      NthDef d k l x ->
      NthDef d (S k) (y::l) x.

Hint Constructors NthDef.
Hint Constructors Nth.

Lemma Nth_to_NthDef : forall k l x d, Nth k l x -> NthDef d k l x.
Proof.
    introv Hnth. induction~ Hnth.
Qed.

Lemma NthDef_to_Nth : forall k l x d, NthDef d k l x -> Nth k l x \/ k >= length l /\ x = d.
Proof.
    introv Hnthd. induction Hnthd; rew_length.
    + intuition math.
    + eauto.
    + destruct_hyp IHHnthd. eauto. intuition math.
Qed.

Lemma NthDef_to_nth_def : forall k l x d, NthDef d k l x -> nth_def d k l = x.
Proof.
    introv Hnthd. induction Hnthd; try destruct k; simpl; eauto.
Qed.

Lemma nth_def_to_NthDef : forall k l x d, nth_def d k l = x -> NthDef d k l x.
Proof.
    induction k; introv Heq; destruct l; simpls; substs; eauto.
Qed.

End LogicList.

(* for faster inverts *)

Ltac inverts_tactic_general T H :=
  let rec go :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh in intro H;
                           first [ subst x | subst y | injects H ];
                           go 
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go 
    | |- (?P -> ?Q) => intro; go 
    | |- (forall _, _) => intro; go 
    end in
  generalize ltac_mark; T H; go;
  unfold eq' in *.

Lemma list_rev_ind
     : forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (l & a)) ->
       forall l : list A, P l.
Proof.
    introv Hbase Hstep.
    intro l.
    asserts (l'&Heq) : (exists l', l = rev l').
    exists (rev l). rew_rev. reflexivity.
    gen l.
    induction l'; intros; substs; rew_rev; auto.
Qed.

(* TODO move this lemma *)
Lemma list_map_tlc : forall A B (f : A -> B) l, 
    List.map f l = LibList.map f l.
Proof.
    induction l.
    reflexivity.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* TODO move to TLC *)
Global Instance Exists_decidable : 
    forall `(l : list A) P (HD : forall a, Decidable (P a)), Decidable (Exists P l).
Proof.
    introv HD.
    applys decidable_make (exists_st (fun a => decide (P a)) l).
    induction l as [ | a l]; unfolds exists_st; simpl.
    fold_bool; rew_reflect. eauto using Exists_nil_inv. 
    rew_refl.
    rewrite IHl.
    remember (isTrue (P a)) as b1 eqn: Eq1.
    destruct b1; rew_bool; fold_bool. 
    rew_refl in *.
    apply~ Exists_here.
    remember (isTrue (Exists P l)) as b2 eqn: Eq2.
    destruct b2; fold_bool.
    rew_reflect in *.
    apply~ Exists_next.
    rew_reflect in *.
    intro.
    inverts~ H.
Defined.

(* TODO move to utilities *)

Inductive Has_dupes {A : Type} : list A -> Prop :=
    | Has_dupes_here : forall a l, Exists (fun b => a = b) l -> Has_dupes (a :: l)
    | Has_dupes_next : forall a l, Has_dupes l -> Has_dupes (a :: l).

Fixpoint has_dupes `{c : Comparable A} (l : list A) := 
    match l with
    | a :: l' => exists_st (fun b => decide (a = b)) l' || has_dupes l'
    | nil => false
    end.

Global Instance Has_dupes_decidable : forall `(l : list A) `(c : Comparable A),
    Decidable (Has_dupes l).
Proof.
    intros.
    applys decidable_make (has_dupes l).
    induction l as [ | a l]; unfold has_dupes; simpl.
    fold_bool; rew_reflect. intro. inverts H.
    fold has_dupes.
    rewrite IHl.
    skip. (* TODO *)
Defined.

Class Deterministic `(P : A -> Prop) : Prop := {
    deterministic : forall {a a'}, P a -> P a' -> a = a'
}.

Instance eq_deterministic : forall `(a : A), Deterministic (eq a).
Proof. introv. constructor. introv Heq1 Heq2. substs. reflexivity. Qed.

Section Det.
Context `{Inhab A} `{@Deterministic A P}. 

Lemma deterministic_epsilon : forall {a}, P a -> epsilon P = a.
Proof. introv Hp. spec_epsilon* as b. Qed.

End Det.

Tactic Notation "determine_eq" constr(H1) constr(H2) "as" ident(H) :=
    lets H : (deterministic H1 H2).

Tactic Notation "determine" constr(H1) constr(H2) :=
    let H := fresh in determine_eq H1 H2 as H; 
    first [subst_hyp H; try clear H2 | injects H; try clear H2 | idtac].

Tactic Notation "determine" := 
    match goal with
    | H1 : ?P ?x1, H2 : ?P ?x2 |- _ => 
        not (first [constr_eq H1 H2 | constr_eq x1 x2 | is_hyp (x1 = x2) | is_hyp (x2 = x1)]); determine H1 H2
    end.

Tactic Notation "determine_epsilon" := 
    match goal with
    | H1 : ?P ?x, H2 : context [ @epsilon _ _ ?P ] |- _ => 
        rewrite (deterministic_epsilon H1) in H2 
    | H1 : ?P ?x |- context [ @epsilon _ _ ?P ] => 
        rewrite (deterministic_epsilon H1) 
    end.

Tactic Notation "determine_epsilon" "using" hyp(H) := rewrite_all (deterministic_epsilon H) in *.

(* TODO move *)
Lemma impl_True_l : forall P : Prop, (True -> P) = P.
Proof. intro. apply* prop_ext. Qed.

Lemma impl_False_l : forall P : Prop, (False -> P) = True.
Proof. intro. apply* prop_ext. Qed.

Lemma impl_True_r : forall P : Prop, (P -> True) = True.
Proof. intro. apply* prop_ext. Qed.

Lemma impl_False_r : forall P : Prop, (P -> False) = ~P.
Proof. intro. apply* prop_ext. Qed.

Hint Rewrite impl_True_l impl_False_l impl_True_r impl_False_r : rew_logic.

Fixpoint fast_assoc {A B} (f : forall a1 a2, {a1 = a2} + {a1 <> a2}) (x : A) (l : list (A * B)) : option B :=
    match l with
    | nil => None
    | (x', v') :: l' => match f x' x with left _ => Some v' | right _ => fast_assoc f x l' end
    end.

Definition fast_string_assoc {A} : string -> list (string * A) -> option A := fast_assoc string_dec.

Definition fast_nat_assoc {A} : nat -> list (nat * A) -> option A := fast_assoc eq_nat_dec.

Lemma Assoc_Mem : forall T A l (k : T) (v : A), Assoc k v l -> Mem (k, v) l.
Proof.
    introv Ha.
    induction Ha.
    + apply Mem_here.
    + apply Mem_next. assumption.
Qed.

Import LibList.

Lemma fast_assoc_assoc_eq : forall A B d (k : A) l (v : B), Assoc k v l = (fast_assoc d k l = Some v).
Proof.
    introv. rew_logic. split; introv Hf. {
        induction Hf; simpl; cases_if; auto.
    } {
        induction l; tryfalse.
        simpls. cases_let. cases_if.
        injects.
        eapply Assoc_here.
        eapply Assoc_next. eapply IHl. assumption. auto. 
    }
Qed.

Lemma fast_assoc_assoc : forall A B (k : A) l (v : B) d, fast_assoc d k l = Some v -> Assoc k v l.
Proof.
    introv. erewrite fast_assoc_assoc_eq. eauto.
Qed.

Lemma assoc_fast_assoc : forall A B (k : A) l (v : B) d, Assoc k v l -> fast_assoc d k l = Some v.
Proof.
    introv. erewrite fast_assoc_assoc_eq. eauto.
Qed.

Lemma fast_assoc_not_assoc : forall A B k (l : list (A * B)) d, 
    fast_assoc d k l = None -> forall v, ~Assoc k v l.
Proof.
    introv Hf Ha.
    induction Ha; simpls; cases_if.
Qed.

Lemma fast_assoc_mem : forall A B (k : A) l (v : B) d, fast_assoc d k l = Some v -> Mem (k, v) l.
Proof.
    introv Hf. applys Assoc_Mem. applys fast_assoc_assoc. eassumption.
Qed.

Lemma fast_string_assoc_assoc : forall A k l (v : A), fast_string_assoc k l = Some v -> Assoc k v l.
Proof. introv. eapply fast_assoc_assoc. Qed.

Lemma assoc_fast_string_assoc : forall A k l (v : A), Assoc k v l -> fast_string_assoc k l = Some v.
Proof. introv. eapply assoc_fast_assoc. Qed.

Lemma fast_string_assoc_mem : forall A k l (v : A), fast_string_assoc k l = Some v -> Mem (k, v) l.
Proof. introv. eapply fast_assoc_mem. Qed.

Lemma fast_nat_assoc_assoc : forall A k l (v : A), fast_nat_assoc k l = Some v -> Assoc k v l.
Proof. introv. eapply fast_assoc_assoc. Qed.

Lemma assoc_fast_nat_assoc : forall A k l (v : A), Assoc k v l -> fast_nat_assoc k l = Some v.
Proof. introv. eapply assoc_fast_assoc. Qed.

Lemma fast_nat_assoc_mem : forall A k l (v : A), fast_nat_assoc k l = Some v -> Mem (k, v) l.
Proof. introv. eapply fast_assoc_mem. Qed.

(* instances *)

Global Instance le_string_inst : Le string.
Admitted.

Extraction Language Ocaml.

Extract Constant le_string_inst => "LibOrder.Build_Le". (* TODO *)
