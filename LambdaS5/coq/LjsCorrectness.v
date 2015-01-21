Set Implicit Arguments.
Require Import LjsShared.
Require Import Syntax.
Require Import PrettyInterm.
Require Import PrettyRules.
Require Import Store.
Require Import Context.
Require Import Values.
Require Import Operators.
Require Import Monads.
Require Import Interpreter.
Require Import Coq.Strings.String.

Require Import List.
Import ListNotations.

Open Scope list_scope.

Implicit Type A B : Type.
Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type loc : value_loc.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.
Implicit Type re : result.
Implicit Type r : res.

Record runs_type_correct runs :=
    make_runs_type_correct {
        runs_type_correct_eval : forall c st e o,
            runs_type_eval runs c st e = result_some o -> red_expr c st e o
}.

(* Lemmas on monadic ops *)

Definition is_some {A} ra (Pred : A -> Prop) :=
    exists a, ra = result_some a /\ Pred a.

Hint Unfold is_some.

Lemma is_some_covariant : forall A (P1 P2 : A -> Prop), 
    (forall a, P1 a -> P2 a) -> 
    forall ra, is_some ra P1 -> is_some ra P2. 
Proof. unfold is_some. jauto. Qed.

Hint Resolve is_some_covariant.

Lemma if_result_some_out : forall A B (ra : resultof A) (b : B) cont, 
    if_result_some ra cont = result_some b -> 
    is_some ra (fun a => cont a = result_some b).
Proof. introv E. destruct* ra; intros; false. Qed.

Definition if_out_ter_post (cont : store -> res -> result) o' o :=
    (exists st r, o = out_ter st r /\ cont st r = result_some o') \/
    (o = out_div /\ o' = o).

Lemma if_out_ter_out : forall re o cont, 
    if_out_ter re cont = result_some o -> 
    is_some re (if_out_ter_post cont o).
Proof.
    introv E.
    lets H: if_result_some_out E.
    gen H. 
    apply is_some_covariant.
    intros o1 E1.  
    destruct o1; inverts E1; unfolds*; tryfalse.
Qed.

Definition eqabort o' o := abort o /\ o' = o.

Hint Unfold eqabort.

Definition if_value_post (cont : store -> value -> result) o' o := 
    (exists st v, o = out_ter st (res_value v) /\ cont st v = result_some o') \/
    eqabort o' o.

Lemma if_value_out : forall re o cont,
    if_value re cont = result_some o ->
    is_some re (if_value_post cont o).
Proof.
    introv E. 
    apply if_out_ter_out in E. 
    gen E.
    apply is_some_covariant.
    intros o1 E.
    unfolds.
    destruct o1;
    (inverts E as H; [inverts H as H; inverts H as H; inverts H as H H1 | inverts H as H]); jauto; tryfalse.
    destruct* x0; inverts H; inverts H1; jauto.
Qed.

Lemma assert_get_object_ptr_out : forall v o cont,
    assert_get_object_ptr v cont = result_some o ->
    exists ptr, v = value_object ptr /\ cont ptr = result_some o.
Proof.
    introv E. destruct* v; false.
Qed.

Lemma assert_get_string : forall v o cont,
    assert_get_string v cont = result_some o ->
    exists s, v = value_string s /\ cont s = result_some o.
Proof.
    introv E. destruct* v; false.
Qed.

Lemma assert_get_bool : forall v o cont,
    assert_get_bool v cont = result_some o ->
    exists b, v = bool_to_value b /\ cont b = result_some o.
Proof.
    introv E. destruct* v; tryfalse; [exists true | exists false]; jauto. 
Qed.

Lemma assert_get_object_from_ptr_out : forall st ptr o cont,
    assert_get_object_from_ptr st ptr cont = result_some o ->
    exists obj, get_object st ptr = Some obj /\ cont obj = result_some o.
Proof.
    introv E. unfold assert_get_object_from_ptr in E.
    destruct* (get_object st ptr); tryfalse.
Qed.

Lemma assert_get_object_out : forall st v o cont,
    assert_get_object st v cont = result_some o -> 
    exists ptr obj, v = value_object ptr /\ get_object st ptr = Some obj /\ cont obj = result_some o.
Proof. 
    introv E. 
    unfold assert_get_object in E.
    lets (ptr&Hptr&Cptr): assert_get_object_ptr_out E.
    lets (obj&Hobj&Cobj): assert_get_object_from_ptr_out Cptr.
    jauto.
Qed.

Lemma assert_some_out : forall A opt cont (o : option A),
    assert_some opt cont = result_some o ->
    exists (a : A), opt = Some a /\ cont a = result_some o.
Proof. 
    introv E.
    destruct* opt; tryfalse.
Qed.

Lemma assert_deref_out : forall st loc cont o,
    assert_deref st loc cont = result_some o ->
    exists v, get_value st loc = Some v /\ cont v = result_some o.
Proof.
    introv E. unfold assert_deref in E.
    destruct* (get_value st loc); tryfalse.
Qed.
