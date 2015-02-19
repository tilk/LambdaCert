Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesIndexed.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import JsNumber.
Require Import Coq.Strings.String.
Import List.ListNotations.

Open Scope list_scope.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Local Hint Constructors red_expr red_exprh.

Lemma red_expr_forget_h : forall k c st e o, red_exprh k c st e o -> red_expr c st e o.
Proof.
    introv H. induction* H.
Qed.

Local Hint Extern 1 ((_ < _)%nat) => omega.

Lemma red_exprh_lt : forall k k' c st ee o, 
    red_exprh k c st ee o -> (k < k')%nat -> red_exprh k' c st ee o.
Proof.
    introv H. gen k'. induction H; introv L; (destruct k' as [|k']; [false; omega | auto*]).
Qed.

Lemma red_expr_add_h : forall c st e o, red_expr c st e o -> exists k, red_exprh k c st e o.
Proof.
    hint red_exprh_lt. introv H. induction H; induct_height. 
Qed.

