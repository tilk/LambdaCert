Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax. 
Require Import LjsPrettyInterm.
Require Import LjsPrettyRulesIndexed.
Derive Inversion_clear inv_red_exprh_empty with (forall k c st st' r,
    red_exprh k c st (expr_empty) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_null with (forall k c st st' r,
    red_exprh k c st (expr_null) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_undefined with (forall k c st st' r,
    red_exprh k c st (expr_undefined) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_string with (forall k c st s st' r,
    red_exprh k c st (expr_string s) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_bool with (forall k c st b st' r,
    red_exprh k c st (expr_bool b) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_number with (forall k c st n st' r,
    red_exprh k c st (expr_number n) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_many_1 with (forall k c st es vs E st' r,
    red_exprh k c st (expr_eval_many_1 es vs E) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_many_2 with (forall k c st es o vs E st' r,
    red_exprh k c st (expr_eval_many_2 es o vs E) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_object with (forall k c st oa a st' r,
    red_exprh k c st (expr_object oa a) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_object_1 with (forall k c st a oal st' r,
    red_exprh k c st (expr_object_1 a oal) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_object_2 with (forall k c st obj a st' r,
    red_exprh k c st (expr_object_2 obj a) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_op1 with (forall k c st op e st' r,
    red_exprh k c st (expr_op1 op e) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_op1_1 with (forall k c st op o st' r,
    red_exprh k c st (expr_op1_1 op o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_op2 with (forall k c st op e1 e2 st' r,
    red_exprh k c st (expr_op2 op e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_op2_1 with (forall k c st op o e2 st' r,
    red_exprh k c st (expr_op2 op o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_op2_2 with (forall k c st op v1 o st' r,
    red_exprh k c st (expr_op2 op v1 o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_if with (forall k c st e e1 e2 st' r,
    red_exprh k c st (expr_if e e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_if_1 with (forall k c st o e1 e2 st' r,
    red_exprh k c st (expr_if_1 o e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_app with (forall k c st e el st' r,
    red_exprh k c st (expr_app e el) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_app_1 with (forall k c st o el st' r,
    red_exprh k c st (expr_app_1 o el) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_app_2 with (forall k c st v vl st' r,
    red_exprh k c st (expr_app_2 v vl) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_seq with (forall k c st e1 e2 st' r,
    red_exprh k c st (expr_seq e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_seq_1 with (forall k c st o e2 st' r,
    red_exprh k c st (expr_seq_1 o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_jseq with (forall k c st e1 e2 st' r,
    red_exprh k c st (expr_jseq e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_jseq_1 with (forall k c st o e2 st' r,
    red_exprh k c st (expr_jseq_1 o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_jseq_2 with (forall k c st v1 o st' r,
    red_exprh k c st (expr_jseq_2 v1 o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_let with (forall k c st i e1 e2 st' r,
    red_exprh k c st (expr_let i e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_let_1 with (forall k c st i o e2 st' r,
    red_exprh k c st (expr_let_1 i o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_rec with (forall k c st i e1 e2 st' r,
    red_exprh k c st (expr_recc i e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_label with (forall k c st i e st' r,
    red_exprh k c st (expr_label i e) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_label_1 with (forall k c st i o st' r,
    red_exprh k c st (expr_label_1 i o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_break with (forall k c st i e st' r,
    red_exprh k c st (expr_break i e) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_break_1 with (forall k c st i o st' r,
    red_exprh k c st (expr_break_1 i o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_catch with (forall k c st e1 e2 st' r,
    red_exprh k c st (expr_try_catch e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_catch_1 with (forall k c st o e2 st' r,
    red_exprh k c st (expr_try_catch_1 o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_catch_2 with (forall k c st v1 o st' r,
    red_exprh k c st (expr_try_catch_2 v1 o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_finally with (forall k c st e1 e2 st' r,
    red_exprh k c st (expr_try_finally e1 e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_finally_1 with (forall k c st o e2 st' r,
    red_exprh k c st (expr_try_finally_1 o e2) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_try_finally_2 with (forall k c st r' o st' r,
    red_exprh k c st (expr_try_finally_2 r' o) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_throw with (forall k c st e st' r,
    red_exprh k c st (expr_throw e) (out_ter st' r)) Sort Prop.
Derive Inversion_clear inv_red_exprh_throw_1 with (forall k c st o st' r,
    red_exprh k c st (expr_throw_1 o) (out_ter st' r)) Sort Prop.
Tactic Notation "invert" "keep" "red_exprh" hyp(H) := 
    match type of H with
    | red_exprh ?k ?c ?st (expr_basic (expr_empty)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_empty
    | red_exprh ?k ?c ?st (expr_basic (expr_null)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_null
    | red_exprh ?k ?c ?st (expr_basic (expr_undefined)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_undefined
    | red_exprh ?k ?c ?st (expr_basic (expr_string ?s)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_string
    | red_exprh ?k ?c ?st (expr_basic (expr_bool ?b)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_bool
    | red_exprh ?k ?c ?st (expr_basic (expr_number ?n)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_number
    | red_exprh ?k ?c ?st (expr_eval_many_1 ?es ?vs ?E) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_many_1
    | red_exprh ?k ?c ?st (expr_eval_many_2 ?es ?o ?vs ?E) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_many_2
    | red_exprh ?k ?c ?st (expr_basic (expr_object ?oa ?a)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_object
    | red_exprh ?k ?c ?st (expr_object_1 ?a ?oal) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_object_1
    | red_exprh ?k ?c ?st (expr_object_2 ?obj ?a) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_object_2
    | red_exprh ?k ?c ?st (expr_basic (expr_op1 ?op ?e)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_op1
    | red_exprh ?k ?c ?st (expr_op1_1 ?op ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_op1_1
    | red_exprh ?k ?c ?st (expr_basic (expr_op2 ?op ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_op2
    | red_exprh ?k ?c ?st (expr_basic (expr_op2 ?op ?o ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_op2_1
    | red_exprh ?k ?c ?st (expr_basic (expr_op2 ?op ?v1 ?o)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_op2_2
    | red_exprh ?k ?c ?st (expr_basic (expr_if ?e ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_if
    | red_exprh ?k ?c ?st (expr_if_1 ?o ?e1 ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_if_1
    | red_exprh ?k ?c ?st (expr_basic (expr_app ?e ?el)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_app
    | red_exprh ?k ?c ?st (expr_app_1 ?o ?el) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_app_1
    | red_exprh ?k ?c ?st (expr_app_2 ?v ?vl) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_app_2
    | red_exprh ?k ?c ?st (expr_basic (expr_seq ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_seq
    | red_exprh ?k ?c ?st (expr_seq_1 ?o ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_seq_1
    | red_exprh ?k ?c ?st (expr_basic (expr_jseq ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_jseq
    | red_exprh ?k ?c ?st (expr_jseq_1 ?o ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_jseq_1
    | red_exprh ?k ?c ?st (expr_jseq_2 ?v1 ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_jseq_2
    | red_exprh ?k ?c ?st (expr_basic (expr_let ?i ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_let
    | red_exprh ?k ?c ?st (expr_let_1 ?i ?o ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_let_1
    | red_exprh ?k ?c ?st (expr_basic (expr_recc ?i ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_rec
    | red_exprh ?k ?c ?st (expr_basic (expr_label ?i ?e)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_label
    | red_exprh ?k ?c ?st (expr_label_1 ?i ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_label_1
    | red_exprh ?k ?c ?st (expr_basic (expr_break ?i ?e)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_break
    | red_exprh ?k ?c ?st (expr_break_1 ?i ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_break_1
    | red_exprh ?k ?c ?st (expr_basic (expr_try_catch ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_catch
    | red_exprh ?k ?c ?st (expr_try_catch_1 ?o ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_catch_1
    | red_exprh ?k ?c ?st (expr_try_catch_2 ?v1 ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_catch_2
    | red_exprh ?k ?c ?st (expr_basic (expr_try_finally ?e1 ?e2)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_finally
    | red_exprh ?k ?c ?st (expr_try_finally_1 ?o ?e2) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_finally_1
    | red_exprh ?k ?c ?st (expr_try_finally_2 ?r' ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_try_finally_2
    | red_exprh ?k ?c ?st (expr_basic (expr_throw ?e)) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_throw
    | red_exprh ?k ?c ?st (expr_throw_1 ?o) (out_ter ?st' ?r) =>
        inversion H using inv_red_exprh_throw_1
    end.
Tactic Notation "inverts" "keep" "red_exprh" hyp(H) := 
    inverts_tactic_general ltac:(fun H => invert keep red_exprh H) H.
Tactic Notation "inverts" "red_exprh" hyp(H) := 
    inverts keep red_exprh H; clear H.
