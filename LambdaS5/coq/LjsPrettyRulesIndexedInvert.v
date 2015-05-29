Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax. 
Require Import LjsPrettyInterm.
Require Import LjsPrettyRulesIndexed.
Ltac red_exprh_hnf e := 
    match eval hnf in e with
    | expr_basic ?e1 =>
        let e1' := eval hnf in e1 in
        constr:(expr_basic e1')
    | ?e1 => constr:e1
    end.
Derive Inversion inv_red_exprh_empty with (forall k c st oo,
    red_exprh k c st (expr_empty) oo) Sort Prop.
Derive Inversion inv_red_exprh_null with (forall k c st oo,
    red_exprh k c st (expr_null) oo) Sort Prop.
Derive Inversion inv_red_exprh_undefined with (forall k c st oo,
    red_exprh k c st (expr_undefined) oo) Sort Prop.
Derive Inversion inv_red_exprh_string with (forall k c st s oo,
    red_exprh k c st (expr_string s) oo) Sort Prop.
Derive Inversion inv_red_exprh_bool with (forall k c st b oo,
    red_exprh k c st (expr_bool b) oo) Sort Prop.
Derive Inversion inv_red_exprh_number with (forall k c st n oo,
    red_exprh k c st (expr_number n) oo) Sort Prop.
Derive Inversion inv_red_exprh_id with (forall k c st i oo,
    red_exprh k c st (expr_id i) oo) Sort Prop.
Derive Inversion inv_red_exprh_lambda with (forall k c st args body oo,
    red_exprh k c st (expr_lambda args body) oo) Sort Prop.
Derive Inversion inv_red_exprh_many_1 with (forall k c st es vs E oo,
    red_exprh k c st (expr_eval_many_1 es vs E) oo) Sort Prop.
Derive Inversion inv_red_exprh_many_2 with (forall k c st es o vs E oo,
    red_exprh k c st (expr_eval_many_2 es o vs E) oo) Sort Prop.
Derive Inversion inv_red_exprh_object with (forall k c st oa ia a oo,
    red_exprh k c st (expr_object oa ia a) oo) Sort Prop.
Derive Inversion inv_red_exprh_object_1 with (forall k c st a ia oal oo,
    red_exprh k c st (expr_object_1 a ia oal) oo) Sort Prop.
Derive Inversion inv_red_exprh_object_2 with (forall k c st a ia obj oo,
    red_exprh k c st (expr_object_2 a ia obj) oo) Sort Prop.
Derive Inversion inv_red_exprh_object_data_1 with (forall k c st obj s E vs oo,
    red_exprh k c st (expr_object_data_1 obj s E vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_object_accessor_1 with (forall k c st obj s E vs oo,
    red_exprh k c st (expr_object_accessor_1 obj s E vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_object_internal_1 with (forall k c st obj s E vs oo,
    red_exprh k c st (expr_object_internal_1 obj s E vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_attr with (forall k c st pa e1 e2 oo,
    red_exprh k c st (expr_get_attr pa e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_attr_1 with (forall k c st pa vs oo,
    red_exprh k c st (expr_get_attr_1 pa vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_attr with (forall k c st pa e1 e2 e3 oo,
    red_exprh k c st (expr_set_attr pa e1 e2 e3) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_attr_1 with (forall k c st pa vs oo,
    red_exprh k c st (expr_set_attr_1 pa vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_obj_attr with (forall k c st pa e1 oo,
    red_exprh k c st (expr_get_obj_attr pa e1) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_obj_attr_1 with (forall k c st pa vs oo,
    red_exprh k c st (expr_get_obj_attr_1 pa vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_obj_attr with (forall k c st pa e1 e2 oo,
    red_exprh k c st (expr_set_obj_attr pa e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_obj_attr_1 with (forall k c st pa vs oo,
    red_exprh k c st (expr_set_obj_attr_1 pa vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_internal with (forall k c st s e1 oo,
    red_exprh k c st (expr_get_internal s e1) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_internal_1 with (forall k c st s vs oo,
    red_exprh k c st (expr_get_internal_1 s vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_internal with (forall k c st s e1 e2 oo,
    red_exprh k c st (expr_set_internal s e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_internal_1 with (forall k c st s vs oo,
    red_exprh k c st (expr_set_internal_1 s vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_field with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_get_field e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_field_1 with (forall k c st vs oo,
    red_exprh k c st (expr_get_field_1 vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_get_field_2 with (forall k c st ptr oattr oo,
    red_exprh k c st (expr_get_field_2 ptr oattr) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_field with (forall k c st e1 e2 e3 oo,
    red_exprh k c st (expr_set_field e1 e2 e3) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_field_1 with (forall k c st vs oo,
    red_exprh k c st (expr_set_field_1 vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_set_field_2 with (forall k c st ptr obj oattr s v3 oo,
    red_exprh k c st (expr_set_field_2 ptr obj oattr s v3) oo) Sort Prop.
Derive Inversion inv_red_exprh_delete_field with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_delete_field e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_delete_field_1 with (forall k c st vs oo,
    red_exprh k c st (expr_delete_field_1 vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_delete_field_2 with (forall k c st ptr obj oattr s oo,
    red_exprh k c st (expr_delete_field_2 ptr obj oattr s) oo) Sort Prop.
Derive Inversion inv_red_exprh_own_field_names with (forall k c st e oo,
    red_exprh k c st (expr_own_field_names e) oo) Sort Prop.
Derive Inversion inv_red_exprh_own_field_names_1 with (forall k c st o oo,
    red_exprh k c st (expr_own_field_names_1 o) oo) Sort Prop.
Derive Inversion inv_red_exprh_op1 with (forall k c st op e oo,
    red_exprh k c st (expr_op1 op e) oo) Sort Prop.
Derive Inversion inv_red_exprh_op1_1 with (forall k c st op o oo,
    red_exprh k c st (expr_op1_1 op o) oo) Sort Prop.
Derive Inversion inv_red_exprh_op2 with (forall k c st op e1 e2 oo,
    red_exprh k c st (expr_op2 op e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_op2_1 with (forall k c st op o e2 oo,
    red_exprh k c st (expr_op2_1 op o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_op2_2 with (forall k c st op v1 o oo,
    red_exprh k c st (expr_op2_2 op v1 o) oo) Sort Prop.
Derive Inversion inv_red_exprh_if with (forall k c st e e1 e2 oo,
    red_exprh k c st (expr_if e e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_if_1 with (forall k c st o e1 e2 oo,
    red_exprh k c st (expr_if_1 o e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_app with (forall k c st e el oo,
    red_exprh k c st (expr_app e el) oo) Sort Prop.
Derive Inversion inv_red_exprh_app_1 with (forall k c st o el oo,
    red_exprh k c st (expr_app_1 o el) oo) Sort Prop.
Derive Inversion inv_red_exprh_app_2 with (forall k c st v vl oo,
    red_exprh k c st (expr_app_2 v vl) oo) Sort Prop.
Derive Inversion inv_red_exprh_seq with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_seq e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_seq_1 with (forall k c st o e2 oo,
    red_exprh k c st (expr_seq_1 o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_jseq with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_jseq e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_jseq_1 with (forall k c st o e2 oo,
    red_exprh k c st (expr_jseq_1 o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_jseq_2 with (forall k c st v1 o oo,
    red_exprh k c st (expr_jseq_2 v1 o) oo) Sort Prop.
Derive Inversion inv_red_exprh_let with (forall k c st i e1 e2 oo,
    red_exprh k c st (expr_let i e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_let_1 with (forall k c st i o e2 oo,
    red_exprh k c st (expr_let_1 i o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_rec with (forall k c st i e1 e2 oo,
    red_exprh k c st (expr_recc i e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_label with (forall k c st i e oo,
    red_exprh k c st (expr_label i e) oo) Sort Prop.
Derive Inversion inv_red_exprh_label_1 with (forall k c st i o oo,
    red_exprh k c st (expr_label_1 i o) oo) Sort Prop.
Derive Inversion inv_red_exprh_break with (forall k c st i e oo,
    red_exprh k c st (expr_break i e) oo) Sort Prop.
Derive Inversion inv_red_exprh_break_1 with (forall k c st i o oo,
    red_exprh k c st (expr_break_1 i o) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_catch with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_try_catch e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_catch_1 with (forall k c st o e2 oo,
    red_exprh k c st (expr_try_catch_1 o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_catch_2 with (forall k c st v1 o oo,
    red_exprh k c st (expr_try_catch_2 v1 o) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_finally with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_try_finally e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_finally_1 with (forall k c st o e2 oo,
    red_exprh k c st (expr_try_finally_1 o e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_try_finally_2 with (forall k c st r' o oo,
    red_exprh k c st (expr_try_finally_2 r' o) oo) Sort Prop.
Derive Inversion inv_red_exprh_throw with (forall k c st e oo,
    red_exprh k c st (expr_throw e) oo) Sort Prop.
Derive Inversion inv_red_exprh_throw_1 with (forall k c st o oo,
    red_exprh k c st (expr_throw_1 o) oo) Sort Prop.
Derive Inversion inv_red_exprh_eval with (forall k c st e1 e2 oo,
    red_exprh k c st (expr_eval e1 e2) oo) Sort Prop.
Derive Inversion inv_red_exprh_eval_1 with (forall k c st vs oo,
    red_exprh k c st (expr_eval_1 vs) oo) Sort Prop.
Derive Inversion inv_red_exprh_hint with (forall k c st s e oo,
    red_exprh k c st (expr_hint s e) oo) Sort Prop.
Derive Inversion inv_red_exprh_fail with (forall k c st s oo,
    red_exprh k c st (expr_fail s) oo) Sort Prop.
Derive Inversion inv_red_exprh_dump with (forall k c st oo,
    red_exprh k c st (expr_dump) oo) Sort Prop.
Tactic Notation "invert" "keep" "red_exprh" hyp(H) := 
    match type of H with
    | red_exprh ?k ?c ?st (?e) ?oo => 
    let eh := red_exprh_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
    | expr_basic (expr_empty) =>
        inversion H using inv_red_exprh_empty
    | expr_basic (expr_null) =>
        inversion H using inv_red_exprh_null
    | expr_basic (expr_undefined) =>
        inversion H using inv_red_exprh_undefined
    | expr_basic (expr_string ?s) =>
        inversion H using inv_red_exprh_string
    | expr_basic (expr_bool ?b) =>
        inversion H using inv_red_exprh_bool
    | expr_basic (expr_number ?n) =>
        inversion H using inv_red_exprh_number
    | expr_basic (expr_id ?i) =>
        inversion H using inv_red_exprh_id
    | expr_basic (expr_lambda ?args ?body) =>
        inversion H using inv_red_exprh_lambda
    | expr_eval_many_1 ?es ?vs ?E =>
        inversion H using inv_red_exprh_many_1
    | expr_eval_many_2 ?es ?o ?vs ?E =>
        inversion H using inv_red_exprh_many_2
    | expr_basic (expr_object ?oa ?ia ?a) =>
        inversion H using inv_red_exprh_object
    | expr_object_1 ?a ?ia ?oal =>
        inversion H using inv_red_exprh_object_1
    | expr_object_2 ?a ?ia ?obj =>
        inversion H using inv_red_exprh_object_2
    | expr_object_data_1 ?obj ?s ?E ?vs =>
        inversion H using inv_red_exprh_object_data_1
    | expr_object_accessor_1 ?obj ?s ?E ?vs =>
        inversion H using inv_red_exprh_object_accessor_1
    | expr_object_internal_1 ?obj ?s ?E ?vs =>
        inversion H using inv_red_exprh_object_internal_1
    | expr_basic (expr_get_attr ?pa ?e1 ?e2) =>
        inversion H using inv_red_exprh_get_attr
    | expr_get_attr_1 ?pa ?vs =>
        inversion H using inv_red_exprh_get_attr_1
    | expr_basic (expr_set_attr ?pa ?e1 ?e2 ?e3) =>
        inversion H using inv_red_exprh_set_attr
    | expr_set_attr_1 ?pa ?vs =>
        inversion H using inv_red_exprh_set_attr_1
    | expr_basic (expr_get_obj_attr ?pa ?e1) =>
        inversion H using inv_red_exprh_get_obj_attr
    | expr_get_obj_attr_1 ?pa ?vs =>
        inversion H using inv_red_exprh_get_obj_attr_1
    | expr_basic (expr_set_obj_attr ?pa ?e1 ?e2) =>
        inversion H using inv_red_exprh_set_obj_attr
    | expr_set_obj_attr_1 ?pa ?vs =>
        inversion H using inv_red_exprh_set_obj_attr_1
    | expr_basic (expr_get_internal ?s ?e1) =>
        inversion H using inv_red_exprh_get_internal
    | expr_get_internal_1 ?s ?vs =>
        inversion H using inv_red_exprh_get_internal_1
    | expr_basic (expr_set_internal ?s ?e1 ?e2) =>
        inversion H using inv_red_exprh_set_internal
    | expr_set_internal_1 ?s ?vs =>
        inversion H using inv_red_exprh_set_internal_1
    | expr_basic (expr_get_field ?e1 ?e2) =>
        inversion H using inv_red_exprh_get_field
    | expr_get_field_1 ?vs =>
        inversion H using inv_red_exprh_get_field_1
    | expr_get_field_2 ?ptr ?oattr =>
        inversion H using inv_red_exprh_get_field_2
    | expr_basic (expr_set_field ?e1 ?e2 ?e3) =>
        inversion H using inv_red_exprh_set_field
    | expr_set_field_1 ?vs =>
        inversion H using inv_red_exprh_set_field_1
    | expr_set_field_2 ?ptr ?obj ?oattr ?s ?v3 =>
        inversion H using inv_red_exprh_set_field_2
    | expr_basic (expr_delete_field ?e1 ?e2) =>
        inversion H using inv_red_exprh_delete_field
    | expr_delete_field_1 ?vs =>
        inversion H using inv_red_exprh_delete_field_1
    | expr_delete_field_2 ?ptr ?obj ?oattr ?s =>
        inversion H using inv_red_exprh_delete_field_2
    | expr_basic (expr_own_field_names ?e) =>
        inversion H using inv_red_exprh_own_field_names
    | expr_own_field_names_1 ?o =>
        inversion H using inv_red_exprh_own_field_names_1
    | expr_basic (expr_op1 ?op ?e) =>
        inversion H using inv_red_exprh_op1
    | expr_op1_1 ?op ?o =>
        inversion H using inv_red_exprh_op1_1
    | expr_basic (expr_op2 ?op ?e1 ?e2) =>
        inversion H using inv_red_exprh_op2
    | expr_op2_1 ?op ?o ?e2 =>
        inversion H using inv_red_exprh_op2_1
    | expr_op2_2 ?op ?v1 ?o =>
        inversion H using inv_red_exprh_op2_2
    | expr_basic (expr_if ?e ?e1 ?e2) =>
        inversion H using inv_red_exprh_if
    | expr_if_1 ?o ?e1 ?e2 =>
        inversion H using inv_red_exprh_if_1
    | expr_basic (expr_app ?e ?el) =>
        inversion H using inv_red_exprh_app
    | expr_app_1 ?o ?el =>
        inversion H using inv_red_exprh_app_1
    | expr_app_2 ?v ?vl =>
        inversion H using inv_red_exprh_app_2
    | expr_basic (expr_seq ?e1 ?e2) =>
        inversion H using inv_red_exprh_seq
    | expr_seq_1 ?o ?e2 =>
        inversion H using inv_red_exprh_seq_1
    | expr_basic (expr_jseq ?e1 ?e2) =>
        inversion H using inv_red_exprh_jseq
    | expr_jseq_1 ?o ?e2 =>
        inversion H using inv_red_exprh_jseq_1
    | expr_jseq_2 ?v1 ?o =>
        inversion H using inv_red_exprh_jseq_2
    | expr_basic (expr_let ?i ?e1 ?e2) =>
        inversion H using inv_red_exprh_let
    | expr_let_1 ?i ?o ?e2 =>
        inversion H using inv_red_exprh_let_1
    | expr_basic (expr_recc ?i ?e1 ?e2) =>
        inversion H using inv_red_exprh_rec
    | expr_basic (expr_label ?i ?e) =>
        inversion H using inv_red_exprh_label
    | expr_label_1 ?i ?o =>
        inversion H using inv_red_exprh_label_1
    | expr_basic (expr_break ?i ?e) =>
        inversion H using inv_red_exprh_break
    | expr_break_1 ?i ?o =>
        inversion H using inv_red_exprh_break_1
    | expr_basic (expr_try_catch ?e1 ?e2) =>
        inversion H using inv_red_exprh_try_catch
    | expr_try_catch_1 ?o ?e2 =>
        inversion H using inv_red_exprh_try_catch_1
    | expr_try_catch_2 ?v1 ?o =>
        inversion H using inv_red_exprh_try_catch_2
    | expr_basic (expr_try_finally ?e1 ?e2) =>
        inversion H using inv_red_exprh_try_finally
    | expr_try_finally_1 ?o ?e2 =>
        inversion H using inv_red_exprh_try_finally_1
    | expr_try_finally_2 ?r' ?o =>
        inversion H using inv_red_exprh_try_finally_2
    | expr_basic (expr_throw ?e) =>
        inversion H using inv_red_exprh_throw
    | expr_throw_1 ?o =>
        inversion H using inv_red_exprh_throw_1
    | expr_basic (expr_eval ?e1 ?e2) =>
        inversion H using inv_red_exprh_eval
    | expr_eval_1 ?vs =>
        inversion H using inv_red_exprh_eval_1
    | expr_basic (expr_hint ?s ?e) =>
        inversion H using inv_red_exprh_hint
    | expr_basic (expr_fail ?s) =>
        inversion H using inv_red_exprh_fail
    | expr_basic (expr_dump) =>
        inversion H using inv_red_exprh_dump
    end end; tryfalse; clear H; intro H.
Tactic Notation "inverts" "keep" "red_exprh" hyp(H) := 
    inverts_tactic_general ltac:(fun H => invert keep red_exprh H) H; tryfalse.
Tactic Notation "inverts" "red_exprh" hyp(H) := 
    inverts keep red_exprh H; clear H.
