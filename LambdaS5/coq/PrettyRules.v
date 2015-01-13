Require Import Syntax.
Require Import PrettyInterm.
Require Import Store.
Require Import Context.
Require Import Values.
Require Import Operators.
Require Import Coq.Strings.String.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type loc : value_loc.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.

Inductive red_expr : store -> ext_expr -> out -> Prop :=
| red_expr_null : forall st, red_expr st expr_null (out_ter st (res_value value_null))
| red_expr_undefined : forall st, red_expr st expr_undefined (out_ter st (res_value value_null))
| red_expr_string : forall st s, red_expr st (expr_string s) (out_ter st (res_value (value_string s)))
| red_expr_number : forall st n, red_expr st (expr_number n) (out_ter st (res_value (value_number n)))
| red_expr_true : forall st, red_expr st expr_true (out_ter st (res_value value_true))
| red_expr_false : forall st, red_expr st expr_false (out_ter st (res_value value_false))
| red_expr_id : forall st i loc v, 
    get_loc st i = Some loc -> 
    get_value st loc = Some v -> 
    red_expr st (expr_id i) (out_ter st (res_value v))

(* object *)

| red_expr_set_bang : forall st i e o o',
    red_expr st e o ->
    red_expr st (expr_set_bang_1 i o) o' ->
    red_expr st (expr_set_bang i e) o'
| red_expr_set_bang_1 : forall st' st st1 i loc v,
    st1 = add_value_at_location st loc v ->
    get_loc st i = Some loc -> 
    red_expr st' (expr_set_bang_1 i (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_expr_set_bang_1_abort : forall st i o,
    abort o ->
    red_expr st (expr_set_bang_1 i o) o

| red_expr_op1 : forall st e op o o',
    red_expr st e o ->
    red_expr st (expr_op1_1 op o) o' ->
    red_expr st (expr_op1 op e) o'
| red_expr_op1_1 : forall st' st op v v',
    unary op st v = result_some v' ->
    red_expr st' (expr_op1_1 op (out_ter st (res_value v))) (out_ter st (res_value v'))
| red_expr_op1_1_abort : forall st op o,
    abort o ->
    red_expr st (expr_op1_1 op o) o

| red_expr_op2 : forall st e1 e2 op o o',
    red_expr st e1 o ->
    red_expr st (expr_op2_1 op o e2) o' ->
    red_expr st (expr_op2 op e1 e2) o'
| red_expr_op2_1 : forall st' st e2 op v o o',
    red_expr st e2 o ->
    red_expr st (expr_op2_2 op v o) o' ->
    red_expr st' (expr_op2_1 op (out_ter st (res_value v)) e2) o'
| red_expr_op2_1_abort : forall st op e2 o,
    abort o ->
    red_expr st (expr_op2_1 op o e2) o
| red_expr_op2_2 : forall st' st op v1 v2 v,
    binary op st v1 v2 = result_some v ->
    red_expr st' (expr_op2_2 op v1 (out_ter st (res_value v2))) (out_ter st (res_value v))
| red_expr_op2_2_abort : forall st op v o,
    abort o ->
    red_expr st (expr_op2_2 op v o) o

| red_expr_if : forall st e e1 e2 o o',
    red_expr st e o ->
    red_expr st (expr_if_1 o e1 e2) o' ->
    red_expr st (expr_if e e1 e2) o'
| red_expr_if_1_true : forall st' st e1 e2 o,
    red_expr st e1 o ->
    red_expr st' (expr_if_1 (out_ter st (res_value value_true)) e1 e2) o
| red_expr_if_1_false : forall st' st e1 e2 o,
    red_expr st e2 o ->
    red_expr st' (expr_if_1 (out_ter st (res_value value_false)) e1 e2) o (* TODO: not-true-is-false? *)
| red_expr_if_1_abort : forall st e1 e2 o,
    abort o ->
    red_expr st (expr_if_1 o e1 e2) o

(* app *)

| red_expr_seq : forall st e1 e2 o o',
    red_expr st e1 o ->
    red_expr st (expr_seq_1 o e2) o' ->
    red_expr st (expr_seq e1 e2) o'
| red_expr_seq_1 : forall st' st v e2 o,
    red_expr st e2 o ->
    red_expr st' (expr_seq_1 (out_ter st (res_value v)) e2) o
| red_expr_seq_1_abort : forall st e2 o,
    abort o ->
    red_expr st (expr_seq_1 o e2) o

| red_expr_let : forall st i e1 e2 o o',
    red_expr st e1 o ->
    red_expr st (expr_let_1 i o e2) o' ->
    red_expr st (expr_let i e1 e2) o'
| red_expr_let_1 : forall st' st st1 i v e2 o,
    st1 = add_named_value st i v ->
    red_expr st1 e2 o ->
    red_expr st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_expr_let_1_abort : forall st i o e2,
    abort o ->
    red_expr st (expr_let_1 i o e2) o

| red_expr_recc : forall st st1 loc i e1 e2 o o',
    (st1, loc) = add_named_value_loc st i value_undefined ->
    red_expr st1 e1 o ->
    red_expr st1 (expr_recc_1 loc o e2) o' ->
    red_expr st (expr_recc i e1 e2) o'
| red_expr_recc_1 : forall st' st st1 loc v e2 o,
    st1 = add_value_at_location st loc v ->
    red_expr st1 e2 o ->
    red_expr st' (expr_recc_1 loc (out_ter st (res_value v)) e2) o
| red_expr_recc_1_abort : forall st loc o e2,
    abort o ->
    red_expr st (expr_recc_1 loc o e2) o

| red_expr_label : forall st i e o o',
    red_expr st e o ->
    red_expr st (expr_label_1 i o) o' ->
    red_expr st (expr_label i e) o'
| red_expr_label_1 : forall st' st i r,
    (forall v, r <> res_break i v) ->
    red_expr st' (expr_label_1 i (out_ter st r)) (out_ter st r)
| red_expr_label_1_break : forall st' st i v,
    red_expr st' (expr_label_1 i (out_ter st (res_break i v))) (out_ter st (res_value v))

| red_expr_break : forall st i e o o',
    red_expr st e o ->
    red_expr st (expr_break_1 i o) o' ->
    red_expr st (expr_break i e) o'
| red_expr_break_1 : forall st' st i v,
    red_expr st' (expr_break_1 i (out_ter st (res_value v))) (out_ter st (res_break i v))
| red_expr_break_1_abort : forall st i o,
    abort o ->
    red_expr st (expr_break_1 i o) o

(* try_catch *)

| red_try_finally : forall st e1 e2 o o',
    red_expr st e1 o ->
    red_expr st (expr_try_finally_1 o e2) o' ->
    red_expr st (expr_try_finally e1 e2) o'
| red_try_finally_1 : forall st' st r e2 o o',
    red_expr st e2 o ->
    red_expr st (expr_try_finally_2 r o) o' ->
    red_expr st' (expr_try_finally_1 (out_ter st r) e2) o'
| red_try_finally_1_div : forall st e2,
    red_expr st (expr_try_finally_1 out_div e2) out_div
| red_try_finally_2_value : forall st r o,
    res_is_value r ->
    red_expr st (expr_try_finally_2 r o) o
| red_try_finally_2_control : forall st' st r v o,
    res_is_control r ->
    red_expr st' (expr_try_finally_2 r (out_ter st (res_value v))) (out_ter st r)
| red_try_finally_2_abort : forall st r o,
    abort o ->
    red_expr st (expr_try_finally_2 r o) o

| red_expr_throw : forall st e o o',
    red_expr st e o ->
    red_expr st (expr_throw_1 o) o' ->
    red_expr st (expr_throw e) o'
| red_expr_throw_1 : forall st' st v,
    red_expr st' (expr_throw_1 (out_ter st (res_value v))) (out_ter st (res_exception v))
| red_expr_throw_1_abort : forall st o,
    abort o ->
    red_expr st (expr_throw_1 o) o
.

