Require Import Syntax.
Require Import PrettyInterm.
Require Import Store.
Require Import Context.
Require Import Values.
Require Import Operators.
Require Import Coq.Strings.String.

Require Import List.
Import ListNotations.

Open Scope list_scope.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type loc : value_loc.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.

Inductive red_expr : ctx -> store -> ext_expr -> out -> Prop :=
| red_expr_null : forall c st, red_expr c st expr_null (out_ter st (res_value value_null))
| red_expr_undefined : forall c st, red_expr c st expr_undefined (out_ter st (res_value value_null))
| red_expr_string : forall c st s, red_expr c st (expr_string s) (out_ter st (res_value (value_string s)))
| red_expr_number : forall c st n, red_expr c st (expr_number n) (out_ter st (res_value (value_number n)))
| red_expr_true : forall c st, red_expr c st expr_true (out_ter st (res_value value_true))
| red_expr_false : forall c st, red_expr c st expr_false (out_ter st (res_value value_false))
| red_expr_id : forall c st i loc v, 
    get_loc c i = Some loc -> 
    get_value st loc = Some v -> 
    red_expr c st (expr_id i) (out_ter st (res_value v))
| red_expr_lambda : forall c st st' args body v,
    (st', v) = add_closure c st args body ->
    red_expr c st (expr_lambda args body) (out_ter st' (res_value v))

(* object *)

| red_expr_set_bang : forall c st i e o o',
    red_expr c st e o ->
    red_expr c st (expr_set_bang_1 i o) o' ->
    red_expr c st (expr_set_bang i e) o'
| red_expr_set_bang_1 : forall c st' st st1 i loc v,
    st1 = add_value_at_location st loc v ->
    get_loc c i = Some loc -> 
    red_expr c st' (expr_set_bang_1 i (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_expr_set_bang_1_abort : forall c st i o,
    abort o ->
    red_expr c st (expr_set_bang_1 i o) o

| red_expr_op1 : forall c st e op o o',
    red_expr c st e o ->
    red_expr c st (expr_op1_1 op o) o' ->
    red_expr c st (expr_op1 op e) o'
| red_expr_op1_1 : forall c st' st op v v',
    unary op st v = result_some v' ->
    red_expr c st' (expr_op1_1 op (out_ter st (res_value v))) (out_ter st (res_value v'))
| red_expr_op1_1_abort : forall c st op o,
    abort o ->
    red_expr c st (expr_op1_1 op o) o

| red_expr_op2 : forall c st e1 e2 op o o',
    red_expr c st e1 o ->
    red_expr c st (expr_op2_1 op o e2) o' ->
    red_expr c st (expr_op2 op e1 e2) o'
| red_expr_op2_1 : forall c st' st e2 op v o o',
    red_expr c st e2 o ->
    red_expr c st (expr_op2_2 op v o) o' ->
    red_expr c st' (expr_op2_1 op (out_ter st (res_value v)) e2) o'
| red_expr_op2_1_abort : forall c st op e2 o,
    abort o ->
    red_expr c st (expr_op2_1 op o e2) o
| red_expr_op2_2 : forall c st' st op v1 v2 v,
    binary op st v1 v2 = result_some v ->
    red_expr c st' (expr_op2_2 op v1 (out_ter st (res_value v2))) (out_ter st (res_value v))
| red_expr_op2_2_abort : forall c st op v o,
    abort o ->
    red_expr c st (expr_op2_2 op v o) o

| red_expr_if : forall c st e e1 e2 o o',
    red_expr c st e o ->
    red_expr c st (expr_if_1 o e1 e2) o' ->
    red_expr c st (expr_if e e1 e2) o'
| red_expr_if_1_true : forall c st' st e1 e2 o,
    red_expr c st e1 o ->
    red_expr c st' (expr_if_1 (out_ter st (res_value value_true)) e1 e2) o
| red_expr_if_1_false : forall c st' st e1 e2 o,
    red_expr c st e2 o ->
    red_expr c st' (expr_if_1 (out_ter st (res_value value_false)) e1 e2) o (* TODO: not-true-is-false? *)
| red_expr_if_1_abort : forall c st e1 e2 o,
    abort o ->
    red_expr c st (expr_if_1 o e1 e2) o

(* app *)
| red_expr_app : forall c st e el o o',
    red_expr c st e o ->
    red_expr c st (expr_app_1 o el) o' ->
    red_expr c st (expr_app e el) o'
| red_expr_app_1 : forall c st' st v el o,
    red_expr c st (expr_app_2 v nil el) o ->
    red_expr c st' (expr_app_1 (out_ter st (res_value v)) el) o
| red_expr_app_1_abort : forall c st o el,
    abort o ->
    red_expr c st (expr_app_1 o el) o
| red_expr_app_2_next : forall c st v vl e el o o',
    red_expr c st e o ->
    red_expr c st (expr_app_3 v vl o el) o' ->
    red_expr c st (expr_app_2 v vl (e :: el)) o'
(* TODO actual application *)
| red_expr_app_3 : forall c st' st v vl v' el o,
    red_expr c st (expr_app_2 v (v' :: vl) el) o ->
    red_expr c st' (expr_app_3 v vl (out_ter st (res_value v)) el) o
| red_expr_app_3_abort : forall c st v vl el o,
    abort o ->
    red_expr c st (expr_app_3 v vl o el) o

| red_expr_seq : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_seq_1 o e2) o' ->
    red_expr c st (expr_seq e1 e2) o'
| red_expr_seq_1 : forall c st' st v e2 o,
    red_expr c st e2 o ->
    red_expr c st' (expr_seq_1 (out_ter st (res_value v)) e2) o
| red_expr_seq_1_abort : forall c st e2 o,
    abort o ->
    red_expr c st (expr_seq_1 o e2) o

| red_expr_let : forall c st i e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_let_1 i o e2) o' ->
    red_expr c st (expr_let i e1 e2) o'
| red_expr_let_1 : forall c c1 st' st st1 i v e2 o,
    (c1, st1) = add_named_value c st i v ->
    red_expr c1 st1 e2 o ->
    red_expr c st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_expr_let_1_abort : forall c st i o e2,
    abort o ->
    red_expr c st (expr_let_1 i o e2) o

| red_expr_recc : forall c c1 st st1 loc i e1 e2 o o',
    (c1, st1, loc) = add_named_value_loc c st i value_undefined ->
    red_expr c1 st1 e1 o ->
    red_expr c1 st1 (expr_recc_1 loc o e2) o' ->
    red_expr c st (expr_recc i e1 e2) o'
| red_expr_recc_1 : forall c st' st st1 loc v e2 o,
    st1 = add_value_at_location st loc v ->
    red_expr c st1 e2 o ->
    red_expr c st' (expr_recc_1 loc (out_ter st (res_value v)) e2) o
| red_expr_recc_1_abort : forall c st loc o e2,
    abort o ->
    red_expr c st (expr_recc_1 loc o e2) o

| red_expr_label : forall c st i e o o',
    red_expr c st e o ->
    red_expr c st (expr_label_1 i o) o' ->
    red_expr c st (expr_label i e) o'
| red_expr_label_1 : forall c st' st i r,
    (forall v, r <> res_break i v) ->
    red_expr c st' (expr_label_1 i (out_ter st r)) (out_ter st r)
| red_expr_label_1_break : forall c st' st i v,
    red_expr c st' (expr_label_1 i (out_ter st (res_break i v))) (out_ter st (res_value v))

| red_expr_break : forall c st i e o o',
    red_expr c st e o ->
    red_expr c st (expr_break_1 i o) o' ->
    red_expr c st (expr_break i e) o'
| red_expr_break_1 : forall c st' st i v,
    red_expr c st' (expr_break_1 i (out_ter st (res_value v))) (out_ter st (res_break i v))
| red_expr_break_1_abort : forall c st i o,
    abort o ->
    red_expr c st (expr_break_1 i o) o

| red_try_catch : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_try_catch_1 o e2) o' ->
    red_expr c st (expr_try_catch e1 e2) o'
| red_try_catch_1 : forall c st e2 o,
    (forall c st v, o <> out_ter st (res_exception v)) -> (* TODO something better? *)
    red_expr c st (expr_try_catch_1 o e2) o
| red_try_catch_1_exc : forall c st' st v e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_try_catch_2 v o) o' ->
    red_expr c st' (expr_try_catch_1 (out_ter st (res_exception v)) e2) o'
| red_try_catch_2 : forall c st' st v v' o,
    red_expr c st (expr_app_2 v' [v] nil) o ->
    red_expr c st' (expr_try_catch_2 v (out_ter st (res_value v'))) o
| red_try_catch_2_abort : forall c st v o,
    abort o ->
    red_expr c st (expr_try_catch_2 v o) o

| red_try_finally : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_try_finally_1 o e2) o' ->
    red_expr c st (expr_try_finally e1 e2) o'
| red_try_finally_1 : forall c st' st r e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_try_finally_2 r o) o' ->
    red_expr c st' (expr_try_finally_1 (out_ter st r) e2) o'
| red_try_finally_1_div : forall c st e2,
    red_expr c st (expr_try_finally_1 out_div e2) out_div
| red_try_finally_2_value : forall c st r o,
    res_is_value r ->
    red_expr c st (expr_try_finally_2 r o) o
| red_try_finally_2_control : forall c st' st r v o,
    res_is_control r ->
    red_expr c st' (expr_try_finally_2 r (out_ter st (res_value v))) (out_ter st r)
| red_try_finally_2_abort : forall c st r o,
    abort o ->
    red_expr c st (expr_try_finally_2 r o) o

| red_expr_throw : forall c st e o o',
    red_expr c st e o ->
    red_expr c st (expr_throw_1 o) o' ->
    red_expr c st (expr_throw e) o'
| red_expr_throw_1 : forall c st' st v,
    red_expr c st' (expr_throw_1 (out_ter st (res_value v))) (out_ter st (res_exception v))
| red_expr_throw_1_abort : forall c st o,
    abort o ->
    red_expr c st (expr_throw_1 o) o
.

