Set Implicit Arguments.
Require Import Syntax.
Require Import Context.
Require Import Values.

Inductive ext_expr :=
| expr_basic : expr -> ext_expr
| expr_set_bang_1 : id -> out -> ext_expr
| expr_op1_1 : unary_op -> out -> ext_expr
| expr_op2_1 : binary_op -> out -> expr -> ext_expr
| expr_op2_2 : binary_op -> value -> out -> ext_expr 
| expr_if_1 : out -> expr -> expr -> ext_expr
(* app *)
| expr_seq_1 : out -> expr -> ext_expr
| expr_let_1 : id -> out -> expr -> ext_expr
| expr_recc_1 : value_loc -> out -> expr -> ext_expr
| expr_label_1 : id -> out -> ext_expr
| expr_break_1 : id -> out -> ext_expr
| expr_try_catch_1 : out -> expr -> ext_expr
| expr_try_finally_1 : out -> expr -> ext_expr
| expr_try_finally_2 : res -> out -> ext_expr
| expr_throw_1 : out -> ext_expr
(* lambda *)
(* eval *)
.

Coercion expr_basic : expr >-> ext_expr.

Inductive res_is_value : res -> Prop :=
| res_is_value_value : forall v, res_is_value (res_value v)
.

Inductive res_is_control : res -> Prop :=
| res_is_control_exception : forall v, res_is_control (res_exception v)
| res_is_control_break : forall i v, res_is_control (res_break i v)
.

Inductive abort : out -> Prop :=
| abort_div : abort out_div
| abort_control : forall st r, res_is_control r -> abort (out_ter st r)
.