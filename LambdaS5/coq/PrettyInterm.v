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
(* let *)
(* recc *)
| expr_label_1 : id -> out -> ext_expr
| expr_break_1 : id -> out -> ext_expr
(* try_catch *)
(* try_finally *)
| expr_throw_1 : out -> ext_expr
.

Coercion expr_basic : expr >-> ext_expr.

Inductive res_control : res -> Prop :=
| res_control_exception : forall v, res_control (res_exception v)
| res_control_break : forall i v, res_control (res_break i v)
.

Inductive abort : out -> Prop :=
| abort_div : abort out_div
| abort_control : forall st r, res_control r -> abort (out_ter st r)
.