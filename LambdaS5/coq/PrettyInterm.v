Set Implicit Arguments.
Require Import Syntax.
Require Import Context.
Require Import Values.
Require Import Coq.Strings.String.

Inductive ext_expr :=
| expr_basic : expr -> ext_expr
| expr_object_1 : out -> expr -> expr -> expr -> expr -> list (string * property) -> ext_expr
| expr_object_2 : value -> out -> expr -> expr -> expr -> list (string * property) -> ext_expr
| expr_object_3 : value -> value -> out -> expr -> expr -> list (string * property) -> ext_expr
| expr_object_4 : value -> value -> value -> out -> expr -> list (string * property) -> ext_expr
| expr_object_5 : value -> value -> value -> value -> out -> list (string * property) -> ext_expr
| expr_object_6 : object -> list (string * property) -> ext_expr
| expr_object_data_1 : object -> list (string * property) -> string -> out -> expr -> expr -> expr -> ext_expr
| expr_object_data_2 : object -> list (string * property) -> string -> value -> out -> expr -> expr -> ext_expr
| expr_object_data_3 : object -> list (string * property) -> string -> value -> value -> out -> expr -> ext_expr
| expr_object_data_4 : object -> list (string * property) -> string -> value -> value -> value -> out -> ext_expr
| expr_object_accessor_1 : object -> list (string * property) -> string -> out -> expr -> expr -> expr -> ext_expr
| expr_object_accessor_2 : object -> list (string * property) -> string -> value -> out -> expr -> expr -> ext_expr
| expr_object_accessor_3 : object -> list (string * property) -> string -> value -> value -> out -> expr -> ext_expr
| expr_object_accessor_4 : object -> list (string * property) -> string -> value -> value -> value -> out -> ext_expr
| expr_get_attr_1 : pattr -> out -> expr -> ext_expr
| expr_get_attr_2 : pattr -> value -> out -> ext_expr
| expr_set_attr_1 : pattr -> out -> expr -> expr -> ext_expr
| expr_set_attr_2 : pattr -> value -> out -> expr -> ext_expr
| expr_set_attr_3 : pattr -> value -> value -> out -> ext_expr
| expr_get_obj_attr_1 : oattr -> out -> ext_expr
| expr_set_obj_attr_1 : oattr -> out -> expr -> ext_expr
| expr_set_obj_attr_2 : oattr -> value -> out -> ext_expr
| expr_get_field_1 : out -> expr -> expr -> ext_expr
| expr_get_field_2 : value -> out -> expr -> ext_expr
| expr_get_field_3 : value -> value -> out -> ext_expr
| expr_get_field_4 : object_ptr -> option attributes -> value -> ext_expr
| expr_set_field_1 : out -> expr -> expr -> expr -> ext_expr
| expr_set_field_2 : value -> out -> expr -> expr -> ext_expr
| expr_set_field_3 : value -> value -> out -> expr -> ext_expr
| expr_set_field_4 : value -> value -> value -> out -> ext_expr
| expr_set_field_5 : object_ptr -> object -> option attributes -> prop_name -> value -> value -> ext_expr
| expr_delete_field_1 : out -> expr -> ext_expr
| expr_delete_field_2 : value -> out -> ext_expr
| expr_delete_field_3 : object_ptr -> object -> option attributes -> prop_name -> ext_expr
| expr_own_field_names_1 : out -> ext_expr
| expr_set_bang_1 : id -> out -> ext_expr
| expr_op1_1 : unary_op -> out -> ext_expr
| expr_op2_1 : binary_op -> out -> expr -> ext_expr
| expr_op2_2 : binary_op -> value -> out -> ext_expr 
| expr_if_1 : out -> expr -> expr -> ext_expr
| expr_app_1 : out -> list expr -> ext_expr
| expr_app_2 : value -> list value -> list expr -> ext_expr
| expr_app_3 : value -> list value -> out -> list expr -> ext_expr
| expr_seq_1 : out -> expr -> ext_expr
| expr_let_1 : id -> out -> expr -> ext_expr
| expr_recc_1 : value_loc -> out -> expr -> ext_expr
| expr_label_1 : id -> out -> ext_expr
| expr_break_1 : id -> out -> ext_expr
| expr_try_catch_1 : out -> expr -> ext_expr
| expr_try_catch_2 : value -> out -> ext_expr
| expr_try_finally_1 : out -> expr -> ext_expr
| expr_try_finally_2 : res -> out -> ext_expr
| expr_throw_1 : out -> ext_expr
| expr_eval_1 : out -> expr -> ext_expr
| expr_eval_2 : value -> out -> ext_expr
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