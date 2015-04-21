Set Implicit Arguments.
Require Import JsNumber.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsCommon.
Require Import LjsValues.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Inductive ext_expr :=
| expr_basic : expr -> ext_expr
| expr_eval_many_1 : list expr -> list value -> (list value -> ext_expr) -> ext_expr
| expr_eval_many_2 : list expr -> out -> list value -> (list value -> ext_expr) -> ext_expr
| expr_object_1 : list (string * property) -> list value -> ext_expr
| expr_object_2 : object -> list (string * property) -> ext_expr
| expr_object_data_1 : object -> list (string * property) -> string -> list value -> ext_expr
| expr_object_accessor_1 : object -> list (string * property) -> string -> list value -> ext_expr
| expr_get_attr_1 : pattr -> list value -> ext_expr
| expr_set_attr_1 : pattr -> list value -> ext_expr
| expr_get_obj_attr_1 : oattr -> out -> ext_expr
| expr_set_obj_attr_1 : oattr -> list value -> ext_expr
| expr_get_field_1 : list value -> ext_expr
| expr_get_field_2 : object_ptr -> option attributes -> ext_expr
| expr_set_field_1 : list value -> ext_expr
| expr_set_field_2 : object_ptr -> object -> option attributes -> prop_name -> value -> ext_expr
| expr_delete_field_1 : list value -> ext_expr
| expr_delete_field_2 : object_ptr -> object -> option attributes -> prop_name -> ext_expr
| expr_own_field_names_1 : out -> ext_expr
| expr_op1_1 : unary_op -> out -> ext_expr
| expr_op2_1 : binary_op -> out -> expr -> ext_expr
| expr_op2_2 : binary_op -> value -> out -> ext_expr 
| expr_if_1 : out -> expr -> expr -> ext_expr
| expr_app_1 : out -> list expr -> ext_expr
| expr_app_2 : value -> list value -> ext_expr
| expr_seq_1 : out -> expr -> ext_expr
| expr_jseq_1 : out -> expr -> ext_expr
| expr_jseq_2 : value -> out -> ext_expr
| expr_let_1 : id -> out -> expr -> ext_expr
| expr_label_1 : id -> out -> ext_expr
| expr_break_1 : id -> out -> ext_expr
| expr_try_catch_1 : out -> expr -> ext_expr
| expr_try_catch_2 : value -> out -> ext_expr
| expr_try_finally_1 : out -> expr -> ext_expr
| expr_try_finally_2 : res -> out -> ext_expr
| expr_throw_1 : out -> ext_expr
| expr_eval_1 : list value -> ext_expr
.

Coercion expr_basic : expr >-> ext_expr.

Definition out_of_ext_expr p := match p with
| expr_eval_many_2 _ o _ _ 
| expr_get_obj_attr_1 _ o
| expr_own_field_names_1 o
| expr_op1_1 _ o
| expr_op2_1 _ o _ 
| expr_op2_2 _ _ o 
| expr_if_1 o _ _
| expr_app_1 o _
| expr_seq_1 o _
| expr_jseq_1 o _
| expr_jseq_2 _ o
| expr_let_1 _ o _
| expr_label_1 _ o
| expr_break_1 _ o
| expr_try_catch_1 o _
| expr_try_catch_2 _ o
| expr_try_finally_1 o _
| expr_try_finally_2 _ o
| expr_throw_1 o 
    => Some o
| _ => None
end.

Inductive abort_intercepted_expr : ext_expr -> Prop := 
| abort_intercepted_expr_jseq_2 : forall st i v v',
    abort_intercepted_expr (expr_jseq_2 v (out_ter st (res_break i v')))
| abort_intercepted_expr_label_1 : forall st i v,
    abort_intercepted_expr (expr_label_1 i (out_ter st (res_break i v)))
| abort_intercepted_expr_try_catch_1 : forall st e v,
    abort_intercepted_expr (expr_try_catch_1 (out_ter st (res_exception v)) e)
| abort_intercepted_expr_try_finally_1 : forall st r e,
    abort_intercepted_expr (expr_try_finally_1 (out_ter st r) e)
.

Inductive res_is_value : res -> Prop :=
| res_is_value_value : forall v, res_is_value (res_value v)
.

Hint Constructors res_is_value.

Inductive res_is_control : res -> Prop :=
| res_is_control_exception : forall v, res_is_control (res_exception v)
| res_is_control_break : forall i v, res_is_control (res_break i v)
.

Hint Constructors res_is_control.

Inductive abort : out -> Prop :=
| abort_div : abort out_div
| abort_control : forall st r, res_is_control r -> abort (out_ter st r)
.

Hint Constructors abort.

Inductive object_property_is st : object -> prop_name -> option attributes -> Prop :=
| object_property_is_own : forall obj name attr, 
    binds (object_properties obj) name attr -> 
    object_property_is st obj name (Some attr)
| object_property_is_none : forall obj name,
    ~index (object_properties obj) name ->
    object_proto obj = value_null ->
    object_property_is st obj name None
| object_property_is_proto : forall obj obj' ptr name oattr,
    ~index (object_properties obj) name ->
    object_proto obj = value_object ptr ->
    binds st ptr obj' ->
    object_property_is st obj' name oattr ->
    object_property_is st obj name oattr.

Inductive value_is_closure st : value -> closure -> Prop :=
| value_is_closure_closure : forall clo, 
    value_is_closure st (value_closure clo) clo
| value_is_closure_code : forall ptr obj clo,
    binds st ptr obj ->
    value_is_closure st (object_code obj) clo ->
    value_is_closure st (value_object ptr) clo.

Inductive closure_ctx : closure -> list value -> ctx -> Prop :=
| closure_ctx_nonrec : forall args_n args_v args lc body,
    Zip args_n args_v args ->
    closure_ctx (closure_intro lc None args_n body) args_v (from_list args \u from_list lc)
| closure_ctx_rec : forall s args_n args_v args lc body,
    Zip args_n args_v args ->
    closure_ctx (closure_intro lc (Some s) args_n body) args_v 
        (from_list args \u (from_list lc \(s := value_closure (closure_intro lc (Some s) args_n body)))).

Inductive int_unary_op : unary_op -> (int -> int) -> Prop :=
| int_unary_op_bnot : int_unary_op unary_op_bnot int32_bitwise_not
| int_unary_op_to_int32 : int_unary_op unary_op_to_int32 (fun x => x)
.

Inductive num_unary_op : unary_op -> (number -> number) -> Prop :=
| num_unary_op_abs : num_unary_op unary_op_abs absolute
| num_unary_op_floor : num_unary_op unary_op_floor floor
.

Inductive eval_unary_op : unary_op -> store -> value -> value -> Prop :=
| eval_unary_op_print : forall v st, eval_unary_op unary_op_print st v value_undefined
| eval_unary_op_pretty : forall v st, eval_unary_op unary_op_pretty st v value_undefined
| eval_unary_op_strlen : forall s st, 
    eval_unary_op unary_op_strlen st (value_string s) (value_number (of_int (String.length s)))
| eval_unary_op_typeof : forall v st, eval_unary_op unary_op_typeof st v (value_string (typeof v))
| eval_unary_op_is_primitive : forall v st, 
    eval_unary_op unary_op_is_primitive st v (value_bool (decide (is_primitive v)))
| eval_unary_op_is_closure : forall v st, 
    eval_unary_op unary_op_is_closure st v (value_bool (decide (is_closure v)))
| eval_unary_op_is_object : forall v st, 
    eval_unary_op unary_op_is_object st v (value_bool (decide (is_object v)))
| eval_unary_op_num : forall n op F st, 
    num_unary_op op F -> eval_unary_op op st (value_number n) (value_number (F n))
| eval_unary_op_int32 : forall n op F st, 
    int_unary_op op F -> eval_unary_op op st (value_number n) (value_number (of_int (F (to_int32 n))))
| eval_unary_op_not : forall b st, eval_unary_op unary_op_not st (value_bool b) (value_bool (! b))
| eval_unary_op_prim_to_bool : forall v st, 
    eval_unary_op unary_op_prim_to_bool st v (value_bool (value_to_bool_cast v))
| eval_unary_op_prim_to_str : forall v st, 
    eval_unary_op unary_op_prim_to_str st v (value_string (value_to_str_cast v))
| eval_unary_op_prim_to_num : forall v st, 
    eval_unary_op unary_op_prim_to_num st v (value_number (value_to_num_cast v))
| eval_unary_op_ascii_ntoc : forall n st,
    eval_unary_op unary_op_ascii_ntoc st (value_number n)
        (value_string (String (_ascii_of_int (to_int32 n)) EmptyString))
| eval_unary_op_ascii_cton : forall ch s st,
    eval_unary_op unary_op_ascii_cton st (value_string (String ch s)) (value_number (of_int (_int_of_ascii ch)))
.
