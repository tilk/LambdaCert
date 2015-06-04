Set Implicit Arguments.
Require Import LibInt.
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
| expr_object_1 : list (string * expr) -> list (string * property) -> list value -> ext_expr
| expr_object_2 : list (string * expr) -> list (string * property) -> object -> ext_expr
| expr_object_internal_1 : object -> string -> (object -> ext_expr) -> list value -> ext_expr
| expr_object_data_1 : object -> string -> (object -> ext_expr) -> list value -> ext_expr
| expr_object_accessor_1 : object -> string -> (object -> ext_expr) -> list value -> ext_expr
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
| expr_get_internal_1 : string -> list value -> ext_expr
| expr_set_internal_1 : string -> list value -> ext_expr
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
| object_property_is_own : forall oas props iprops name attr, 
    binds props name attr -> 
    object_property_is st (object_intro oas props iprops) name (Some attr)
| object_property_is_none : forall oas props iprops name,
    ~index props name ->
    oattrs_proto oas = value_null ->
    object_property_is st (object_intro oas props iprops) name None
| object_property_is_proto : forall oas props iprops obj' ptr name oattr,
    ~index props name ->
    oattrs_proto oas = value_object ptr ->
    binds st ptr obj' ->
    object_property_is st obj' name oattr ->
    object_property_is st (object_intro oas props iprops) name oattr.

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
| num_unary_op_ceil : num_unary_op unary_op_ceil ceil
| num_unary_op_neg : num_unary_op unary_op_neg neg
| num_unary_op_sign : num_unary_op unary_op_sign sign
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
| eval_unary_op_int : forall n op F st, 
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
| eval_unary_op_current_utc_millis : forall st, 
    eval_unary_op unary_op_current_utc_millis st value_undefined (value_number (current_utc tt))
.

Inductive num_binary_op : binary_op -> (number -> number -> number) -> Prop :=
| num_binary_op_add : num_binary_op binary_op_add JsNumber.add
| num_binary_op_sub : num_binary_op binary_op_sub JsNumber.sub
| num_binary_op_mul : num_binary_op binary_op_mul JsNumber.mult
| num_binary_op_div : num_binary_op binary_op_div JsNumber.div
| num_binary_op_mod : num_binary_op binary_op_mod JsNumber.fmod
.

Inductive int_binary_op : binary_op -> (int -> int -> int) -> Prop :=
| int_binary_op_band : int_binary_op binary_op_band int32_bitwise_and
| int_binary_op_bor : int_binary_op binary_op_bor int32_bitwise_or
| int_binary_op_bxor : int_binary_op binary_op_bxor int32_bitwise_xor
| int_binary_op_shiftl : int_binary_op binary_op_shiftl int32_left_shift
| int_binary_op_shiftr : int_binary_op binary_op_shiftr int32_right_shift
| int_binary_op_zfshiftr : int_binary_op binary_op_zfshiftr uint32_right_shift
.

Inductive num_cmp_binary_op : binary_op -> (number -> number -> bool) -> Prop :=
| num_cmp_binary_op_lt : num_cmp_binary_op binary_op_lt num_lt
| num_cmp_binary_op_gt : num_cmp_binary_op binary_op_gt num_gt
| num_cmp_binary_op_le : num_cmp_binary_op binary_op_le num_le
| num_cmp_binary_op_ge : num_cmp_binary_op binary_op_ge num_ge
.

Inductive eval_binary_op : binary_op -> store -> value -> value -> value -> Prop :=
| eval_binary_op_num : forall op st F n1 n2, 
    num_binary_op op F -> 
    eval_binary_op op st (value_number n1) (value_number n2) (value_number (F n1 n2))
| eval_binary_op_int : forall op st F n1 n2, 
    int_binary_op op F -> 
    eval_binary_op op st (value_number n1) (value_number n2) (value_number (of_int (F (to_int32 n1) (to_int32 n2))))
| eval_binary_op_num_cmp : forall op st F n1 n2,
    num_cmp_binary_op op F ->
    eval_binary_op op st (value_number n1) (value_number n2) (value_bool (F n1 n2))
| eval_binary_op_stx_eq : forall st v1 v2,
    eval_binary_op binary_op_stx_eq st v1 v2 (value_bool (decide (stx_eq v1 v2)))
| eval_binary_op_same_value : forall st v1 v2,
    eval_binary_op binary_op_same_value st v1 v2 (value_bool (decide (same_value v1 v2)))
| eval_binary_op_string_plus : forall st s1 s2,
    eval_binary_op binary_op_string_plus st (value_string s1) (value_string s2) (value_string (s1++s2))
| eval_binary_op_has_property : forall st ptr obj s oattrs,
    binds st ptr obj -> 
    object_property_is st obj s oattrs ->
    eval_binary_op binary_op_has_property st (value_object ptr) (value_string s) 
        (value_bool (is_some oattrs))
| eval_binary_op_has_own_property : forall st ptr obj s,
    binds st ptr obj -> 
    eval_binary_op binary_op_has_own_property st (value_object ptr) (value_string s) 
        (value_bool (decide (index (object_properties obj) s)))
| eval_binary_op_has_internal : forall st ptr obj s,
    binds st ptr obj ->
    eval_binary_op binary_op_has_internal st (value_object ptr) (value_string s)
        (value_bool (decide (index (object_internal obj) s)))
| eval_binary_op_string_lt : forall st s1 s2,
    eval_binary_op binary_op_string_lt st (value_string s1) (value_string s2) (value_bool (string_lt s1 s2))
| eval_binary_op_locale_compare : forall st s1 s2,
    eval_binary_op binary_op_locale_compare st (value_string s1) (value_string s2) (value_bool (string_lt s1 s2))
| eval_binary_op_is_accessor : forall st s ptr obj attrs,
    binds st ptr obj -> 
    object_property_is st obj s (Some attrs) ->
    eval_binary_op binary_op_is_accessor st (value_object ptr) (value_string s) 
        (value_bool (decide (is_accessor attrs)))
| eval_binary_op_char_at : forall st s ch n,
    0 <= to_int32 n -> String.get (abs (to_int32 n)) s = Some ch ->
    eval_binary_op binary_op_char_at st (value_string s) (value_number n) 
        (value_string (String ch EmptyString))
.
