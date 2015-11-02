Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Export LjsSyntax.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Global Instance value_inhab : Inhab value.
Proof.
    intros. apply (prove_Inhab value_undefined).
Qed.

Inductive type :=
| type_empty
| type_undefined
| type_null
| type_bool
| type_number
| type_int
| type_string
| type_object
| type_closure
.

Definition value_type v :=
    match v with
    | value_empty => type_empty
    | value_undefined => type_undefined
    | value_null => type_null
    | value_bool _ => type_bool
    | value_number _ => type_number
    | value_int _ => type_int
    | value_string _ => type_string
    | value_object _ => type_object
    | value_closure _ => type_closure
    end.

Inductive unary_op_type : unary_op -> type -> type -> Prop := 
(* debugging operators *)
| unary_op_type_print : forall t, unary_op_type unary_op_print t type_undefined
| unary_op_type_pretty : forall t, unary_op_type unary_op_pretty t type_undefined
(* string operators *)
| unary_op_type_strlen : unary_op_type unary_op_strlen type_string type_number
| unary_op_type_ascii_ntoc : unary_op_type unary_op_ascii_ntoc type_int type_string
| unary_op_type_ascii_cton : unary_op_type unary_op_ascii_cton type_string type_int
(* type testing operators *)
| unary_op_type_typeof : forall t, unary_op_type unary_op_typeof t type_string
| unary_op_type_is_primitive : forall t, unary_op_type unary_op_is_primitive t type_bool
| unary_op_type_is_closure : forall t, unary_op_type unary_op_is_closure t type_bool
| unary_op_type_is_object : forall t, unary_op_type unary_op_is_object t type_bool
(* number operators *)
| unary_op_type_abs : unary_op_type unary_op_abs type_number type_number
| unary_op_type_floor : unary_op_type unary_op_floor type_number type_number
| unary_op_type_ceil : unary_op_type unary_op_floor type_number type_number
| unary_op_type_neg : unary_op_type unary_op_neg type_number type_number
| unary_op_type_sign : unary_op_type unary_op_sign type_number type_number
(* conversion operators *)
| unary_op_type_prim_to_str : forall t, unary_op_type unary_op_prim_to_bool t type_string
| unary_op_type_prim_to_num : forall t, unary_op_type unary_op_prim_to_bool t type_number
| unary_op_type_prim_to_bool : forall t, unary_op_type unary_op_prim_to_bool t type_bool
| unary_op_type_prim_to_int : forall t, unary_op_type unary_op_prim_to_bool t type_int
(* logic operators *)
| unary_op_type_not : unary_op_type unary_op_not type_bool type_bool
(* int operators *)
| unary_op_type_bnot : unary_op_type unary_op_bnot type_number type_number
(* time operators *)
| unary_op_type_current_utc_millis : unary_op_type unary_op_current_utc_millis type_undefined type_number
.

Definition unary_op_ret_type op :=
    match op with 
    (* debugging operators *)
    | unary_op_print 
    | unary_op_pretty => type_undefined
    (* string operators *)
    | unary_op_strlen => type_number
    | unary_op_ascii_ntoc => type_string
    | unary_op_ascii_cton => type_int
    (* type testing operators *)
    | unary_op_typeof => type_string
    | unary_op_is_primitive 
    | unary_op_is_closure 
    | unary_op_is_object => type_bool
    (* number operators *)
    | unary_op_abs 
    | unary_op_floor 
    | unary_op_ceil
    | unary_op_neg 
    | unary_op_sign => type_number
    (* conversion operators *)
    | unary_op_prim_to_str => type_string
    | unary_op_prim_to_num => type_number
    | unary_op_prim_to_bool => type_bool
    | unary_op_prim_to_int => type_int
    (* logic operators *)
    | unary_op_not => type_bool
    (* int operators *)
    | unary_op_bnot => type_int
    (* time operators *)
    | unary_op_current_utc_millis => type_number
    (* undefined operators *)
    | _ => type_undefined
    end.

Inductive binary_op_type : binary_op -> type -> type -> type -> Prop := 
(* arithmetic operators *)
| binary_op_type_add : binary_op_type binary_op_add type_number type_number type_number
| binary_op_type_sub : binary_op_type binary_op_sub type_number type_number type_number
| binary_op_type_mul : binary_op_type binary_op_mul type_number type_number type_number
| binary_op_type_div : binary_op_type binary_op_div type_number type_number type_number
| binary_op_type_mod : binary_op_type binary_op_mod type_number type_number type_number
(* comparison operators *)
| binary_op_type_lt : binary_op_type binary_op_lt type_number type_number type_bool
| binary_op_type_le : binary_op_type binary_op_le type_number type_number type_bool
| binary_op_type_gt : binary_op_type binary_op_gt type_number type_number type_bool
| binary_op_type_ge : binary_op_type binary_op_ge type_number type_number type_bool
(* string comparison operators *)
| binary_op_type_string_lt : binary_op_type binary_op_string_lt type_string type_string type_bool
| binary_op_type_locale_compare : binary_op_type binary_op_locale_compare type_string type_string type_bool
(* equality operators *)
| binary_op_type_stx_eq : forall t1 t2, binary_op_type binary_op_stx_eq t1 t2 type_bool
| binary_op_type_same_value : forall t1 t2, binary_op_type binary_op_same_value t1 t2 type_bool
(* object inspection operators *)
| binary_op_type_has_own_property : binary_op_type binary_op_has_own_property type_object type_string type_bool
| binary_op_type_has_internal : binary_op_type binary_op_has_internal type_object type_string type_bool
| binary_op_type_is_accessor : binary_op_type binary_op_is_accessor type_object type_string type_bool
(* string operators *)
| binary_op_type_string_plus : binary_op_type binary_op_string_plus type_string type_string type_string
| binary_op_type_char_at : binary_op_type binary_op_char_at type_string type_number type_string
(* int operators (bitwise and shifts) *)
| binary_op_type_band : binary_op_type binary_op_band type_int type_int type_int
| binary_op_type_bor : binary_op_type binary_op_bor type_int type_int type_int
| binary_op_type_bxor : binary_op_type binary_op_bxor type_int type_int type_int
| binary_op_type_shiftl : binary_op_type binary_op_shiftl type_int type_int type_int
| binary_op_type_shiftr : binary_op_type binary_op_shiftr type_int type_int type_int
| binary_op_type_zfshiftr : binary_op_type binary_op_zfshiftr type_int type_int type_int
.

Definition binary_op_ret_type op := 
    match op with
    (* arithmetic operators *)
    | binary_op_add 
    | binary_op_sub 
    | binary_op_mul 
    | binary_op_div 
    | binary_op_mod => type_number
    (* comparison operators *)
    | binary_op_lt 
    | binary_op_le 
    | binary_op_gt 
    | binary_op_ge 
    (* string comparison operators *)
    | binary_op_string_lt 
    | binary_op_locale_compare 
    (* equality operators *)
    | binary_op_stx_eq 
    | binary_op_same_value 
    (* object inspection operators *)
    | binary_op_has_own_property 
    | binary_op_has_internal 
    | binary_op_is_accessor => type_bool
    (* string operators *)
    | binary_op_string_plus 
    | binary_op_char_at => type_string
    (* int operators (bitwise and shifts) *)
    | binary_op_band 
    | binary_op_bor
    | binary_op_bxor 
    | binary_op_shiftl 
    | binary_op_shiftr 
    | binary_op_zfshiftr => type_int
    (* undefined operators *)
    | _ => type_undefined
    end.

Inductive pure_expr : expr -> Prop :=
| pure_expr_empty : pure_expr expr_empty
| pure_expr_null : pure_expr expr_null
| pure_expr_undefined : pure_expr expr_undefined
| pure_expr_string : forall s, pure_expr (expr_string s)
| pure_expr_number : forall n, pure_expr (expr_number n)
| pure_expr_int : forall n, pure_expr (expr_int n)
| pure_expr_bool : forall b, pure_expr (expr_bool b)
| pure_expr_lambda : forall is e, pure_expr (expr_lambda is e)
| pure_expr_id : forall i, pure_expr (expr_id i)
| pure_expr_if : forall e1 e2 e3, 
    pure_expr e1 -> pure_expr e2 -> pure_expr e3 -> 
    pure_expr (expr_if e1 e2 e3)
| pure_expr_seq : forall e1 e2, 
    pure_expr e1 -> pure_expr e2 ->
    pure_expr (expr_seq e1 e2)
| pure_expr_jseq : forall e1 e2, 
    pure_expr e1 -> pure_expr e2 ->
    pure_expr (expr_jseq e1 e2)
| pure_expr_let : forall s e1 e2, 
    pure_expr e1 -> pure_expr e2 ->
    pure_expr (expr_let s e1 e2)
| pure_expr_op1 : forall op e, 
    pure_expr e ->
    pure_expr (expr_op1 op e)
| pure_expr_op2 : forall op e1 e2, 
    pure_expr e1 -> pure_expr e2 ->
    pure_expr (expr_op2 op e1 e2)
| pure_expr_get_attr : forall pa e1 e2,
    pure_expr e1 -> pure_expr e2 ->
    pure_expr (expr_get_attr pa e1 e2)
| pure_expr_get_oattr : forall oa e,
    pure_expr e ->
    pure_expr (expr_get_obj_attr oa e)
.

Inductive bool_expr : expr -> Prop :=
| bool_expr_bool : forall b, bool_expr (expr_bool b)
| bool_expr_if : forall e1 e2 e3,
    bool_expr e1 -> bool_expr e2 -> bool_expr e3 ->
    bool_expr (expr_if e1 e2 e3)
| bool_expr_let : forall s e1 e2,
    pure_expr e1 -> bool_expr e2 -> 
    bool_expr (expr_let s e1 e2)
| bool_expr_not : forall e,
    bool_expr e ->
    bool_expr (expr_op1 unary_op_not e)
| bool_expr_op1 : forall op e,
    unary_op_ret_type op = type_bool ->
    op <> unary_op_not ->
    pure_expr e ->
    bool_expr (expr_op1 op e)
| bool_expr_op2 : forall op e1 e2,
    binary_op_ret_type op = type_bool ->
    pure_expr e1 ->
    pure_expr e2 ->
    bool_expr (expr_op2 op e1 e2)
.

Create HintDb ljs discriminated.

Hint Constructors pure_expr : ljs.
Hint Constructors bool_expr : ljs.
