Require Import Syntax.
Require Import PrettyInterm.
Require Import Store.
Require Import Context.
Require Import Values.
Require Import Operators.
Require Import Monads.
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
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

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

| red_expr_get_attr : forall c st pa e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_get_attr_1 pa o e2) o' ->
    red_expr c st (expr_get_attr pa e1 e2) o'
| red_expr_get_attr_1 : forall c st' st pa v1 e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_get_attr_2 pa v1 o) o' ->
    red_expr c st' (expr_get_attr_1 pa (out_ter st (res_value v1)) e2) o'
| red_expr_get_attr_1_abort : forall c st pa e2 o,
    abort o ->
    red_expr c st (expr_get_attr_1 pa o e2) o
| red_expr_get_attr_2_abort : forall c st pa v1 o,
    abort o ->
    red_expr c st (expr_get_attr_2 pa v1 o) o

| red_expr_set_attr : forall c st pa e1 e2 e3 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_set_attr_1 pa o e2 e3) o' ->
    red_expr c st (expr_set_attr pa e1 e2 e3) o'
| red_expr_set_attr_1 : forall c st' st pa v1 e2 e3 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_set_attr_2 pa v1 o e3) o' ->
    red_expr c st' (expr_set_attr_1 pa (out_ter st (res_value v1)) e2 e3) o'
| red_expr_set_attr_1_abort : forall c st pa e2 e3 o,
    abort o ->
    red_expr c st (expr_set_attr_1 pa o e2 e3) o
| red_expr_set_attr_2 : forall c st' st pa v1 v2 e3 o o',
    red_expr c st e3 o ->
    red_expr c st (expr_set_attr_3 pa v1 v2 o) o' ->
    red_expr c st' (expr_set_attr_2 pa v1 (out_ter st (res_value v2)) e3) o'
| red_expr_set_attr_2_abort : forall c st pa v1 e3 o,
    abort o ->
    red_expr c st (expr_set_attr_2 pa v1 o e3) o
| red_expr_set_attr_3_abort : forall c st pa v1 v2 o,
    abort o ->
    red_expr c st (expr_set_attr_3 pa v1 v2 o) o

| red_expr_get_obj_attr : forall c st oa e1 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_get_obj_attr_1 oa o) o' ->
    red_expr c st (expr_get_obj_attr oa e1) o'
| red_expr_get_obj_attr_1 : forall c st' st oa ptr obj,
    get_object st ptr = Some obj ->
    red_expr c st' (expr_get_obj_attr_1 oa (out_ter st (res_value (value_object ptr)))) (out_ter st (res_value (get_object_oattr obj oa)))
| red_expr_get_obj_attr_1_abort : forall c st oa o,
    abort o ->
    red_expr c st (expr_get_obj_attr_1 oa o) o

| red_expr_set_obj_attr : forall c st oa e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_set_obj_attr_1 oa o e2) o' ->
    red_expr c st (expr_set_obj_attr oa e1 e2) o'
| red_expr_set_obj_attr_1 : forall c st' st oa v1 e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_set_obj_attr_2 oa v1 o) o' ->
    red_expr c st' (expr_set_obj_attr_1 oa (out_ter st (res_value v1)) e2) o'
| red_expr_set_obj_attr_1_abort : forall c st oa e2 o,
    abort o ->
    red_expr c st (expr_set_obj_attr_1 oa o e2) o
| red_expr_set_obj_attr_2 : forall c st' st st1 oa ptr obj obj' v,
    get_object st ptr = Some obj ->
    set_object_oattr obj oa v = result_some obj' ->
    st1 = update_object st ptr obj' ->
    red_expr c st' (expr_set_obj_attr_2 oa (value_object ptr) (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_expr_set_obj_attr_2_abort : forall c st oa v1 o,
    abort o ->
    red_expr c st (expr_set_obj_attr_2 oa v1 o) o

| red_expr_get_field : forall c st e1 e2 e3 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_get_field_1 o e2 e3) o' ->
    red_expr c st (expr_get_field e1 e2 e3) o'
| red_expr_get_field_1 : forall c st' st v1 e2 e3 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_get_field_2 v1 o e3) o' ->
    red_expr c st' (expr_get_field_1 (out_ter st (res_value v1)) e2 e3) o'
| red_expr_get_field_1_abort : forall c st e2 e3 o,
    abort o ->
    red_expr c st (expr_get_field_1 o e2 e3) o
| red_expr_get_field_2 : forall c st' st v1 v2 e3 o o',
    red_expr c st e3 o ->
    red_expr c st (expr_get_field_3 v1 v2 o) o' ->
    red_expr c st' (expr_get_field_2 v1 (out_ter st (res_value v2)) e3) o'
| red_expr_get_field_2_abort : forall c st v1 e3 o,
    abort o ->
    red_expr c st (expr_get_field_2 v1 o e3) o
| red_expr_get_field_3 : forall c st' st v3 ptr s oattr o,
    get_property st ptr s = result_some oattr ->
    red_expr c st (expr_get_field_4 ptr oattr v3) o ->
    red_expr c st' (expr_get_field_3 (value_object ptr) (value_string s) (out_ter st (res_value v3))) o
| red_expr_get_field_3_abort : forall c st v1 v2 o,
    abort o ->
    red_expr c st (expr_get_field_3 v1 v2 o) o
| red_expr_get_field_4_no_field : forall c st ptr v3,
    red_expr c st (expr_get_field_4 ptr None v3) (out_ter st (res_value value_undefined))
| red_expr_get_field_4_get_field : forall c st ptr v3 data,
    red_expr c st (expr_get_field_4 ptr (Some (attributes_data_of data)) v3) (out_ter st (res_value (attributes_data_value data)))
| red_expr_get_field_4_getter : forall c st ptr v3 acc o,
    red_expr c st (expr_app_2 (attributes_accessor_get acc) [v3; value_object ptr] nil) o ->
    red_expr c st (expr_get_field_4 ptr (Some (attributes_accessor_of acc)) v3) o

| red_expr_set_field : forall c st e1 e2 e3 e4 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_set_field_1 o e2 e3 e4) o' ->
    red_expr c st (expr_set_field e1 e2 e3 e4) o'
| red_expr_set_field_1 : forall c st' st v1 e2 e3 e4 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_set_field_2 v1 o e3 e4) o' ->
    red_expr c st' (expr_set_field_1 (out_ter st (res_value v1)) e2 e3 e4) o'
| red_expr_set_field_1_abort : forall c st e2 e3 e4 o,
    abort o ->
    red_expr c st (expr_set_field_1 o e2 e3 e4) o
| red_expr_set_field_2 : forall c st' st v1 v2 e3 e4 o o',
    red_expr c st e3 o ->
    red_expr c st (expr_set_field_3 v1 v2 o e4) o' ->
    red_expr c st' (expr_set_field_2 v1 (out_ter st (res_value v2)) e3 e4) o'
| red_expr_set_field_2_abort : forall c st v1 e3 e4 o,
    abort o ->
    red_expr c st (expr_set_field_2 v1 o e3 e4) o
| red_expr_set_field_3 : forall c st' st v1 v2 v3 e4 o o',
    red_expr c st e4 o ->
    red_expr c st (expr_set_field_4 v1 v2 v3 o) o' ->
    red_expr c st' (expr_set_field_3 v1 v2 (out_ter st (res_value v3)) e4) o'
| red_expr_set_field_3_abort : forall c st v1 v2 e4 o,
    abort o ->
    red_expr c st (expr_set_field_3 v1 v2 o e4) o
| red_expr_set_field_4 : forall c st' st ptr obj oattr s v3 v4 o,
    get_property st ptr s = result_some oattr ->
    get_object st ptr = Some obj ->
    red_expr c st (expr_set_field_5 ptr obj oattr s v3 v4) o ->
    red_expr c st' (expr_set_field_4 (value_object ptr) (value_string s) v3 (out_ter st (res_value v4))) o
| red_expr_set_field_4_abort : forall c st v1 v2 v3 o,
    abort o ->
    red_expr c st (expr_set_field_4 v1 v2 v3 o) o
| red_expr_set_field_4_set_field : forall c st st1 ptr obj data attr s v3 v4,
    get_object_property obj s = Some attr ->
    attributes_data_writable data = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_value_update data v3))) ->
    red_expr c st (expr_set_field_5 ptr obj (Some (attributes_data_of data)) s v3 v4) (out_ter st1 (res_value v3))
| red_expr_set_field_4_shadow_field : forall c st st1 ptr obj data s v3 v4,
    get_object_property obj s = None ->
    object_extensible obj = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_expr c st (expr_set_field_5 ptr obj (Some (attributes_data_of data)) s v3 v4) (out_ter st1 (res_value v3))
| red_expr_set_field_4_add_field : forall c st st1 ptr obj s v3 v4,
    object_extensible obj = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_expr c st (expr_set_field_5 ptr obj None s v3 v4) (out_ter st1 (res_value v3))
| red_expr_set_field_4_setter : forall c st ptr obj acc s v3 v4 o,
    red_expr c st (expr_app_2 (attributes_accessor_get acc) [v4; value_object ptr] nil) o ->
    red_expr c st (expr_set_field_5 ptr obj (Some (attributes_accessor_of acc)) s v3 v4) o

| red_expr_delete_field : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_delete_field_1 o e2) o' ->
    red_expr c st (expr_delete_field e1 e2) o'
| red_expr_delete_field_1 : forall c st' st v1 e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_delete_field_2 v1 o) o' ->
    red_expr c st' (expr_delete_field_1 (out_ter st (res_value v1)) e2) o'
| red_expr_delete_field_1_abort : forall c st e2 o,
    abort o ->
    red_expr c st (expr_delete_field_1 o e2) o
| red_expr_delete_field_2 : forall c st' st ptr s obj oattr o,
    get_object st ptr = Some obj ->
    get_object_property obj s = oattr ->
    red_expr c st (expr_delete_field_3 ptr obj oattr s) o ->
    red_expr c st' (expr_delete_field_2 (value_object ptr) (out_ter st (res_value (value_string s)))) o
| red_expr_delete_field_2_abort : forall c st v1 o,
    abort o ->
    red_expr c st (expr_delete_field_2 v1 o) o
| red_expr_delete_field_3_not_found : forall c st ptr obj s,
    red_expr c st (expr_delete_field_3 ptr obj None s) (out_ter st (res_value value_false))
| red_expr_delete_field_3_unconfigurable : forall c st ptr obj attr s,
    attributes_configurable attr = false ->
    red_expr c st (expr_delete_field_3 ptr obj (Some attr) s) (out_ter st (res_exception (value_string "unconfigurable-delete")))
| red_expr_delete_field_3_found : forall c st st1 ptr obj attr s,
    attributes_configurable attr = true ->
    st1 = update_object st ptr (delete_object_property obj s) ->
    red_expr c st (expr_delete_field_3 ptr obj (Some attr) s) (out_ter st1 (res_value value_true))

| red_expr_own_field_names : forall c st e o o',
    red_expr c st e o ->
    red_expr c st (expr_own_field_names_1 o) o' ->
    red_expr c st (expr_own_field_names e) o'
| red_expr_own_field_names_1 : forall c st' st st1 ptr obj v,
    get_object st ptr = Some obj ->
    (st1, v) = add_object st (make_prop_list obj) ->
    red_expr c st' (expr_own_field_names_1 (out_ter st (res_value (value_object ptr)))) (out_ter st1 (res_value v))
| red_expr_own_field_names_1_abort : forall c st o,
    abort o ->
    red_expr c st (expr_own_field_names_1 o) o

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
| red_expr_app_2 : forall c c' c'' st st' v ci c is e vl vll o,
    v = value_closure ci c' is e ->
    (st', vll) = add_values st (rev vl) ->
    add_parameters c' is vll = result_some c'' ->
    red_expr c'' st e o ->
    red_expr c st (expr_app_2 v vl nil) o 
| red_expr_app_2_next : forall c st v vl e el o o',
    red_expr c st e o ->
    red_expr c st (expr_app_3 v vl o el) o' ->
    red_expr c st (expr_app_2 v vl (e :: el)) o'
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

