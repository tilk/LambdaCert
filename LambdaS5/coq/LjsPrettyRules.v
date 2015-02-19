Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import JsNumber.
Require Import Coq.Strings.String.
Import List.ListNotations.

Open Scope list_scope.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Inductive red_expr : ctx -> store -> ext_expr -> out -> Prop :=
| red_expr_null : forall c st, red_expr c st expr_null (out_ter st (res_value value_null))
| red_expr_undefined : forall c st, red_expr c st expr_undefined (out_ter st (res_value value_undefined))
| red_expr_string : forall c st s, red_expr c st (expr_string s) (out_ter st (res_value (value_string s)))
| red_expr_number : forall c st n, red_expr c st (expr_number n) (out_ter st (res_value (value_number n)))
| red_expr_true : forall c st, red_expr c st expr_true (out_ter st (res_value value_true))
| red_expr_false : forall c st, red_expr c st expr_false (out_ter st (res_value value_false))
| red_expr_id : forall c st i v, 
    get_value c i = Some v -> 
    red_expr c st (expr_id i) (out_ter st (res_value v))
| red_expr_lambda : forall c st args body v,
    v = add_closure c None args body ->
    red_expr c st (expr_lambda args body) (out_ter st (res_value v))

(* eval_many *)
| red_expr_eval_many_1 : forall c st vs E o,
    red_expr c st (E (rev vs)) o ->
    red_expr c st (expr_eval_many_1 nil vs E) o
| red_expr_eval_many_1_next : forall c st e es vs E o o',
    red_expr c st e o ->
    red_expr c st (expr_eval_many_2 es o vs E) o' ->
    red_expr c st (expr_eval_many_1 (e::es) vs E) o'
| red_expr_eval_many_2 : forall c st' st es v vs E o,
    red_expr c st (expr_eval_many_1 es (v::vs) E) o ->
    red_expr c st' (expr_eval_many_2 es (out_ter st (res_value v)) vs E) o
| red_expr_eval_many_2_abort : forall c st es vs E o,
    abort o ->
    red_expr c st (expr_eval_many_2 es o vs E) o

(* object *)
| red_expr_object : forall c st e1 e2 e3 e4 e5 a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4; e5] nil (expr_object_1 a)) o ->
    red_expr c st (expr_object (objattrs_intro e1 e2 e3 e4 e5) a) o
| red_expr_object_1 : forall c st class extv ext proto code prim a o,
    value_to_bool extv = Some ext ->
    red_expr c st (expr_object_2 (object_intro (oattrs_intro proto class ext prim code) Heap.empty) a) o ->
    red_expr c st (expr_object_1 a [value_string class; extv; proto; code; prim]) o
| red_expr_object_2 : forall c st st1 obj v,
    (st1, v) = add_object st obj ->
    red_expr c st (expr_object_2 obj nil) (out_ter st1 (res_value v))
| red_expr_object_2_data : forall c st obj s e1 e2 e3 e4 a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_data_1 obj a s)) o ->
    red_expr c st (expr_object_2 obj ((s, property_data (data_intro e3 e4 e2 e1)) :: a)) o
| red_expr_object_data_1 : forall c st obj a s v1 v2 v3 v4 b1 b2 b4 o,
    value_to_bool v1 = Some b1 ->
    value_to_bool v2 = Some b2 ->
    value_to_bool v4 = Some b4 ->
    red_expr c st (expr_object_2 (set_object_property obj s (attributes_data_of (attributes_data_intro v3 b4 b2 b1))) a) o ->
    red_expr c st (expr_object_data_1 obj a s [v1; v2; v3; v4]) o
| red_expr_object_2_accessor : forall c st obj s e1 e2 e3 e4 a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_accessor_1 obj a s)) o ->
    red_expr c st (expr_object_2 obj ((s, property_accessor (accessor_intro e3 e4 e2 e1)) :: a)) o
| red_expr_object_accessor_1 : forall c st obj a s v1 v2 v3 v4 b1 b2 o,
    value_to_bool v1 = Some b1 ->
    value_to_bool v2 = Some b2 ->
    red_expr c st (expr_object_2 (set_object_property obj s (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1))) a) o ->
    red_expr c st (expr_object_accessor_1 obj a s [v1; v2; v3; v4]) o

(* get_attr *)
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
| red_expr_get_attr_2 : forall c st' st pa s ptr obj v,
    get_object st ptr = Some obj ->
    get_object_pattr obj s pa = result_some v ->
    red_expr c st' (expr_get_attr_2 pa (value_object ptr) (out_ter st (res_value (value_string s)))) (out_ter st (res_value v))
| red_expr_get_attr_2_abort : forall c st pa v1 o,
    abort o ->
    red_expr c st (expr_get_attr_2 pa v1 o) o

(* set_attr *)
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
| red_expr_set_attr_3 : forall c st' st st1 pa ptr obj obj' s v,
    get_object st ptr = Some obj ->
    set_object_pattr obj s pa v = result_some obj' ->
    st1 = update_object st ptr obj' ->
    red_expr c st' (expr_set_attr_3 pa (value_object ptr) (value_string s) (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_expr_set_attr_3_abort : forall c st pa v1 v2 o,
    abort o ->
    red_expr c st (expr_set_attr_3 pa v1 v2 o) o

(* get_obj_attr *)
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

(* set_obj_attr *)
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

(* get_field *)
| red_expr_get_field : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_get_field_1 o e2) o' ->
    red_expr c st (expr_get_field e1 e2) o'
| red_expr_get_field_1 : forall c st' st v1 e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_get_field_2 v1 o) o' ->
    red_expr c st' (expr_get_field_1 (out_ter st (res_value v1)) e2) o'
| red_expr_get_field_1_abort : forall c st e2 o,
    abort o ->
    red_expr c st (expr_get_field_1 o e2) o
| red_expr_get_field_2 : forall c st' st ptr s oattr o,
    get_property st ptr s = result_some oattr ->
    red_expr c st (expr_get_field_3 ptr oattr) o ->
    red_expr c st' (expr_get_field_2 (value_object ptr) (out_ter st (res_value (value_string s)))) o
| red_expr_get_field_2_abort : forall c st v1 o,
    abort o ->
    red_expr c st (expr_get_field_2 v1 o) o
| red_expr_get_field_3_no_field : forall c st ptr,
    red_expr c st (expr_get_field_3 ptr None) (out_ter st (res_value value_undefined))
| red_expr_get_field_3_get_field : forall c st ptr data,
    red_expr c st (expr_get_field_3 ptr (Some (attributes_data_of data))) (out_ter st (res_value (attributes_data_value data)))
| red_expr_get_field_3_getter : forall c st ptr acc o,
    red_expr c st (expr_app_2 (attributes_accessor_get acc) [value_object ptr]) o ->
    red_expr c st (expr_get_field_3 ptr (Some (attributes_accessor_of acc))) o

(* set_field *)
| red_expr_set_field : forall c st e1 e2 e3 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_set_field_1 o e2 e3) o' ->
    red_expr c st (expr_set_field e1 e2 e3) o'
| red_expr_set_field_1 : forall c st' st v1 e2 e3 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_set_field_2 v1 o e3) o' ->
    red_expr c st' (expr_set_field_1 (out_ter st (res_value v1)) e2 e3) o'
| red_expr_set_field_1_abort : forall c st e2 e3 e4 o,
    abort o ->
    red_expr c st (expr_set_field_1 o e2 e3) o
| red_expr_set_field_2 : forall c st' st v1 v2 e3 o o',
    red_expr c st e3 o ->
    red_expr c st (expr_set_field_3 v1 v2 o) o' ->
    red_expr c st' (expr_set_field_2 v1 (out_ter st (res_value v2)) e3) o'
| red_expr_set_field_2_abort : forall c st v1 e3 o,
    abort o ->
    red_expr c st (expr_set_field_2 v1 o e3) o
| red_expr_set_field_3 : forall c st' st ptr obj oattr s v3 v4 o,
    get_property st ptr s = result_some oattr ->
    get_object st ptr = Some obj ->
    red_expr c st (expr_set_field_4 ptr obj oattr s v3) o ->
    red_expr c st' (expr_set_field_3 (value_object ptr) (value_string s) (out_ter st (res_value v3))) o
| red_expr_set_field_3_abort : forall c st v1 v2 o,
    abort o ->
    red_expr c st (expr_set_field_3 v1 v2 o) o
| red_expr_set_field_4_set_field : forall c st st1 ptr obj data s v3,
    get_object_property obj s <> None ->
    attributes_data_writable data = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_value_update data v3))) ->
    red_expr c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st1 (res_value v3))
| red_expr_set_field_4_shadow_field : forall c st st1 ptr obj data s v3,
    get_object_property obj s = None ->
    object_extensible obj = true ->
    attributes_data_writable data = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_expr c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st1 (res_value v3))
| red_expr_set_field_4_add_field : forall c st st1 ptr obj s v3,
    object_extensible obj = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_expr c st (expr_set_field_4 ptr obj None s v3) (out_ter st1 (res_value v3))
| red_expr_set_field_4_setter : forall c st ptr obj acc s v3 o,
    red_expr c st (expr_app_2 (attributes_accessor_set acc) [value_object ptr; v3]) o ->
    red_expr c st (expr_set_field_4 ptr obj (Some (attributes_accessor_of acc)) s v3) o
| red_expr_set_field_4_unwritable : forall c st ptr obj data s v3,
    attributes_data_writable data = false ->
    red_expr c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st (res_exception (value_string "unwritable-field")))
| red_expr_set_field_4_unextensible_add : forall c st ptr obj s v3,
    object_extensible obj = false ->
    red_expr c st (expr_set_field_4 ptr obj None s v3) (out_ter st (res_exception (value_string "unextensible-set")))
| red_expr_set_field_4_unextensible_shadow : forall c st ptr obj data s v3,
    attributes_data_writable data = true ->
    get_object_property obj s = None ->
    object_extensible obj = false ->
    red_expr c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st (res_exception (value_string "unextensible-shadow")))

(* delete_field *)
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

(* own_field_names *)
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

(* op1 *)
| red_expr_op1 : forall c st e op o o',
    red_expr c st e o ->
    red_expr c st (expr_op1_1 op o) o' ->
    red_expr c st (expr_op1 op e) o'
| red_expr_op1_1 : forall c st' st op v v',
    unary_operator op st v = result_some v' ->
    red_expr c st' (expr_op1_1 op (out_ter st (res_value v))) (out_ter st (res_value v'))
| red_expr_op1_1_abort : forall c st op o,
    abort o ->
    red_expr c st (expr_op1_1 op o) o

(* op2 *)
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
    binary_operator op st v1 v2 = result_some v ->
    red_expr c st' (expr_op2_2 op v1 (out_ter st (res_value v2))) (out_ter st (res_value v))
| red_expr_op2_2_abort : forall c st op v o,
    abort o ->
    red_expr c st (expr_op2_2 op v o) o

(* if *)
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
    red_expr c st (expr_eval_many_1 el nil (expr_app_2 v)) o ->
    red_expr c st' (expr_app_1 (out_ter st (res_value v)) el) o
| red_expr_app_1_abort : forall c st o el,
    abort o ->
    red_expr c st (expr_app_1 o el) o
| red_expr_app_2 : forall c c' st v clo vl o,
    get_closure st v = result_some (value_closure clo) ->
    closure_ctx clo vl = result_some c' ->
    red_expr c' st (closure_body clo) o ->
    red_expr c st (expr_app_2 v vl) o 

(* seq *)
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

(* let *)
| red_expr_let : forall c st i e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_let_1 i o e2) o' ->
    red_expr c st (expr_let i e1 e2) o'
| red_expr_let_1 : forall c c' st' st i v e2 o,
    c' = add_value c i v ->
    red_expr c' st e2 o ->
    red_expr c st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_expr_let_1_abort : forall c st i o e2,
    abort o ->
    red_expr c st (expr_let_1 i o e2) o

(* rec *)
| red_expr_rec : forall c c' st i args body v e2 o,
    v = add_closure c (Some i) args body ->
    c' = add_value c i v ->
    red_expr c' st e2 o ->
    red_expr c st (expr_recc i (expr_lambda args body) e2) o

(* label *)
| red_expr_label : forall c st i e o o',
    red_expr c st e o ->
    red_expr c st (expr_label_1 i o) o' ->
    red_expr c st (expr_label i e) o'
| red_expr_label_1 : forall c st' i o,
    (forall st v, o <> out_ter st (res_break i v)) ->
    red_expr c st' (expr_label_1 i o) o
| red_expr_label_1_break : forall c st' st i v,
    red_expr c st' (expr_label_1 i (out_ter st (res_break i v))) (out_ter st (res_value v))

(* break *)
| red_expr_break : forall c st i e o o',
    red_expr c st e o ->
    red_expr c st (expr_break_1 i o) o' ->
    red_expr c st (expr_break i e) o'
| red_expr_break_1 : forall c st' st i v,
    red_expr c st' (expr_break_1 i (out_ter st (res_value v))) (out_ter st (res_break i v))
| red_expr_break_1_abort : forall c st i o,
    abort o ->
    red_expr c st (expr_break_1 i o) o

(* try_catch *)
| red_expr_try_catch : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_try_catch_1 o e2) o' ->
    red_expr c st (expr_try_catch e1 e2) o'
| red_expr_try_catch_1 : forall c st e2 o,
    (forall st v, o <> out_ter st (res_exception v)) -> (* TODO something better? *)
    red_expr c st (expr_try_catch_1 o e2) o
| red_expr_try_catch_1_exc : forall c st' st v e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_try_catch_2 v o) o' ->
    red_expr c st' (expr_try_catch_1 (out_ter st (res_exception v)) e2) o'
| red_expr_try_catch_2 : forall c st' st v v' o,
    red_expr c st (expr_app_2 v' [v]) o ->
    red_expr c st' (expr_try_catch_2 v (out_ter st (res_value v'))) o
| red_expr_try_catch_2_abort : forall c st v o,
    abort o ->
    red_expr c st (expr_try_catch_2 v o) o

(* try_finally *)
| red_expr_try_finally : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_try_finally_1 o e2) o' ->
    red_expr c st (expr_try_finally e1 e2) o'
| red_expr_try_finally_1 : forall c st' st r e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_try_finally_2 r o) o' ->
    red_expr c st' (expr_try_finally_1 (out_ter st r) e2) o'
| red_expr_try_finally_1_div : forall c st e2,
    red_expr c st (expr_try_finally_1 out_div e2) out_div
| red_expr_try_finally_2 : forall c st' st r v,
    red_expr c st' (expr_try_finally_2 r (out_ter st (res_value v))) (out_ter st r)
| red_expr_try_finally_2_abort : forall c st r o,
    abort o ->
    red_expr c st (expr_try_finally_2 r o) o

(* throw *)
| red_expr_throw : forall c st e o o',
    red_expr c st e o ->
    red_expr c st (expr_throw_1 o) o' ->
    red_expr c st (expr_throw e) o'
| red_expr_throw_1 : forall c st' st v,
    red_expr c st' (expr_throw_1 (out_ter st (res_value v))) (out_ter st (res_exception v))
| red_expr_throw_1_abort : forall c st o,
    abort o ->
    red_expr c st (expr_throw_1 o) o

(* eval *)
| red_expr_eval : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_eval_1 o e2) o' ->
    red_expr c st (expr_eval e1 e2) o' 
| red_expr_eval_1 : forall c st st' v1 e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_eval_2 v1 o) o' -> 
    red_expr c st' (expr_eval_1 (out_ter st (res_value v1)) e2) o'
| red_expr_eval_1_abort : forall c st e2 o,
    abort o ->
    red_expr c st (expr_eval_1 o e2) o
| red_expr_eval_2 : forall c c1 st' st s e ptr obj o,
    get_object st ptr = Some obj ->
    ctx_of_obj obj = Some c1 ->
    desugar_expr s = Some e ->
    red_expr c1 st e o ->
    red_expr c st' (expr_eval_2 (value_string s) (out_ter st (res_value (value_object ptr)))) o
| red_expr_eval_2_abort : forall c st v1 o,
    abort o ->
    red_expr c st (expr_eval_2 v1 o) o

(* hint *)
| red_expr_hint : forall c st s e o,
    red_expr c st e o ->
    red_expr c st (expr_hint s e) o 
.

