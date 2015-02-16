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
Implicit Type loc : value_loc.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

Inductive red_exprh : nat -> ctx -> store -> ext_expr -> out -> Prop :=
| red_exprh_null : forall k c st, red_exprh (S k) c st expr_null (out_ter st (res_value value_null))
| red_exprh_undefined : forall k c st, red_exprh (S k) c st expr_undefined (out_ter st (res_value value_undefined))
| red_exprh_string : forall k c st s, red_exprh (S k) c st (expr_string s) (out_ter st (res_value (value_string s)))
| red_exprh_number : forall k c st n, red_exprh (S k) c st (expr_number n) (out_ter st (res_value (value_number n)))
| red_exprh_true : forall k c st, red_exprh (S k) c st expr_true (out_ter st (res_value value_true))
| red_exprh_false : forall k c st, red_exprh (S k) c st expr_false (out_ter st (res_value value_false))
| red_exprh_id : forall k c st i loc v, 
    get_loc c i = Some loc -> 
    get_value st loc = Some v -> 
    red_exprh (S k) c st (expr_id i) (out_ter st (res_value v))
| red_exprh_lambda : forall k c st st' args body v,
    (st', v) = add_closure c st args body ->
    red_exprh (S k) c st (expr_lambda args body) (out_ter st' (res_value v))

(* object *)
| red_exprh_object : forall k c st e1 e2 e3 e4 e5 a o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_object_1 o e2 e3 e4 e5 a) o' ->
    red_exprh (S k) c st (expr_object (objattrs_intro e1 e2 e3 e4 e5) a) o'
| red_exprh_object_1 : forall k c st' st v1 e2 e3 e4 e5 a o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_object_2 v1 o e3 e4 e5 a) o' ->
    red_exprh k c st' (expr_object_1 (out_ter st (res_value v1)) e2 e3 e4 e5 a) o'
| red_exprh_object_1_abort : forall k c st e2 e3 e4 e5 a o,
    abort o ->
    red_exprh k c st (expr_object_1 o e2 e3 e4 e5 a) o
| red_exprh_object_2 : forall k c st' st v1 v2 e3 e4 e5 a o o',
    red_exprh k c st e3 o ->
    red_exprh k c st (expr_object_3 v1 v2 o e4 e5 a) o' ->
    red_exprh k c st' (expr_object_2 v1 (out_ter st (res_value v2)) e3 e4 e5 a) o'
| red_exprh_object_2_abort : forall k c st v1 e3 e4 e5 a o,
    abort o ->
    red_exprh k c st (expr_object_2 v1 o e3 e4 e5 a) o
| red_exprh_object_3 : forall k c st' st v1 v2 v3 e4 e5 a o o',
    red_exprh k c st e4 o ->
    red_exprh k c st (expr_object_4 v1 v2 v3 o e5 a) o' ->
    red_exprh k c st' (expr_object_3 v1 v2 (out_ter st (res_value v3)) e4 e5 a) o'
| red_exprh_object_3_abort : forall k c st v1 v2 e4 e5 a o,
    abort o ->
    red_exprh k c st (expr_object_3 v1 v2 o e4 e5 a) o
| red_exprh_object_4 : forall k c st' st v1 v2 v3 v4 e5 a o o',
    red_exprh k c st e5 o ->
    red_exprh k c st (expr_object_5 v1 v2 v3 v4 o a) o' ->
    red_exprh k c st' (expr_object_4 v1 v2 v3 (out_ter st (res_value v4)) e5 a) o'
| red_exprh_object_4_abort : forall k c st v1 v2 v3 e5 a o,
    abort o ->
    red_exprh k c st (expr_object_4 v1 v2 v3 o e5 a) o
| red_exprh_object_5 : forall k c st' st class extv ext proto code prim a o,
    value_to_bool extv = Some ext ->
    red_exprh k c st (expr_object_6 (object_intro proto class ext prim Heap.empty code) a) o ->
    red_exprh k c st' (expr_object_5 (value_string class) extv proto code (out_ter st (res_value prim)) a) o
| red_exprh_object_5_abort : forall k c st v1 v2 v3 v4 a o,
    abort o ->
    red_exprh k c st (expr_object_5 v1 v2 v3 v4 o a) o
| red_exprh_object_6 : forall k c st st1 obj v,
    (st1, v) = add_object st obj ->
    red_exprh k c st (expr_object_6 obj nil) (out_ter st1 (res_value v))
| red_exprh_object_6_data : forall k c st obj s e1 e2 e3 e4 a o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_object_data_1 obj a s o e2 e3 e4) o' ->
    red_exprh k c st (expr_object_6 obj ((s, property_data (data_intro e3 e4 e2 e1)) :: a)) o'
| red_exprh_object_data_1 : forall k c st' st obj a s v1 e2 e3 e4 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_object_data_2 obj a s v1 o e3 e4) o' ->
    red_exprh k c st' (expr_object_data_1 obj a s (out_ter st (res_value v1)) e2 e3 e4) o'
| red_exprh_object_data_1_abort : forall k c st obj a s e2 e3 e4 o,
    abort o ->
    red_exprh k c st (expr_object_data_1 obj a s o e2 e3 e4) o
| red_exprh_object_data_2 : forall k c st' st obj a s v1 v2 e3 e4 o o',
    red_exprh k c st e3 o ->
    red_exprh k c st (expr_object_data_3 obj a s v1 v2 o e4) o' ->
    red_exprh k c st' (expr_object_data_2 obj a s v1 (out_ter st (res_value v2)) e3 e4) o'
| red_exprh_object_data_2_abort : forall k c st obj a s v1 e3 e4 o,
    abort o ->
    red_exprh k c st (expr_object_data_2 obj a s v1 o e3 e4) o
| red_exprh_object_data_3 : forall k c st' st obj a s v1 v2 v3 e4 o o',
    red_exprh k c st e4 o ->
    red_exprh k c st (expr_object_data_4 obj a s v1 v2 v3 o) o' ->
    red_exprh k c st' (expr_object_data_3 obj a s v1 v2 (out_ter st (res_value v3)) e4) o'
| red_exprh_object_data_3_abort : forall k c st obj a s v1 v2 e4 o,
    abort o ->
    red_exprh k c st (expr_object_data_3 obj a s v1 v2 o e4) o
| red_exprh_object_data_4 : forall k c st' st obj a s v1 v2 v3 v4 b1 b2 b4 o,
    value_to_bool v1 = Some b1 ->
    value_to_bool v2 = Some b2 ->
    value_to_bool v4 = Some b4 ->
    red_exprh k c st (expr_object_6 (set_object_property obj s (attributes_data_of (attributes_data_intro v3 b4 b2 b1))) a) o ->
    red_exprh k c st' (expr_object_data_4 obj a s v1 v2 v3 (out_ter st (res_value v4))) o
| red_exprh_object_data_4_abort : forall k c st obj a s v1 v2 v3 o,
    abort o ->
    red_exprh k c st (expr_object_data_4 obj a s v1 v2 v3 o) o
| red_exprh_object_6_accessor : forall k c st obj s e1 e2 e3 e4 a o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_object_accessor_1 obj a s o e2 e3 e4) o' ->
    red_exprh k c st (expr_object_6 obj ((s, property_accessor (accessor_intro e3 e4 e2 e1)) :: a)) o'
| red_exprh_object_accessor_1 : forall k c st' st obj a s v1 e2 e3 e4 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_object_accessor_2 obj a s v1 o e3 e4) o' ->
    red_exprh k c st' (expr_object_accessor_1 obj a s (out_ter st (res_value v1)) e2 e3 e4) o'
| red_exprh_object_accessor_1_abort : forall k c st obj a s e2 e3 e4 o,
    abort o ->
    red_exprh k c st (expr_object_accessor_1 obj a s o e2 e3 e4) o
| red_exprh_object_accessor_2 : forall k c st' st obj a s v1 v2 e3 e4 o o',
    red_exprh k c st e3 o ->
    red_exprh k c st (expr_object_accessor_3 obj a s v1 v2 o e4) o' ->
    red_exprh k c st' (expr_object_accessor_2 obj a s v1 (out_ter st (res_value v2)) e3 e4) o'
| red_exprh_object_accessor_2_abort : forall k c st obj a s v1 e3 e4 o,
    abort o ->
    red_exprh k c st (expr_object_accessor_2 obj a s v1 o e3 e4) o
| red_exprh_object_accessor_3 : forall k c st' st obj a s v1 v2 v3 e4 o o',
    red_exprh k c st e4 o ->
    red_exprh k c st (expr_object_accessor_4 obj a s v1 v2 v3 o) o' ->
    red_exprh k c st' (expr_object_accessor_3 obj a s v1 v2 (out_ter st (res_value v3)) e4) o'
| red_exprh_object_accessor_3_abort : forall k c st obj a s v1 v2 e4 o,
    abort o ->
    red_exprh k c st (expr_object_accessor_3 obj a s v1 v2 o e4) o
| red_exprh_object_accessor_4 : forall k c st' st obj a s v1 v2 v3 v4 b1 b2 o,
    value_to_bool v1 = Some b1 ->
    value_to_bool v2 = Some b2 ->
    red_exprh k c st (expr_object_6 (set_object_property obj s (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1))) a) o ->
    red_exprh k c st' (expr_object_accessor_4 obj a s v1 v2 v3 (out_ter st (res_value v4))) o
| red_exprh_object_accessor_4_abort : forall k c st obj a s v1 v2 v3 o,
    abort o ->
    red_exprh k c st (expr_object_accessor_4 obj a s v1 v2 v3 o) o

(* get_attr *)
| red_exprh_get_attr : forall k c st pa e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_get_attr_1 pa o e2) o' ->
    red_exprh (S k) c st (expr_get_attr pa e1 e2) o'
| red_exprh_get_attr_1 : forall k c st' st pa v1 e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_get_attr_2 pa v1 o) o' ->
    red_exprh k c st' (expr_get_attr_1 pa (out_ter st (res_value v1)) e2) o'
| red_exprh_get_attr_1_abort : forall k c st pa e2 o,
    abort o ->
    red_exprh k c st (expr_get_attr_1 pa o e2) o
| red_exprh_get_attr_2 : forall k c st' st pa s ptr obj v,
    get_object st ptr = Some obj ->
    get_object_pattr obj s pa = result_some v ->
    red_exprh k c st' (expr_get_attr_2 pa (value_object ptr) (out_ter st (res_value (value_string s)))) (out_ter st (res_value v))
| red_exprh_get_attr_2_abort : forall k c st pa v1 o,
    abort o ->
    red_exprh k c st (expr_get_attr_2 pa v1 o) o

(* set_attr *)
| red_exprh_set_attr : forall k c st pa e1 e2 e3 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_set_attr_1 pa o e2 e3) o' ->
    red_exprh (S k) c st (expr_set_attr pa e1 e2 e3) o'
| red_exprh_set_attr_1 : forall k c st' st pa v1 e2 e3 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_set_attr_2 pa v1 o e3) o' ->
    red_exprh k c st' (expr_set_attr_1 pa (out_ter st (res_value v1)) e2 e3) o'
| red_exprh_set_attr_1_abort : forall k c st pa e2 e3 o,
    abort o ->
    red_exprh k c st (expr_set_attr_1 pa o e2 e3) o
| red_exprh_set_attr_2 : forall k c st' st pa v1 v2 e3 o o',
    red_exprh k c st e3 o ->
    red_exprh k c st (expr_set_attr_3 pa v1 v2 o) o' ->
    red_exprh k c st' (expr_set_attr_2 pa v1 (out_ter st (res_value v2)) e3) o'
| red_exprh_set_attr_2_abort : forall k c st pa v1 e3 o,
    abort o ->
    red_exprh k c st (expr_set_attr_2 pa v1 o e3) o
| red_exprh_set_attr_3 : forall k c st' st st1 pa ptr obj obj' s v,
    get_object st ptr = Some obj ->
    set_object_pattr obj s pa v = result_some obj' ->
    st1 = update_object st ptr obj' ->
    red_exprh k c st' (expr_set_attr_3 pa (value_object ptr) (value_string s) (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_exprh_set_attr_3_abort : forall k c st pa v1 v2 o,
    abort o ->
    red_exprh k c st (expr_set_attr_3 pa v1 v2 o) o

(* get_obj_attr *)
| red_exprh_get_obj_attr : forall k c st oa e1 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_get_obj_attr_1 oa o) o' ->
    red_exprh (S k) c st (expr_get_obj_attr oa e1) o'
| red_exprh_get_obj_attr_1 : forall k c st' st oa ptr obj,
    get_object st ptr = Some obj ->
    red_exprh k c st' (expr_get_obj_attr_1 oa (out_ter st (res_value (value_object ptr)))) (out_ter st (res_value (get_object_oattr obj oa)))
| red_exprh_get_obj_attr_1_abort : forall k c st oa o,
    abort o ->
    red_exprh k c st (expr_get_obj_attr_1 oa o) o

(* set_obj_attr *)
| red_exprh_set_obj_attr : forall k c st oa e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_set_obj_attr_1 oa o e2) o' ->
    red_exprh (S k) c st (expr_set_obj_attr oa e1 e2) o'
| red_exprh_set_obj_attr_1 : forall k c st' st oa v1 e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_set_obj_attr_2 oa v1 o) o' ->
    red_exprh k c st' (expr_set_obj_attr_1 oa (out_ter st (res_value v1)) e2) o'
| red_exprh_set_obj_attr_1_abort : forall k c st oa e2 o,
    abort o ->
    red_exprh k c st (expr_set_obj_attr_1 oa o e2) o
| red_exprh_set_obj_attr_2 : forall k c st' st st1 oa ptr obj obj' v,
    get_object st ptr = Some obj ->
    set_object_oattr obj oa v = result_some obj' ->
    st1 = update_object st ptr obj' ->
    red_exprh k c st' (expr_set_obj_attr_2 oa (value_object ptr) (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_exprh_set_obj_attr_2_abort : forall k c st oa v1 o,
    abort o ->
    red_exprh k c st (expr_set_obj_attr_2 oa v1 o) o

(* get_field *)
| red_exprh_get_field : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_get_field_1 o e2) o' ->
    red_exprh (S k) c st (expr_get_field e1 e2) o'
| red_exprh_get_field_1 : forall k c st' st v1 e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_get_field_2 v1 o) o' ->
    red_exprh k c st' (expr_get_field_1 (out_ter st (res_value v1)) e2) o'
| red_exprh_get_field_1_abort : forall k c st e2 o,
    abort o ->
    red_exprh k c st (expr_get_field_1 o e2) o
| red_exprh_get_field_2 : forall k c st' st ptr s oattr o,
    get_property st ptr s = result_some oattr ->
    red_exprh k c st (expr_get_field_3 ptr oattr) o ->
    red_exprh k c st' (expr_get_field_2 (value_object ptr) (out_ter st (res_value (value_string s)))) o
| red_exprh_get_field_2_abort : forall k c st v1 o,
    abort o ->
    red_exprh k c st (expr_get_field_2 v1 o) o
| red_exprh_get_field_3_no_field : forall k c st ptr,
    red_exprh k c st (expr_get_field_3 ptr None) (out_ter st (res_value value_undefined))
| red_exprh_get_field_3_get_field : forall k c st ptr data,
    red_exprh k c st (expr_get_field_3 ptr (Some (attributes_data_of data))) (out_ter st (res_value (attributes_data_value data)))
| red_exprh_get_field_3_getter : forall k c st st' ptr v3 acc o,
    (st', v3) = add_object st (default_object) ->
    red_exprh k c st' (expr_app_2 (attributes_accessor_get acc) [v3; value_object ptr] nil) o ->
    red_exprh k c st (expr_get_field_3 ptr (Some (attributes_accessor_of acc))) o

(* set_field *)
| red_exprh_set_field : forall k c st e1 e2 e3 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_set_field_1 o e2 e3) o' ->
    red_exprh (S k) c st (expr_set_field e1 e2 e3) o'
| red_exprh_set_field_1 : forall k c st' st v1 e2 e3 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_set_field_2 v1 o e3) o' ->
    red_exprh k c st' (expr_set_field_1 (out_ter st (res_value v1)) e2 e3) o'
| red_exprh_set_field_1_abort : forall k c st e2 e3 e4 o,
    abort o ->
    red_exprh k c st (expr_set_field_1 o e2 e3) o
| red_exprh_set_field_2 : forall k c st' st v1 v2 e3 o o',
    red_exprh k c st e3 o ->
    red_exprh k c st (expr_set_field_3 v1 v2 o) o' ->
    red_exprh k c st' (expr_set_field_2 v1 (out_ter st (res_value v2)) e3) o'
| red_exprh_set_field_2_abort : forall k c st v1 e3 o,
    abort o ->
    red_exprh k c st (expr_set_field_2 v1 o e3) o
| red_exprh_set_field_3 : forall k c st' st ptr obj oattr s v3 v4 o,
    get_property st ptr s = result_some oattr ->
    get_object st ptr = Some obj ->
    red_exprh k c st (expr_set_field_4 ptr obj oattr s v3) o ->
    red_exprh k c st' (expr_set_field_3 (value_object ptr) (value_string s) (out_ter st (res_value v3))) o
| red_exprh_set_field_3_abort : forall k c st v1 v2 o,
    abort o ->
    red_exprh k c st (expr_set_field_3 v1 v2 o) o
| red_exprh_set_field_4_set_field : forall k c st st1 ptr obj data s v3,
    get_object_property obj s <> None ->
    attributes_data_writable data = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_value_update data v3))) ->
    red_exprh k c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st1 (res_value v3))
| red_exprh_set_field_4_shadow_field : forall k c st st1 ptr obj data s v3,
    get_object_property obj s = None ->
    object_extensible obj = true ->
    attributes_data_writable data = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_exprh k c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st1 (res_value v3))
| red_exprh_set_field_4_add_field : forall k c st st1 ptr obj s v3,
    object_extensible obj = true ->
    st1 = update_object st ptr (set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_exprh k c st (expr_set_field_4 ptr obj None s v3) (out_ter st1 (res_value v3))
| red_exprh_set_field_4_setter : forall k c st st' ptr obj acc s v3 v4 o,
    (st', v4) = add_object st (object_with_properties 
                      (Heap.write Heap.empty "0" (attributes_data_of 
                        (attributes_data_intro v3 true false false))) default_object) ->
    red_exprh k c st' (expr_app_2 (attributes_accessor_set acc) [v4; value_object ptr] nil) o ->
    red_exprh k c st (expr_set_field_4 ptr obj (Some (attributes_accessor_of acc)) s v3) o
| red_exprh_set_field_4_unwritable : forall k c st ptr obj data s v3,
    attributes_data_writable data = false ->
    red_exprh k c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st (res_exception (value_string "unwritable-field")))
| red_exprh_set_field_4_unextensible_add : forall k c st ptr obj s v3,
    object_extensible obj = false ->
    red_exprh k c st (expr_set_field_4 ptr obj None s v3) (out_ter st (res_value value_undefined))
| red_exprh_set_field_4_unextensible_shadow : forall k c st ptr obj data s v3,
    attributes_data_writable data = true ->
    get_object_property obj s = None ->
    object_extensible obj = false ->
    red_exprh k c st (expr_set_field_4 ptr obj (Some (attributes_data_of data)) s v3) (out_ter st (res_value value_undefined))

(* delete_field *)
| red_exprh_delete_field : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_delete_field_1 o e2) o' ->
    red_exprh (S k) c st (expr_delete_field e1 e2) o'
| red_exprh_delete_field_1 : forall k c st' st v1 e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_delete_field_2 v1 o) o' ->
    red_exprh k c st' (expr_delete_field_1 (out_ter st (res_value v1)) e2) o'
| red_exprh_delete_field_1_abort : forall k c st e2 o,
    abort o ->
    red_exprh k c st (expr_delete_field_1 o e2) o
| red_exprh_delete_field_2 : forall k c st' st ptr s obj oattr o,
    get_object st ptr = Some obj ->
    get_object_property obj s = oattr ->
    red_exprh k c st (expr_delete_field_3 ptr obj oattr s) o ->
    red_exprh k c st' (expr_delete_field_2 (value_object ptr) (out_ter st (res_value (value_string s)))) o
| red_exprh_delete_field_2_abort : forall k c st v1 o,
    abort o ->
    red_exprh k c st (expr_delete_field_2 v1 o) o
| red_exprh_delete_field_3_not_found : forall k c st ptr obj s,
    red_exprh k c st (expr_delete_field_3 ptr obj None s) (out_ter st (res_value value_false))
| red_exprh_delete_field_3_unconfigurable : forall k c st ptr obj attr s,
    attributes_configurable attr = false ->
    red_exprh k c st (expr_delete_field_3 ptr obj (Some attr) s) (out_ter st (res_exception (value_string "unconfigurable-delete")))
| red_exprh_delete_field_3_found : forall k c st st1 ptr obj attr s,
    attributes_configurable attr = true ->
    st1 = update_object st ptr (delete_object_property obj s) ->
    red_exprh k c st (expr_delete_field_3 ptr obj (Some attr) s) (out_ter st1 (res_value value_true))

(* own_field_names *)
| red_exprh_own_field_names : forall k c st e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_own_field_names_1 o) o' ->
    red_exprh (S k) c st (expr_own_field_names e) o'
| red_exprh_own_field_names_1 : forall k c st' st st1 ptr obj v,
    get_object st ptr = Some obj ->
    (st1, v) = add_object st (make_prop_list obj) ->
    red_exprh k c st' (expr_own_field_names_1 (out_ter st (res_value (value_object ptr)))) (out_ter st1 (res_value v))
| red_exprh_own_field_names_1_abort : forall k c st o,
    abort o ->
    red_exprh k c st (expr_own_field_names_1 o) o

(* set_bang *)
| red_exprh_set_bang : forall k c st i e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_set_bang_1 i o) o' ->
    red_exprh (S k) c st (expr_set_bang i e) o'
| red_exprh_set_bang_1 : forall k c st' st st1 i loc v,
    st1 = add_value_at_location st loc v ->
    get_loc c i = Some loc -> 
    red_exprh k c st' (expr_set_bang_1 i (out_ter st (res_value v))) (out_ter st1 (res_value v))
| red_exprh_set_bang_1_abort : forall k c st i o,
    abort o ->
    red_exprh k c st (expr_set_bang_1 i o) o

(* op1 *)
| red_exprh_op1 : forall k c st e op o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_op1_1 op o) o' ->
    red_exprh (S k) c st (expr_op1 op e) o'
| red_exprh_op1_1 : forall k c st' st op v v',
    unary_operator op st v = result_some v' ->
    red_exprh k c st' (expr_op1_1 op (out_ter st (res_value v))) (out_ter st (res_value v'))
| red_exprh_op1_1_abort : forall k c st op o,
    abort o ->
    red_exprh k c st (expr_op1_1 op o) o

(* op2 *)
| red_exprh_op2 : forall k c st e1 e2 op o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_op2_1 op o e2) o' ->
    red_exprh (S k) c st (expr_op2 op e1 e2) o'
| red_exprh_op2_1 : forall k c st' st e2 op v o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_op2_2 op v o) o' ->
    red_exprh k c st' (expr_op2_1 op (out_ter st (res_value v)) e2) o'
| red_exprh_op2_1_abort : forall k c st op e2 o,
    abort o ->
    red_exprh k c st (expr_op2_1 op o e2) o
| red_exprh_op2_2 : forall k c st' st op v1 v2 v,
    binary_operator op st v1 v2 = result_some v ->
    red_exprh k c st' (expr_op2_2 op v1 (out_ter st (res_value v2))) (out_ter st (res_value v))
| red_exprh_op2_2_abort : forall k c st op v o,
    abort o ->
    red_exprh k c st (expr_op2_2 op v o) o

(* if *)
| red_exprh_if : forall k c st e e1 e2 o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_if_1 o e1 e2) o' ->
    red_exprh (S k) c st (expr_if e e1 e2) o'
| red_exprh_if_1_true : forall k c st' st e1 e2 o,
    red_exprh k c st e1 o ->
    red_exprh k c st' (expr_if_1 (out_ter st (res_value value_true)) e1 e2) o
| red_exprh_if_1_false : forall k c st' st e1 e2 o,
    red_exprh k c st e2 o ->
    red_exprh k c st' (expr_if_1 (out_ter st (res_value value_false)) e1 e2) o (* TODO: not-true-is-false? *)
| red_exprh_if_1_abort : forall k c st e1 e2 o,
    abort o ->
    red_exprh k c st (expr_if_1 o e1 e2) o

(* app *)
| red_exprh_app : forall k c st e el o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_app_1 o el) o' ->
    red_exprh (S k) c st (expr_app e el) o'
| red_exprh_app_1 : forall k c st' st v el o,
    red_exprh k c st (expr_app_2 v nil el) o ->
    red_exprh k c st' (expr_app_1 (out_ter st (res_value v)) el) o
| red_exprh_app_1_abort : forall k c st o el,
    abort o ->
    red_exprh k c st (expr_app_1 o el) o
| red_exprh_app_2 : forall k c c' c'' st st' v ci is e vl vll o,
    get_closure st v = result_some (value_closure ci c' is e) ->
    (st', vll) = add_values st (rev vl) ->
    add_parameters c' is vll = result_some c'' ->
    red_exprh k c'' st' e o ->
    red_exprh k c st (expr_app_2 v vl nil) o 
| red_exprh_app_2_next : forall k c st v vl e el o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_app_3 v vl o el) o' ->
    red_exprh k c st (expr_app_2 v vl (e :: el)) o'
| red_exprh_app_3 : forall k c st' st v vl v' el o,
    red_exprh k c st (expr_app_2 v (v' :: vl) el) o ->
    red_exprh k c st' (expr_app_3 v vl (out_ter st (res_value v')) el) o
| red_exprh_app_3_abort : forall k c st v vl el o,
    abort o ->
    red_exprh k c st (expr_app_3 v vl o el) o

(* seq *)
| red_exprh_seq : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_seq_1 o e2) o' ->
    red_exprh (S k) c st (expr_seq e1 e2) o'
| red_exprh_seq_1 : forall k c st' st v e2 o,
    red_exprh k c st e2 o ->
    red_exprh k c st' (expr_seq_1 (out_ter st (res_value v)) e2) o
| red_exprh_seq_1_abort : forall k c st e2 o,
    abort o ->
    red_exprh k c st (expr_seq_1 o e2) o

(* let *)
| red_exprh_let : forall k c st i e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_let_1 i o e2) o' ->
    red_exprh (S k) c st (expr_let i e1 e2) o'
| red_exprh_let_1 : forall k c c1 st' st st1 i v e2 o,
    (c1, st1) = add_named_value c st i v ->
    red_exprh k c1 st1 e2 o ->
    red_exprh k c st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_exprh_let_1_abort : forall k c st i o e2,
    abort o ->
    red_exprh k c st (expr_let_1 i o e2) o

(* rec *)
| red_exprh_rec : forall k c c1 st st1 loc i e1 e2 o o',
    (c1, st1, loc) = add_named_value_loc c st i value_undefined ->
    red_exprh k c1 st1 e1 o ->
    red_exprh k c1 st1 (expr_recc_1 loc o e2) o' ->
    red_exprh (S k) c st (expr_recc i e1 e2) o'
| red_exprh_rec_1 : forall k c st' st st1 loc v e2 o,
    st1 = add_value_at_location st loc v ->
    red_exprh k c st1 e2 o ->
    red_exprh k c st' (expr_recc_1 loc (out_ter st (res_value v)) e2) o
| red_exprh_rec_1_abort : forall k c st loc o e2,
    abort o ->
    red_exprh k c st (expr_recc_1 loc o e2) o

(* label *)
| red_exprh_label : forall k c st i e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_label_1 i o) o' ->
    red_exprh (S k) c st (expr_label i e) o'
| red_exprh_label_1 : forall k c st' i o,
    (forall st v, o <> out_ter st (res_break i v)) ->
    red_exprh k c st' (expr_label_1 i o) o
| red_exprh_label_1_break : forall k c st' st i v,
    red_exprh k c st' (expr_label_1 i (out_ter st (res_break i v))) (out_ter st (res_value v))

(* break *)
| red_exprh_break : forall k c st i e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_break_1 i o) o' ->
    red_exprh (S k) c st (expr_break i e) o'
| red_exprh_break_1 : forall k c st' st i v,
    red_exprh k c st' (expr_break_1 i (out_ter st (res_value v))) (out_ter st (res_break i v))
| red_exprh_break_1_abort : forall k c st i o,
    abort o ->
    red_exprh k c st (expr_break_1 i o) o

(* try_catch *)
| red_exprh_try_catch : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_try_catch_1 o e2) o' ->
    red_exprh (S k) c st (expr_try_catch e1 e2) o'
| red_exprh_try_catch_1 : forall k c st e2 o,
    (forall st v, o <> out_ter st (res_exception v)) -> (* TODO something better? *)
    red_exprh k c st (expr_try_catch_1 o e2) o
| red_exprh_try_catch_1_exc : forall k c st' st v e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_try_catch_2 v o) o' ->
    red_exprh k c st' (expr_try_catch_1 (out_ter st (res_exception v)) e2) o'
| red_exprh_try_catch_2 : forall k c st' st v v' o,
    red_exprh k c st (expr_app_2 v' [v] nil) o ->
    red_exprh k c st' (expr_try_catch_2 v (out_ter st (res_value v'))) o
| red_exprh_try_catch_2_abort : forall k c st v o,
    abort o ->
    red_exprh k c st (expr_try_catch_2 v o) o

(* try_finally *)
| red_exprh_try_finally : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_try_finally_1 o e2) o' ->
    red_exprh (S k) c st (expr_try_finally e1 e2) o'
| red_exprh_try_finally_1 : forall k c st' st r e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_try_finally_2 r o) o' ->
    red_exprh k c st' (expr_try_finally_1 (out_ter st r) e2) o'
| red_exprh_try_finally_1_div : forall k c st e2,
    red_exprh k c st (expr_try_finally_1 out_div e2) out_div
| red_exprh_try_finally_2 : forall k c st' st r v,
    red_exprh k c st' (expr_try_finally_2 r (out_ter st (res_value v))) (out_ter st r)
| red_exprh_try_finally_2_abort : forall k c st r o,
    abort o ->
    red_exprh k c st (expr_try_finally_2 r o) o

(* throw *)
| red_exprh_throw : forall k c st e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_throw_1 o) o' ->
    red_exprh (S k) c st (expr_throw e) o'
| red_exprh_throw_1 : forall k c st' st v,
    red_exprh k c st' (expr_throw_1 (out_ter st (res_value v))) (out_ter st (res_exception v))
| red_exprh_throw_1_abort : forall k c st o,
    abort o ->
    red_exprh k c st (expr_throw_1 o) o

(* eval *)
| red_exprh_eval : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_eval_1 o e2) o' ->
    red_exprh (S k) c st (expr_eval e1 e2) o' 
| red_exprh_eval_1 : forall k c st st' v1 e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_eval_2 v1 o) o' -> 
    red_exprh k c st' (expr_eval_1 (out_ter st (res_value v1)) e2) o'
| red_exprh_eval_1_abort : forall k c st e2 o,
    abort o ->
    red_exprh k c st (expr_eval_1 o e2) o
| red_exprh_eval_2 : forall k c c1 st' st st1 s e ptr obj o,
    get_object st ptr = Some obj ->
    envstore_of_obj st obj = Some (c1, st1) ->
    desugar_expr s = Some e ->
    red_exprh k c1 st1 e o ->
    red_exprh k c st' (expr_eval_2 (value_string s) (out_ter st (res_value (value_object ptr)))) o
| red_exprh_eval_2_abort : forall k c st v1 o,
    abort o ->
    red_exprh k c st (expr_eval_2 v1 o) o

(* hint *)
| red_exprh_hint : forall k c st s e o,
    red_exprh k c st e o ->
    red_exprh (S k) c st (expr_hint s e) o 
.

