Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Import List.ListNotations.

Open Scope list_scope.
Open Scope container_scope.

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

Inductive red_exprh : nat -> ctx -> store -> ext_expr -> out -> Prop :=
| red_exprh_empty : forall k c st, red_exprh (S k) c st expr_empty (out_ter st (res_value value_empty))
| red_exprh_null : forall k c st, red_exprh (S k) c st expr_null (out_ter st (res_value value_null))
| red_exprh_undefined : forall k c st, red_exprh (S k) c st expr_undefined (out_ter st (res_value value_undefined))
| red_exprh_string : forall k c st s, red_exprh (S k) c st (expr_string s) (out_ter st (res_value (value_string s)))
| red_exprh_number : forall k c st n, red_exprh (S k) c st (expr_number n) (out_ter st (res_value (value_number n)))
| red_exprh_bool : forall k c st b, red_exprh (S k) c st (expr_bool b) (out_ter st (res_value (value_bool b)))
| red_exprh_id : forall k c st i v, 
    binds c i v -> 
    red_exprh (S k) c st (expr_id i) (out_ter st (res_value v))
| red_exprh_lambda : forall k c st args body v,
    v = add_closure c None args body ->
    red_exprh (S k) c st (expr_lambda args body) (out_ter st (res_value v))

(* eval_many *)
| red_exprh_eval_many_1 : forall k c st vs E o,
    red_exprh k c st (E (rev vs)) o ->
    red_exprh k c st (expr_eval_many_1 nil vs E) o
| red_exprh_eval_many_1_next : forall k c st e es vs E o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_eval_many_2 es o vs E) o' ->
    red_exprh k c st (expr_eval_many_1 (e::es) vs E) o'
| red_exprh_eval_many_2 : forall k c st' st es v vs E o,
    red_exprh k c st (expr_eval_many_1 es (v::vs) E) o ->
    red_exprh k c st' (expr_eval_many_2 es (out_ter st (res_value v)) vs E) o
| red_exprh_eval_many_2_abort : forall k c st es vs E o,
    abort o ->
    red_exprh k c st (expr_eval_many_2 es o vs E) o

(* object *)
| red_exprh_object : forall k c st e1 e2 e3 e4 e5 a o,
    red_exprh k c st (expr_eval_many_1 [e1; e2; e3; e4; e5] nil (expr_object_1 a)) o ->
    red_exprh (S k) c st (expr_object (objattrs_intro e1 e2 e3 e4 e5) a) o
| red_exprh_object_1 : forall k c st class ext proto code prim a o,
    red_exprh k c st (expr_object_2 (object_intro (oattrs_intro proto class ext prim code) \{}) a) o ->
    red_exprh k c st (expr_object_1 a [value_string class; value_bool ext; proto; code; prim]) o
| red_exprh_object_2 : forall k c st st1 obj,
    st1 = st \(fresh st := obj) ->
    red_exprh k c st (expr_object_2 obj nil) (out_ter st1 (res_value (value_object (fresh st))))
| red_exprh_object_2_data : forall k c st obj s e1 e2 e3 e4 a o,
    red_exprh k c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_data_1 obj a s)) o ->
    red_exprh k c st (expr_object_2 obj ((s, property_data (data_intro e3 e4 e2 e1)) :: a)) o
| red_exprh_object_data_1 : forall k c st obj a s v3 b1 b2 b4 o,
    red_exprh k c st (expr_object_2 (set_object_property obj s (attributes_data_of (attributes_data_intro v3 b4 b2 b1))) a) o ->
    red_exprh k c st (expr_object_data_1 obj a s [value_bool b1; value_bool b2; v3; value_bool b4]) o
| red_exprh_object_2_accessor : forall k c st obj s e1 e2 e3 e4 a o,
    red_exprh k c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_accessor_1 obj a s)) o ->
    red_exprh k c st (expr_object_2 obj ((s, property_accessor (accessor_intro e3 e4 e2 e1)) :: a)) o
| red_exprh_object_accessor_1 : forall k c st obj a s v1 v2 v3 v4 b1 b2 o,
    red_exprh k c st (expr_object_2 (set_object_property obj s (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1))) a) o ->
    red_exprh k c st (expr_object_accessor_1 obj a s [value_bool b1; value_bool b2; v3; v4]) o

(* get_attr *)
| red_exprh_get_attr : forall k c st pa e1 e2 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2] nil (expr_get_attr_1 pa)) o ->
    red_exprh (S k) c st (expr_get_attr pa e1 e2) o
| red_exprh_get_attr_1 : forall k c st pa s ptr obj attrs,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_pattr_readable attrs pa ->
    red_exprh k c st (expr_get_attr_1 pa [value_object ptr; value_string s]) 
        (out_ter st (res_value (get_attributes_pattr attrs pa)))

(* set_attr *)
| red_exprh_set_attr : forall k c st pa e1 e2 e3 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2; e3] nil (expr_set_attr_1 pa)) o ->
    red_exprh (S k) c st (expr_set_attr pa e1 e2 e3) o
| red_exprh_set_attr_1 : forall k c st st1 pa ptr obj attrs s v,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_pattr_valid pa v ->
    attributes_pattr_writable attrs pa ->
    st1 = st \(ptr := set_object_property obj s (set_attributes_pattr attrs pa v)) ->
    red_exprh k c st (expr_set_attr_1 pa [value_object ptr; value_string s; v]) (out_ter st1 (res_value v))
| red_exprh_set_attr_1_add_field : forall k c st st1 pa ptr obj s v,
    binds st ptr obj ->
    ~index (object_properties obj) s ->
    object_extensible obj ->
    attributes_pattr_valid pa v ->
    st1 = st \(ptr := set_object_property obj s (new_attributes_pattr pa v)) ->
    red_exprh k c st (expr_set_attr_1 pa [value_object ptr; value_string s; v]) (out_ter st1 (res_value v))

(* get_obj_attr *)
| red_exprh_get_obj_attr : forall k c st oa e1 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_get_obj_attr_1 oa o) o' ->
    red_exprh (S k) c st (expr_get_obj_attr oa e1) o'
| red_exprh_get_obj_attr_1 : forall k c st' st oa ptr obj,
    binds st ptr obj ->
    red_exprh k c st' (expr_get_obj_attr_1 oa (out_ter st (res_value (value_object ptr)))) 
        (out_ter st (res_value (get_object_oattr obj oa)))
| red_exprh_get_obj_attr_1_abort : forall k c st oa o,
    abort o ->
    red_exprh k c st (expr_get_obj_attr_1 oa o) o

(* set_obj_attr *)
| red_exprh_set_obj_attr : forall k c st oa e1 e2 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2] nil (expr_set_obj_attr_1 oa)) o ->
    red_exprh (S k) c st (expr_set_obj_attr oa e1 e2) o
| red_exprh_set_obj_attr_1 : forall k c st st1 oa ptr obj v,
    binds st ptr obj ->
    object_oattr_valid oa v ->
    object_oattr_modifiable obj oa ->
    st1 = st \(ptr := set_object_oattr obj oa v) ->
    red_exprh k c st (expr_set_obj_attr_1 oa [value_object ptr; v]) (out_ter st1 (res_value v))

(* get_field *)
| red_exprh_get_field : forall k c st e1 e2 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2] nil expr_get_field_1) o ->
    red_exprh (S k) c st (expr_get_field e1 e2) o
| red_exprh_get_field_1 : forall k c st ptr obj s oattr o,
    binds st ptr obj ->
    object_property_is st obj s oattr ->
    red_exprh k c st (expr_get_field_2 ptr oattr) o ->
    red_exprh k c st (expr_get_field_1 [value_object ptr; value_string s]) o
| red_exprh_get_field_2_no_field : forall k c st ptr,
    red_exprh k c st (expr_get_field_2 ptr None) (out_ter st (res_value value_undefined))
| red_exprh_get_field_2_get_field : forall k c st ptr data,
    red_exprh k c st (expr_get_field_2 ptr (Some (attributes_data_of data))) 
        (out_ter st (res_value (attributes_data_value data)))
| red_exprh_get_field_2_getter : forall k c st ptr acc o,
    red_exprh k c st (expr_app_2 (attributes_accessor_get acc) [value_object ptr]) o ->
    red_exprh k c st (expr_get_field_2 ptr (Some (attributes_accessor_of acc))) o

(* set_field *)
| red_exprh_set_field : forall k c st e1 e2 e3 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2; e3] nil expr_set_field_1) o ->
    red_exprh (S k) c st (expr_set_field e1 e2 e3) o
| red_exprh_set_field_1 : forall k c st ptr obj oattr s v3 v4 o,
    binds st ptr obj ->
    object_property_is st obj s oattr ->
    red_exprh k c st (expr_set_field_2 ptr obj oattr s v3) o ->
    red_exprh k c st (expr_set_field_1 [value_object ptr; value_string s; v3]) o
| red_exprh_set_field_2_set_field : forall k c st st1 ptr obj data s v3,
    index (object_properties obj) s ->
    attributes_data_writable data ->
    st1 = st \(ptr := set_object_property obj s (attributes_data_of (attributes_data_value_update data v3))) ->
    red_exprh k c st (expr_set_field_2 ptr obj (Some (attributes_data_of data)) s v3) 
        (out_ter st1 (res_value v3))
| red_exprh_set_field_2_shadow_field : forall k c st st1 ptr obj data s v3,
    ~index (object_properties obj) s ->
    object_extensible obj ->
    attributes_data_writable data ->
    st1 = st \(ptr := set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_exprh k c st (expr_set_field_2 ptr obj (Some (attributes_data_of data)) s v3) 
        (out_ter st1 (res_value v3))
| red_exprh_set_field_2_add_field : forall k c st st1 ptr obj s v3,
    object_extensible obj ->
    st1 = st \(ptr := set_object_property obj s (attributes_data_of (attributes_data_intro v3 true true true))) ->
    red_exprh k c st (expr_set_field_2 ptr obj None s v3) (out_ter st1 (res_value v3))
| red_exprh_set_field_2_setter : forall k c st ptr obj acc s v3 o,
    red_exprh k c st (expr_app_2 (attributes_accessor_set acc) [value_object ptr; v3]) o ->
    red_exprh k c st (expr_set_field_2 ptr obj (Some (attributes_accessor_of acc)) s v3) o
| red_exprh_set_field_2_unwritable : forall k c st ptr obj data s v3,
    !attributes_data_writable data ->
    red_exprh k c st (expr_set_field_2 ptr obj (Some (attributes_data_of data)) s v3) 
        (out_ter st (res_exception (value_string "unwritable-field")))
| red_exprh_set_field_2_unextensible_add : forall k c st ptr obj s v3,
    !object_extensible obj ->
    red_exprh k c st (expr_set_field_2 ptr obj None s v3) 
        (out_ter st (res_exception (value_string "unextensible-set")))
| red_exprh_set_field_2_unextensible_shadow : forall k c st ptr obj data s v3,
    attributes_data_writable data ->
    ~index (object_properties obj) s ->
    !object_extensible obj ->
    red_exprh k c st (expr_set_field_2 ptr obj (Some (attributes_data_of data)) s v3) 
        (out_ter st (res_exception (value_string "unextensible-shadow")))

(* delete_field *)
| red_exprh_delete_field : forall k c st e1 e2 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2] nil expr_delete_field_1) o ->
    red_exprh (S k) c st (expr_delete_field e1 e2) o
| red_exprh_delete_field_1 : forall k c st ptr s obj oattr o,
    binds st ptr obj ->
    get_object_property obj s = oattr ->
    red_exprh k c st (expr_delete_field_2 ptr obj oattr s) o ->
    red_exprh k c st (expr_delete_field_1 [value_object ptr; value_string s]) o
| red_exprh_delete_field_2_not_found : forall k c st ptr obj s,
    red_exprh k c st (expr_delete_field_2 ptr obj None s) (out_ter st (res_value value_false))
| red_exprh_delete_field_2_unconfigurable : forall k c st ptr obj attr s,
    !attributes_configurable attr ->
    red_exprh k c st (expr_delete_field_2 ptr obj (Some attr) s) 
        (out_ter st (res_exception (value_string "unconfigurable-delete")))
| red_exprh_delete_field_2_found : forall k c st st1 ptr obj attr s,
    attributes_configurable attr ->
    st1 = st \(ptr := delete_object_property obj s) ->
    red_exprh k c st (expr_delete_field_2 ptr obj (Some attr) s) (out_ter st1 (res_value value_true))

(* own_field_names *)
| red_exprh_own_field_names : forall k c st e o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_own_field_names_1 o) o' ->
    red_exprh (S k) c st (expr_own_field_names e) o'
| red_exprh_own_field_names_1 : forall k c st' st st1 ptr obj,
    binds st ptr obj ->
    st1 = st \(fresh st := make_prop_list obj) ->
    red_exprh k c st' (expr_own_field_names_1 (out_ter st (res_value (value_object ptr)))) 
        (out_ter st1 (res_value (value_object (fresh st))))
| red_exprh_own_field_names_1_abort : forall k c st o,
    abort o ->
    red_exprh k c st (expr_own_field_names_1 o) o

(* op1 *)
| red_exprh_op1 : forall k c st e op o o',
    red_exprh k c st e o ->
    red_exprh k c st (expr_op1_1 op o) o' ->
    red_exprh (S k) c st (expr_op1 op e) o'
| red_exprh_op1_1 : forall k c st' st op v v',
    eval_unary_op op st v v' ->
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
    eval_binary_op op st v1 v2 v ->
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
    red_exprh k c st (expr_eval_many_1 el nil (expr_app_2 v)) o ->
    red_exprh k c st' (expr_app_1 (out_ter st (res_value v)) el) o
| red_exprh_app_1_abort : forall k c st o el,
    abort o ->
    red_exprh k c st (expr_app_1 o el) o
| red_exprh_app_2 : forall k c c' st v clo vl o,
    value_is_closure st v clo ->
    closure_ctx clo vl c' ->
    red_exprh k c' st (closure_body clo) o ->
    red_exprh k c st (expr_app_2 v vl) o 

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

(* jseq *)
| red_exprh_jseq : forall k c st e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_jseq_1 o e2) o' ->
    red_exprh (S k) c st (expr_jseq e1 e2) o'
| red_exprh_jseq_1 : forall k c st' st v e2 o o',
    red_exprh k c st e2 o ->
    red_exprh k c st (expr_jseq_2 v o) o' ->
    red_exprh k c st' (expr_jseq_1 (out_ter st (res_value v)) e2) o'
| red_exprh_jseq_1_abort : forall k c st e2 o,
    abort o ->
    red_exprh k c st (expr_jseq_1 o e2) o
| red_exprh_jseq_2 : forall k c st st' v1 v2,
    red_exprh k c st' (expr_jseq_2 v1 (out_ter st (res_value v2))) 
        (out_ter st (res_value (overwrite_value_if_empty v1 v2)))
| red_exprh_jseq_2_exception : forall k c st st' v1 v2,
    red_exprh k c st' (expr_jseq_2 v1 (out_ter st (res_exception v2))) 
        (out_ter st (res_exception v2))
| red_exprh_jseq_2_break : forall k c st st' v1 v2 l,
    red_exprh k c st' (expr_jseq_2 v1 (out_ter st (res_break l v2))) 
       (out_ter st (res_break l (overwrite_value_if_empty v1 v2)))
| red_exprh_jseq_2_div : forall k c st v1,
    red_exprh k c st (expr_jseq_2 v1 out_div) out_div

(* let *)
| red_exprh_let : forall k c st i e1 e2 o o',
    red_exprh k c st e1 o ->
    red_exprh k c st (expr_let_1 i o e2) o' ->
    red_exprh (S k) c st (expr_let i e1 e2) o'
| red_exprh_let_1 : forall k c c' st' st i v e2 o,
    c' = c \(i := v) ->
    red_exprh k c' st e2 o ->
    red_exprh k c st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_exprh_let_1_abort : forall k c st i o e2,
    abort o ->
    red_exprh k c st (expr_let_1 i o e2) o

(* rec *)
| red_exprh_rec : forall k c c' st i args body v e2 o,
    v = add_closure c (Some i) args body ->
    c' = c \(i := v) ->
    red_exprh k c' st e2 o ->
    red_exprh (S k) c st (expr_recc i (expr_lambda args body) e2) o

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
    red_exprh k c st (expr_app_2 v' [v]) o ->
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
| red_exprh_eval : forall k c st e1 e2 o,
    red_exprh k c st (expr_eval_many_1 [e1; e2] nil expr_eval_1) o ->
    red_exprh (S k) c st (expr_eval e1 e2) o
| red_exprh_eval_1 : forall k c c1 st s e ptr obj o,
    binds st ptr obj ->
    ctx_of_obj obj = Some c1 ->
    desugar_expr s = Some e ->
    red_exprh k c1 st e o ->
    red_exprh k c st (expr_eval_1 [value_string s; value_object ptr]) o

(* hint *)
| red_exprh_hint : forall k c st s e o,
    red_exprh k c st e o ->
    red_exprh (S k) c st (expr_hint s e) o 
.

