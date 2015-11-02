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
Require EjsFromJs.
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

Inductive red_expr : ctx -> store -> ext_expr -> out -> Prop :=
| red_expr_empty : forall c st, red_expr c st expr_empty (out_ter st (res_value value_empty))
| red_expr_null : forall c st, red_expr c st expr_null (out_ter st (res_value value_null))
| red_expr_undefined : forall c st, red_expr c st expr_undefined (out_ter st (res_value value_undefined))
| red_expr_string : forall c st s, red_expr c st (expr_string s) (out_ter st (res_value (value_string s)))
| red_expr_number : forall c st n, red_expr c st (expr_number n) (out_ter st (res_value (value_number n)))
| red_expr_int : forall c st k1, red_expr c st (expr_int k1) (out_ter st (res_value (value_int k1)))
| red_expr_bool : forall c st b, red_expr c st (expr_bool b) (out_ter st (res_value (value_bool b)))
| red_expr_id : forall c st i v, 
    binds c i v -> 
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
| red_expr_object : forall c st e1 e2 e3 e4 ia a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_1 ia a)) o ->
    red_expr c st (expr_object (objattrs_intro e1 e2 e3 e4) ia a) o
| red_expr_object_1 : forall c st class ext proto code ia a o,
    object_oattr_valid oattr_proto proto ->
    object_oattr_valid oattr_code code ->
    red_expr c st (expr_object_2 ia a (object_intro (oattrs_intro proto class ext code) \{} \{})) o ->
    red_expr c st (expr_object_1 ia a [value_string class; value_bool ext; proto; code]) o
| red_expr_object_2 : forall c st st1 obj,
    st1 = st \(fresh st := obj) ->
    red_expr c st (expr_object_2 nil nil obj) (out_ter st1 (res_value (value_object (fresh st))))
| red_expr_object_2_data : forall c st obj s e1 e2 e3 e4 a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_data_1 obj s (expr_object_2 nil a))) o ->
    red_expr c st (expr_object_2 nil ((s, property_data (data_intro e3 e4 e2 e1)) :: a) obj) o
| red_expr_object_data_1 : forall c st obj E s v3 b1 b2 b4 o,
    red_expr c st (E (set_object_property obj s (attributes_data_of (attributes_data_intro v3 b4 b2 b1)))) o ->
    red_expr c st (expr_object_data_1 obj s E [value_bool b1; value_bool b2; v3; value_bool b4]) o
| red_expr_object_2_accessor : forall c st obj s e1 e2 e3 e4 a o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3; e4] nil (expr_object_accessor_1 obj s (expr_object_2 nil a))) o ->
    red_expr c st (expr_object_2 nil ((s, property_accessor (accessor_intro e3 e4 e2 e1)) :: a) obj) o
| red_expr_object_accessor_1 : forall c st obj E s v3 v4 b1 b2 o,
    red_expr c st (E (set_object_property obj s (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1)))) o ->
    red_expr c st (expr_object_accessor_1 obj s E [value_bool b1; value_bool b2; v3; v4]) o
| red_expr_object_2_internal : forall c st obj s e ia a o,
    red_expr c st (expr_eval_many_1 [e] nil (expr_object_internal_1 obj s (expr_object_2 ia a))) o ->
    red_expr c st (expr_object_2 ((s, e) :: ia) a obj) o
| red_expr_object_internal_1 : forall c st obj E s v o,
    red_expr c st (E (set_object_internal obj s v)) o ->
    red_expr c st (expr_object_internal_1 obj s E [v]) o

(* get_attr *)
| red_expr_get_attr : forall c st pa e1 e2 o,
    red_expr c st (expr_eval_many_1 [e1; e2] nil (expr_get_attr_1 pa)) o ->
    red_expr c st (expr_get_attr pa e1 e2) o
| red_expr_get_attr_1 : forall c st pa s ptr obj attrs,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_pattr_readable attrs pa ->
    red_expr c st (expr_get_attr_1 pa [value_object ptr; value_string s]) 
        (out_ter st (res_value (get_attributes_pattr attrs pa)))

(* set_attr *)
| red_expr_set_attr : forall c st pa e1 e2 e3 o,
    red_expr c st (expr_eval_many_1 [e1; e2; e3] nil (expr_set_attr_1 pa)) o ->
    red_expr c st (expr_set_attr pa e1 e2 e3) o
| red_expr_set_attr_1 : forall c st st1 pa ptr obj attrs s v,
    binds st ptr obj ->
    binds (object_properties obj) s attrs ->
    attributes_pattr_valid pa v ->
    attributes_pattr_writable attrs pa ->
    st1 = st \(ptr := set_object_property obj s (set_attributes_pattr attrs pa v)) ->
    red_expr c st (expr_set_attr_1 pa [value_object ptr; value_string s; v]) (out_ter st1 (res_value v))
| red_expr_set_attr_1_add_field : forall c st st1 pa ptr obj s v,
    binds st ptr obj ->
    ~index (object_properties obj) s ->
    object_extensible obj ->
    attributes_pattr_valid pa v ->
    st1 = st \(ptr := set_object_property obj s (new_attributes_pattr pa v)) ->
    red_expr c st (expr_set_attr_1 pa [value_object ptr; value_string s; v]) (out_ter st1 (res_value v))

(* get_obj_attr *)
| red_expr_get_obj_attr : forall c st oa e1 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_get_obj_attr_1 oa o) o' ->
    red_expr c st (expr_get_obj_attr oa e1) o'
| red_expr_get_obj_attr_1 : forall c st' st oa ptr obj,
    binds st ptr obj ->
    red_expr c st' (expr_get_obj_attr_1 oa (out_ter st (res_value (value_object ptr)))) 
        (out_ter st (res_value (get_object_oattr obj oa)))
| red_expr_get_obj_attr_1_abort : forall c st oa o,
    abort o ->
    red_expr c st (expr_get_obj_attr_1 oa o) o

(* set_obj_attr *)
| red_expr_set_obj_attr : forall c st oa e1 e2 o,
    red_expr c st (expr_eval_many_1 [e1; e2] nil (expr_set_obj_attr_1 oa)) o ->
    red_expr c st (expr_set_obj_attr oa e1 e2) o
| red_expr_set_obj_attr_1 : forall c st st1 oa ptr obj v,
    binds st ptr obj ->
    object_oattr_valid oa v ->
    object_oattr_modifiable obj oa ->
    st1 = st \(ptr := set_object_oattr obj oa v) ->
    red_expr c st (expr_set_obj_attr_1 oa [value_object ptr; v]) (out_ter st1 (res_value v))

(* delete_field *)
| red_expr_delete_field : forall c st e1 e2 o,
    red_expr c st (expr_eval_many_1 [e1; e2] nil expr_delete_field_1) o ->
    red_expr c st (expr_delete_field e1 e2) o
| red_expr_delete_field_1 : forall c st st1 ptr s obj attr,
    binds st ptr obj ->
    binds (object_properties obj) s attr ->
    attributes_configurable attr ->
    st1 = st \(ptr := delete_object_property obj s) ->
    red_expr c st (expr_delete_field_1 [value_object ptr; value_string s]) (out_ter st1 (res_value value_undefined))

(* get_internal *)
| red_expr_get_internal : forall c st s e o,
    red_expr c st (expr_eval_many_1 [e] nil (expr_get_internal_1 s)) o ->
    red_expr c st (expr_get_internal s e) o
| red_expr_get_internal_1 : forall c st s ptr obj v,
    binds st ptr obj ->
    binds (object_internal obj) s v ->
    red_expr c st (expr_get_internal_1 s [value_object ptr]) (out_ter st (res_value v))

(* set_internal *)
| red_expr_set_internal : forall c st s e1 e2 o,
    red_expr c st (expr_eval_many_1 [e1; e2] nil (expr_set_internal_1 s)) o ->
    red_expr c st (expr_set_internal s e1 e2) o
| red_expr_set_internal_1 : forall c st st1 s ptr obj v,
    binds st ptr obj ->
    index (object_internal obj) s ->
    st1 = st \(ptr := set_object_internal obj s v) ->
    red_expr c st (expr_set_internal_1 s [value_object ptr; v]) (out_ter st1 (res_value v))

(* own_field_names *)
| red_expr_own_field_names : forall c st e o o',
    red_expr c st e o ->
    red_expr c st (expr_own_field_names_1 o) o' ->
    red_expr c st (expr_own_field_names e) o'
| red_expr_own_field_names_1 : forall c st' st st1 ptr obj,
    binds st ptr obj ->
    st1 = st \(fresh st := make_prop_list obj) ->
    red_expr c st' (expr_own_field_names_1 (out_ter st (res_value (value_object ptr)))) 
        (out_ter st1 (res_value (value_object (fresh st))))
| red_expr_own_field_names_1_abort : forall c st o,
    abort o ->
    red_expr c st (expr_own_field_names_1 o) o

(* op1 *)
| red_expr_op1 : forall c st e op o o',
    red_expr c st e o ->
    red_expr c st (expr_op1_1 op o) o' ->
    red_expr c st (expr_op1 op e) o'
| red_expr_op1_1 : forall c st' st op v v',
    eval_unary_op op st v v' ->
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
    eval_binary_op op st v1 v2 v ->
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
| red_expr_app_2 : forall c c' st clo vl o,
    closure_ctx clo vl c' ->
    red_expr c' st (closure_body clo) o ->
    red_expr c st (expr_app_2 (value_closure clo) vl) o 
| red_expr_app_2_object : forall c st ptr obj clo vl o,
    binds st ptr obj ->
    object_code obj = value_closure clo ->
    red_expr c st (expr_app_2 (value_closure clo) (value_object ptr :: vl)) o ->
    red_expr c st (expr_app_2 (value_object ptr) vl) o 

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

(* jseq *)
| red_expr_jseq : forall c st e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_jseq_1 o e2) o' ->
    red_expr c st (expr_jseq e1 e2) o'
| red_expr_jseq_1 : forall c st' st v e2 o o',
    red_expr c st e2 o ->
    red_expr c st (expr_jseq_2 v o) o' ->
    red_expr c st' (expr_jseq_1 (out_ter st (res_value v)) e2) o'
| red_expr_jseq_1_abort : forall c st e2 o,
    abort o ->
    red_expr c st (expr_jseq_1 o e2) o
| red_expr_jseq_2 : forall c st st' v1 v2,
    red_expr c st' (expr_jseq_2 v1 (out_ter st (res_value v2))) 
        (out_ter st (res_value (overwrite_value_if_empty v1 v2)))
| red_expr_jseq_2_exception : forall c st st' v1 v2,
    red_expr c st' (expr_jseq_2 v1 (out_ter st (res_exception v2))) 
        (out_ter st (res_exception v2))
| red_expr_jseq_2_break : forall c st st' v1 v2 l,
    red_expr c st' (expr_jseq_2 v1 (out_ter st (res_break l v2))) 
       (out_ter st (res_break l (overwrite_value_if_empty v1 v2)))
| red_expr_jseq_2_div : forall c st v1,
    red_expr c st (expr_jseq_2 v1 out_div) out_div

(* let *)
| red_expr_let : forall c st i e1 e2 o o',
    red_expr c st e1 o ->
    red_expr c st (expr_let_1 i o e2) o' ->
    red_expr c st (expr_let i e1 e2) o'
| red_expr_let_1 : forall c c' st' st i v e2 o,
    c' = c \(i := v) ->
    red_expr c' st e2 o ->
    red_expr c st' (expr_let_1 i (out_ter st (res_value v)) e2) o
| red_expr_let_1_abort : forall c st i o e2,
    abort o ->
    red_expr c st (expr_let_1 i o e2) o

(* rec *)
| red_expr_rec : forall c c' st i args body v e2 o,
    v = add_closure c (Some i) args body ->
    c' = c \(i := v) ->
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
| red_expr_eval : forall c st e1 e2 o,
    red_expr c st (expr_eval_many_1 [e1; e2] nil expr_eval_1) o ->
    red_expr c st (expr_eval e1 e2) o
| red_expr_eval_1 : forall c c1 st s e ptr obj o,
    binds st ptr obj ->
    ctx_of_obj obj = Some c1 ->
    EjsFromJs.desugar_expr true s = Some e ->
    red_expr c1 st e o ->
    red_expr c st (expr_eval_1 [value_string s; value_object ptr]) o

(* hint *)
| red_expr_hint : forall c st s e o,
    red_expr c st e o ->
    red_expr c st (expr_hint s e) o 
.

