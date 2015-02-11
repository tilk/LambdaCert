Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax LjsPrettyRules LjsPrettyInterm LjsStore.
Require EjsSyntax.
Require JsSyntax JsPrettyRules JsPrettyInterm.
Require Import EjsFromJs EjsToLjs.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Local Coercion JsNumber.of_int : Z >-> JsNumber.number.

Module L. 
Include LjsSyntax.
Include LjsPrettyRules.
Include LjsPrettyInterm.
Include LjsStore.
End L.

Module E := EjsSyntax.

Module J.
Include JsSyntax.
Include JsPreliminary.
Include JsPrettyRules.
Include JsPrettyInterm.
End J.

Implicit Type A B : Type.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : L.id.
Implicit Type st : L.store.
Implicit Type e : L.expr.
Implicit Type v : L.value.
Implicit Type loc : L.value_loc.
Implicit Type o : L.out.
Implicit Type c : L.ctx.
Implicit Type ptr : L.object_ptr.
Implicit Type obj : L.object.
Implicit Type re : L.result.
Implicit Type r : L.res.

Implicit Type jst : J.state.
Implicit Type je : J.expr.
Implicit Type jc : J.execution_ctx.
Implicit Type jo : J.out.
Implicit Type jr : J.res.
Implicit Type jv : J.value.
Implicit Type jptr : J.object_loc.
Implicit Type jobj : J.object.

Definition object_bisim := J.object_loc -> L.object_ptr -> bool.

Implicit Type BR : object_bisim.

Definition js_literal_to_ljs jl := ejs_to_ljs (js_literal_to_ejs jl).
Definition js_expr_to_ljs je := ejs_to_ljs (js_expr_to_ejs je).

Inductive object_flat_sim jobj obj :=
| object_flat_sim_intro : (* TODO *) 
    J.object_class_ jobj = L.object_class obj ->
    J.object_extensible_ jobj = L.object_extensible obj ->
    object_flat_sim jobj obj
.

Inductive ref_label :=
| ref_label_proto : ref_label
| ref_label_primval : ref_label
| ref_label_value : string -> ref_label
.

Inductive js_ref_label_binds : J.object -> ref_label -> J.object_loc -> Prop :=
| js_ref_label_binds_proto : forall jobj jptr, 
    J.object_proto_ jobj = J.value_object jptr ->
    js_ref_label_binds jobj ref_label_proto jptr
.

(* TODO ljs_ref_label_binds *)

Inductive heaps_bisim jst st : Prop := 
heaps_bisim_intro : forall BR, 
    (forall jptr ptr jobj obj, 
     istrue (BR jptr ptr) -> 
     J.object_binds jst jptr jobj ->
     L.object_binds st ptr obj ->
     object_flat_sim jobj obj /\ True) -> (* TODO *)
    heaps_bisim jst st
.

Inductive js_value_ljs `(bisim : heaps_bisim jst st) : J.value -> L.value -> Prop :=
| js_value_ljs_undefined : js_value_ljs bisim (J.value_prim J.prim_undef) L.value_undefined
| js_value_ljs_null : js_value_ljs bisim (J.value_prim J.prim_null) L.value_null
| js_value_ljs_true : js_value_ljs bisim (J.value_prim (J.prim_bool true)) L.value_true 
| js_value_ljs_false : js_value_ljs bisim (J.value_prim (J.prim_bool false)) L.value_false  
| js_value_ljs_number : forall n, js_value_ljs bisim (J.value_prim (J.prim_number n)) (L.value_number n)  
| js_value_ljs_string : forall s, js_value_ljs bisim (J.value_prim (J.prim_string s)) (L.value_string s)  
.

Inductive js_res_ljs `(bisim : heaps_bisim jst st) : J.res -> L.res -> Prop :=
| js_res_ljs_normal_value : forall jv v,
    js_value_ljs bisim jv v ->
    js_res_ljs bisim (J.res_intro J.restype_normal (J.resvalue_value jv) J.label_empty) (L.res_value v)
.

Inductive js_out_ljs `(bisim : heaps_bisim jst st) : J.out -> L.out -> Prop :=
| js_out_ljs_ter : forall jr r,
    js_res_ljs bisim jr r ->
    js_out_ljs bisim (J.out_ter jst jr) (L.out_ter st r)
.

Create HintDb js_ljs discriminated.

Hint Constructors js_value_ljs : js_ljs.
Hint Constructors js_res_ljs : js_ljs.
Hint Constructors js_out_ljs : js_ljs.

Lemma red_literal_ok : forall jst jc jo st c o l (bisim : heaps_bisim jst st), 
    J.red_expr jst jc (J.expr_basic (J.expr_literal l)) jo -> 
    L.red_expr c st (L.expr_basic (js_literal_to_ljs l)) o ->
    js_out_ljs bisim jo o.
Proof.
    introv jred lred.
    destruct l as [ | [ | ] | | ]; 
    inverts jred; inverts lred; tryfalse;
    eauto with js_ljs. 
Admitted. (* faster *)

Ltac inv_internal_ljs :=
    match goal with
    | H	: L.red_expr _ _ ?e _ |- _ => 
        match e with 
        | L.expr_basic _ => fail 
        | _ => inverts H 
        end
    end
.

(* TODO 

Lemma red_identifier_ok : forall jst jc jo st c o i (bisim : heaps_bisim jst st),
    J.red_expr jst jc (J.expr_basic (J.expr_identifier i)) jo -> 
    L.red_expr c st (L.expr_basic (js_expr_to_ljs (J.expr_identifier i))) o ->
    js_out_ljs bisim jo o.
Proof.
    introv jred lred.
    inverts jred; inverts lred; tryfalse.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.
    inv_internal_ljs.


    repeat inv_internal_ljs.
    inverts H7; tryfalse.
    inverts H8; tryfalse.
    inverts H11; tryfalse.
    inverts H12; tryfalse.

    inverts H0; tryfalse.
    inverts H3; tryfalse.
*)
