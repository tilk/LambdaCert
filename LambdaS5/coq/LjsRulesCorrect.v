Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax LjsPrettyRules LjsPrettyInterm LjsStore LjsAuxiliary.
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
Include LjsAuxiliary.
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

Definition object_bisim := J.object_loc -> L.object_ptr -> Prop.

Implicit Type BR : object_bisim.

Inductive value_related BR : J.value -> L.value -> Prop :=
| value_related_null : value_related BR (J.value_prim J.prim_null) L.value_null
| value_related_undefined : value_related BR (J.value_prim J.prim_undef) L.value_undefined
| value_related_number : forall n, value_related BR (J.value_prim (J.prim_number n)) (L.value_number n)
| value_related_string : forall s, value_related BR (J.value_prim (J.prim_string s)) (L.value_string s)
| value_related_true : value_related BR (J.value_prim (J.prim_bool true)) L.value_true
| value_related_false : value_related BR (J.value_prim (J.prim_bool false)) L.value_false
| value_related_object : forall jptr ptr, 
    BR jptr ptr -> value_related BR (J.value_object jptr) (L.value_object ptr) 
.

Inductive attributes_data_related BR : J.attributes_data -> L.attributes_data -> Prop := 
| attributes_data_related_intro : forall jv v b1 b2 b3, 
    value_related BR jv v ->
    attributes_data_related BR 
        (J.attributes_data_intro jv b1 b2 b3) 
        (L.attributes_data_intro v b1 b2 b3)
.

Inductive attributes_accessor_related BR : J.attributes_accessor -> L.attributes_accessor -> Prop := 
| attributes_accessor_related_intro : forall jv1 jv2 v1 v2 b1 b2, 
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    attributes_accessor_related BR 
        (J.attributes_accessor_intro jv1 jv2 b1 b2) 
        (L.attributes_accessor_intro v1 v2 b1 b2)
.

Inductive attributes_related BR : J.attributes -> L.attributes -> Prop :=
| attributes_related_data : forall jdata data,
    attributes_data_related BR jdata data -> 
    attributes_related BR (J.attributes_data_of jdata) (L.attributes_data_of data)
| attributes_related_accessor : forall jacc acc,
    attributes_accessor_related BR jacc acc -> 
    attributes_related BR (J.attributes_accessor_of jacc) (L.attributes_accessor_of acc)
.

Definition object_bisim_lfun BR :=
    forall jptr ptr1 ptr2, BR jptr ptr1 -> BR jptr ptr2 -> ptr1 = ptr2.

Definition object_bisim_rfun BR :=
    forall jptr1 jptr2 ptr, BR jptr1 ptr -> BR jptr2 ptr -> jptr1 = jptr2.

Definition object_bisim_ltotal jst BR :=
    forall jptr, J.object_indom jst jptr -> exists ptr, BR jptr ptr.

Definition object_bisim_lnoghost jst BR :=
    forall jptr ptr, BR jptr ptr -> J.object_indom jst jptr.

Definition object_bisim_rnoghost st BR :=
    forall jptr ptr, BR jptr ptr -> L.object_indom st ptr.

Definition object_bisim_consistent jst st BR :=
    object_bisim_lfun BR /\
    object_bisim_rfun BR /\
    object_bisim_ltotal jst BR /\
    object_bisim_lnoghost jst BR /\
    object_bisim_rnoghost st BR.

Definition object_attributes_related BR jobj obj := forall s, 
    ~J.Heap.indom (J.object_properties_ jobj) s /\ ~Heap.indom (L.object_properties_ obj) s \/
    exists jptr ptr, 
        J.Heap.binds (J.object_properties_ jobj) s jptr /\ Heap.binds (L.object_properties_ obj) s ptr /\
        attributes_related BR jptr ptr.

Definition object_prim_related BR jobj obj := 
    J.object_class_ jobj = L.object_class obj /\
    J.object_extensible_ jobj = L.object_extensible obj.

Definition object_related BR jobj obj :=
    object_prim_related BR jobj obj /\
    object_attributes_related BR jobj obj.

Definition heaps_bisim BR jst st := forall jptr ptr jobj obj, 
     BR jptr ptr -> 
     J.object_binds jst jptr jobj ->
     L.object_binds st ptr obj ->
     object_related BR jobj obj.

Definition js_literal_to_ljs jl := ejs_to_ljs (js_literal_to_ejs jl).
Definition js_expr_to_ljs je := ejs_to_ljs (js_expr_to_ejs je).

Inductive res_related BR : J.res -> L.res -> Prop :=
| res_related_normal_value : forall jv v,
    value_related BR jv v ->
    res_related BR (J.res_intro J.restype_normal (J.resvalue_value jv) J.label_empty) (L.res_value v)
.

Inductive out_related BR : J.out -> L.out -> Prop :=
| out_related_ter : forall jst st jr r,
    res_related BR jr r ->
    out_related BR (J.out_ter jst jr) (L.out_ter st r)
.

Create HintDb js_ljs discriminated.

Hint Constructors attributes_data_related : js_ljs.
Hint Constructors attributes_accessor_related : js_ljs.
Hint Constructors attributes_related : js_ljs.
Hint Constructors value_related : js_ljs.
Hint Constructors res_related : js_ljs.
Hint Constructors out_related : js_ljs.

Hint Constructors J.red_expr : js_ljs.

Lemma red_literal_ok : forall jst jc st c o l BR, 
    L.red_expr c st (L.expr_basic (js_literal_to_ljs l)) o ->
    exists jo,
    J.red_expr jst jc (J.expr_basic (J.expr_literal l)) jo /\ 
    out_related BR jo o.
Proof.
    introv lred.
    destruct l as [ | [ | ] | | ]; inverts lred; eexists; eauto with js_ljs.
Qed.

Ltac inv_internal_ljs :=
    match goal with
    | H	: L.red_expr _ _ ?e _ |- _ => 
        match e with 
        | L.expr_basic _ => fail 
        | _ => inverts H 
        end
    end
.


(*

Lemma red_identifier_ok : forall jst jc st c o i BR,
    heaps_bisim BR jst st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs (J.expr_identifier i))) o ->
    exists jo,
    J.red_expr jst jc (J.expr_basic (J.expr_identifier i)) jo /\
    out_related BR jo o.
Proof.
    introv Bisim lred.
    inverts lred.

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