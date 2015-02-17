Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax LjsPrettyRules LjsPrettyInterm LjsStore LjsAuxiliary.
Require EjsSyntax.
Require JsSyntax JsPrettyInterm JsPrettyRules.
Require EjsFromJs EjsToLjs.
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
Include LjsValues.
End L.

Module E.
Include EjsSyntax.
Include EjsFromJs.
Include EjsToLjs.
End E.

Module J.
Include JsSyntax.
Include JsPreliminary.
Include JsPrettyInterm.
Include JsPrettyRules.
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
Implicit Type jrv : J.resvalue.
Implicit Type jt : J.stat.
Implicit Type jref : J.ref.

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

Definition js_literal_to_ljs jl := E.ejs_to_ljs (E.js_literal_to_ejs jl).
Definition js_expr_to_ljs je := E.ejs_to_ljs (E.js_expr_to_ejs je).
Definition js_stat_to_ljs jt := E.ejs_to_ljs (E.js_stat_to_ejs jt).

Inductive resvalue_related BR : J.resvalue -> L.value -> Prop :=
| resvalue_related_value : forall jv v,
    value_related BR jv v ->
    resvalue_related BR (J.resvalue_value jv) v
.

Definition js_exn_object obj v := 
    Heap.binds (L.object_properties_ obj) "%js-exn" 
        (L.attributes_data_of (L.attributes_data_intro v false false false)).

Inductive res_related BR jst st : J.res -> L.res -> Prop :=
| res_related_normal : forall jrv v,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_normal jrv J.label_empty) (L.res_value v)
| res_related_throw : forall jrv ptr obj v,
    L.object_binds st ptr obj ->
    js_exn_object obj v ->
    res_related BR jst st (J.res_intro J.restype_throw jrv J.label_empty) 
        (L.res_exception (L.value_object ptr))
.

(*
Inductive out_related BR : J.out -> L.out -> Prop :=
| out_related_ter : forall jst st jr r,
    res_related BR jr r ->
    out_related BR (J.out_ter jst jr) (L.out_ter st r)
.
*)

Create HintDb js_ljs discriminated.

Hint Constructors attributes_data_related : js_ljs.
Hint Constructors attributes_accessor_related : js_ljs. 
Hint Constructors attributes_related : js_ljs.
Hint Constructors value_related : js_ljs.
Hint Constructors resvalue_related : js_ljs.
Hint Constructors res_related : js_ljs.
(* Hint Constructors out_related : js_ljs. *)

Hint Constructors J.red_expr : js_ljs.
Hint Constructors J.red_stat : js_ljs.
Hint Constructors J.red_spec : js_ljs.

Definition state_invariant BR jst jc c st :=
    heaps_bisim BR jst st.

Definition concl_expr_value BR jst jc c st st' r je :=
    exists jst' jr,
    state_invariant BR jst' jc c st' /\
    J.red_expr jst jc (J.expr_basic je) (J.out_ter jst' jr) /\ 
    res_related BR jst' st' jr r.

Definition concl_stat BR jst jc c st st' r jt :=
    exists jst' jr,
    state_invariant BR jst' jc c st' /\
    J.red_stat jst jc (J.stat_basic jt) (J.out_ter jst' jr) /\ 
    res_related BR jst' st' jr r.

(*
Definition concl_spec {A : Type} BR jst jc c st st' r js (P : A -> Prop) :=
    exists jst',
    state_invariant BR jst' jc c st' /\ 
    ((exists x, J.red_spec jst jc js (J.specret_val jst' x) /\ P x) \/
     (exists jr, 
        J.red_spec jst jc js (@J.specret_out A (J.out_ter jst' jr)) /\ 
        res_related BR jst' st' jr r)).
*)

Definition concl_spec {A : Type} BR jst jc c st st' r js (P : A -> Prop) :=
    exists jst',
    state_invariant BR jst' jc c st' /\ 
    ((exists x, J.red_spec jst jc js (J.specret_val jst' x) /\ P x) \/
     (exists jr, 
        J.red_spec jst jc js (@J.specret_out A (J.out_ter jst' jr)) /\ 
        J.abort (J.out_ter jst' jr) /\
        res_related BR jst' st' jr r)).

Definition concl_expr_getvalue BR jst jc c st st' r je :=
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value je) 
       (fun jv => exists v, r = L.res_value v /\ value_related BR jv v).

(*
Definition ih_expr je := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr BR jst jc c st st' r je.
*)
Definition ih_expr je := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr_getvalue BR jst jc c st st' r je.

Definition ih_stat jt := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_stat_to_ljs jt)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r jt.

Lemma red_expr_literal_ok : forall jst jc c st st' r l BR, 
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_literal_to_ljs l)) (L.out_ter st' r) ->
    concl_expr_value BR jst jc c st st' r (J.expr_literal l).
Proof.
    introv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts Hlred; eexists; jauto_set; eauto with js_ljs.
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

Ltac inv_res_related :=
    match goal with
    | H : res_related _ _ _ |- _ => inverts H
    end.

Ltac inv_resvalue_related :=
    match goal with
    | H : resvalue_related _ _ _ |- _ => inverts H
    end.

Ltac unfold_concl := unfold concl_expr_value, concl_expr_getvalue, concl_stat, concl_spec in *.

Ltac jauto_js := repeat (jauto_set; eauto with js_ljs).

Hint Extern 10 => match goal with 
    | H : J.abort_intercepted_stat _ |- _ => solve [inverts H]
    end : js_ljs. 

Lemma red_stat_expr_ok : forall jst jc c st st' r je BR, 
    ih_expr je ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r (J.stat_expr je).
Proof.
    introv IH Hinv Hlred.
    specializes IH Hinv Hlred.
    unfold_concl.
    destruct IH as (jst'&Hinv'&[|]). (* TODO better tactics *)
    jauto_js.
    substs.
    jauto_js.
    jauto_js.
Qed.
(*
Lemma red_spec_get_value_ok : forall jst jc c st st' r je BR, 
    ih_expr je ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value je) 
       (fun jv => exists v, r = L.res_value v /\ value_related BR jv v).
Proof.
    introv IHe Hinv Hlred.
    specializes IHe Hinv Hlred.
    unfold_concl.
    jauto_js. 
    inverts H1. inverts H2. (* TODO *)
    left.
    jauto_js.
Qed.
*)
(* TODO
Lemma ljs_to_bool_lemma : forall BR jst jc c st st' r jv v loc v1,
    state_invariant BR jst jc c st ->
    value_related BR jv v -> 
    L.id_binds c "%ToBoolean" loc ->
    L.value_binds st loc v1 ->
    L.red_expr c st (L.expr_app_2 v1 [v] nil) (L.out_ter st' r) ->
    st = st' /\
    exists b,
    r = L.res_value (L.bool_to_value b) /\
    J.red_expr jst jc (J.spec_to_boolean jv) 
        (J.out_ter jst (J.res_val (J.value_prim (J.prim_bool b)))).
Proof.
Admitted.
*)

Lemma red_spec_to_boolean_ok : forall jst jc c st st' r je BR, 
    ih_expr je ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (E.to_bool (js_expr_to_ljs je))) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value_conv J.spec_to_boolean je) 
       (fun jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
           r = L.res_value (L.bool_to_value b)).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred.
Admitted.

Lemma res_related_abort : forall BR jst jst' st jr r,
    res_related BR jst st jr r ->
    J.abort (J.out_ter jst' jr) ->
    L.res_is_control r.
Proof.
    introv Hrel Hab.
    inverts Hrel.
    inverts Hab. unfold J.res_is_normal in *. simpls. tryfalse.
    eapply L.res_is_control_exception.
Qed.

Lemma red_stat_if_ok : forall jst jc c st st' r je jt1 jt2 BR, 
    ih_expr je ->
    ih_stat jt1 ->
    ih_stat jt2 ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_stat_to_ljs (J.stat_if je jt1 (Some jt2)))) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r (J.stat_if je jt1 (Some jt2)).
Proof.
    introv IHe IHt1 IHt2 Hinv Hlred.
    inverts Hlred.
    destruct o.
    inverts H6.
    forwards Hh : red_spec_to_boolean_ok IHe Hinv H5.
    unfold concl_spec in Hh.
    destruct Hh as (jst'&Hinv'&[|]). (* TODO better tactics *)
    jauto_set.
    substs.
    destruct x0.
    (* true *) 
    inverts H6.
    specializes IHt1 Hinv' H8.
    unfold concl_stat in *.
    jauto_js.
    inverts H3. inverts H1.
    (* false *)
    inverts H6.
    specializes IHt2 Hinv' H8.
    unfold concl_stat in *.
    jauto_js.
    inverts H3. inverts H1.
    (* abort *)
    jauto_set. 
    forwards Hab : res_related_abort H1 H0.
    inverts H6.
    inverts Hab. 
    inverts Hab. 
    unfold concl_stat.
    jauto_js.
Qed.

Lemma red_stat_throw_ok : forall jst jc c st st' r je BR,
    ih_expr je ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (L.expr_basic (js_stat_to_ljs (J.stat_throw je))) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r (J.stat_throw je).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred.
    inverts H0.
Admitted. (* TODO lemmas, tactics needed! *)

    
    

(*

Lemma red_identifier_ok : forall jst jc st c o i BR,
    heaps_bisim BR jst st ->
    L.red_expr c st (L.expr_basic (js_expr_to_ljs (J.expr_identifier i))) o ->
    exists jo,
    J.red_expr jst jc (J.expr_basic (J.expr_identifier i)) jo /\
    out_related BR jo o.
Proof.
*)
