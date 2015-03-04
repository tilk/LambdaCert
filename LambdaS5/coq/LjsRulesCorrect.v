Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax LjsPrettyRules LjsPrettyRulesAux LjsPrettyRulesIndexed LjsPrettyRulesIndexedAux
    LjsPrettyInterm LjsStore LjsAuxiliary.
Require LjsInitEnv.
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
Include LjsPrettyRulesIndexed.
Include LjsPrettyRulesIndexedAux.
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

Import LjsPrettyRulesAux.Tactics.
Import LjsPrettyRulesIndexedAux.Tactics.

Implicit Type A B : Type.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : L.id.
Implicit Type st : L.store.
Implicit Type e : L.expr.
Implicit Type v : L.value.
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
    ~J.Heap.indom (J.object_properties_ jobj) s /\ ~(s \in L.object_properties obj) \/
    exists jptr ptr, 
        J.Heap.binds (J.object_properties_ jobj) s jptr /\ binds (L.object_properties obj) s ptr /\
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
| resvalue_related_empty :  
    resvalue_related BR J.resvalue_empty L.value_empty
| resvalue_related_value : forall jv v,
    value_related BR jv v ->
    resvalue_related BR (J.resvalue_value jv) v
.

Definition js_exn_object obj v := 
    binds (L.object_properties obj) "%js-exn" 
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
| res_related_return : forall jrv v,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_return jrv J.label_empty) (L.res_break "%ret" v)
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

Definition includes_init_ctx c :=
    forall i v v', L.id_binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'. 

Definition state_invariant BR jst jc c st :=
    heaps_bisim BR jst st /\
    includes_init_ctx c.

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
Definition th_expr k je := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr_getvalue BR jst jc c st st' r je.

Definition th_stat k jt := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_stat_to_ljs jt)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r jt.

Definition ih_expr k := forall je k', (k' < k)%nat -> th_expr k' je.

Definition ih_stat k := forall jt k', (k' < k)%nat -> th_stat k' jt.

Ltac ljs_abort := match goal with
    | H : L.abort (L.out_ter _ (L.res_value _)) |- _ => 
        let H1 := fresh "H" in 
        solve [invert H as H1; inverts H1]
    end.

Ltac inv_internal_ljs :=
    match goal with
    | H	: L.red_exprh _ _ _ ?e _ |- _ => 
        match e with 
        | L.expr_basic _ => fail 
        | _ => inverts H; try ljs_abort
        end
    end.

Ltac inv_internal_fwd_ljs :=
    match goal with
    | H	: L.red_exprh _ _ _ ?e _ |- _ => 
        match e with 
        | L.expr_basic _ => fail 
        | _ => (inverts H; try ljs_abort); [idtac]
        end
    end.

Ltac inv_res_related :=
    match goal with
    | H : res_related _ _ _ |- _ => inverts H
    end.

Ltac inv_resvalue_related :=
    match goal with
    | H : resvalue_related _ _ _ |- _ => inverts H
    end.

Ltac unfold_concl := unfold concl_expr_value, concl_expr_getvalue, concl_stat, concl_spec.
 
Tactic Notation "unfold_concl" "in" hyp(H) := 
    unfold concl_expr_value, concl_expr_getvalue, concl_stat, concl_spec in H.

Ltac js_abort_intercepted := match goal with 
    | |- ~ J.abort_intercepted_stat _ => let H := fresh "H" in intro H; solve [inverts H]
    | |- ~ J.abort_intercepted_spec _ => let H := fresh "H" in intro H; solve [inverts H]
    | H : J.abort_intercepted_stat _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_spec _ |- _ => solve [inverts H]
    end.

Hint Extern 1 (~ J.abort_intercepted_stat _) => js_abort_intercepted : js_ljs.
Hint Extern 1 (~ J.abort_intercepted_spec _) => js_abort_intercepted : js_ljs.
Hint Extern 10 => js_abort_intercepted : js_ljs.

Ltac js_abort_rel_contr := match goal with
    | Ha : J.abort (J.out_ter ?jst ?x), Hr : res_related _ ?jst _ ?x (L.res_value _) |- _ =>
        let Hisn := fresh "Hisn" in
        inverts Ha as Hisn; inverts Hr; unfold J.res_is_normal, J.res_type in Hisn; false
    end.

Hint Extern 10 => js_abort_rel_contr : js_ljs.
 
Ltac apply_ih_expr := match goal with
    | H : ih_expr ?k', HS : state_invariant _ _ _ ?c ?st, 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        asserts Hle : (k < k')%nat; [omega | specializes H Hle HS HR; clear Hle; clear HR]
    end.

Ltac apply_ih_stat := match goal with
    | H : ih_stat ?k', HS : state_invariant _ _ _ ?c ?st, 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        asserts Hle : (k < k')%nat; [omega | specializes H HS HR; clear HR]
    end.

(* TODO move to utilities *)
Ltac destruct_hyp H := match type of H with
    | _ \/ _ => destruct H as [H|H]; try destruct_hyp H
    | _ /\ _ => 
        let H1 := fresh H in let H2 := fresh H in 
        destruct H as (H1&H2); try destruct_hyp H1; try destruct_hyp H2
    | exists v, _ => let v := fresh v in destruct H as (v&H); try destruct_hyp H
    | ?x = _ => is_var x; subst x
    | _ = ?x => is_var x; subst x
    end.

Tactic Notation "autoforwards" simple_intropattern(I) ":" constr(E) :=
    (forwards I : E; try eassumption; try omega); [idtac].

Ltac destr_concl := match goal with
    | H : concl_spec _ _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_stat _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    | H : concl_expr_getvalue _ _ _ _ _ _ _ _ |- _ =>
        unfold_concl in H; destruct_hyp H
    end.

Ltac jauto_js := repeat destr_concl; jauto_set; eauto with js_ljs; 
    repeat (try unfold_concl; jauto_set; eauto with js_ljs).

(* HERE START PROOFS *)

Lemma red_expr_literal_ok : forall k l,
    th_expr k (J.expr_literal l).
Proof.
    introv.
    unfolds.
    introv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts Hlred; jauto_js; solve [intuition jauto_js].
Qed.

Lemma red_stat_expr_ok : forall k je, 
    ih_expr k ->
    th_stat k (J.stat_expr je).
Proof.
    introv IH Hinv Hlred.
    inverts Hlred.
    apply_ih_expr.
    jauto_js.
Qed.
(*
Lemma red_spec_get_value_ok : forall jst jc c st st' r je BR, 
    ih_expr je ->
    state_invariant BR jst jc c st ->
    L.red_expr c st (js_expr_to_ljs je) (L.out_ter st' r) ->
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

(* TODO move this lemma! *)
Lemma get_closure_lemma : forall st clo, LjsCommon.get_closure st (L.value_closure clo) = L.result_some clo.
Proof.
    intros. unfolds. destruct (LjsStore.num_objects st); reflexivity. 
Qed.
 
(* TODO move this one too! *)
Lemma get_value_binds : forall c i v,
    L.get_value c i = Some v ->
    L.id_binds c i v.
Proof.
Admitted.

Hint Resolve get_value_binds.

Lemma ljs_to_bool_lemma : forall k BR jst jc c st st' r jv v,
    state_invariant BR jst jc c st ->
    value_related BR jv v -> 
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privToBoolean [v]) (L.out_ter st' r) ->
    st = st' /\
    exists b,
    r = L.res_value (L.bool_to_value b) /\
    J.red_expr jst jc (J.spec_to_boolean jv) 
        (J.out_ter jst (J.res_val (J.value_prim (J.prim_bool b)))).
Proof.
    introv Hinv Hrel Hlred.
    inverts Hlred.

    unfold LjsInitEnv.privToBoolean in *.
    rewrite get_closure_lemma in *.
    injects.
    simpl in H5.
    unfolds in H5.
    simpl in H5.
    injects.
    simpl in H7.
    inverts H7.
    inverts H4.
    unfolds in H3.
    simpl in H3.
    inverts H6.
    simpl in H3.
    assert (Htodo : v0 = v). skip. substs. (* TODO better heap library *)
    splits. reflexivity.
    inverts Hrel; try injects; jauto_js. 
    cases_if; 
    simpl; unfold J.convert_number_to_bool; cases_if; reflexivity.
    cases_if; 
    simpl; unfold J.convert_string_to_bool; cases_if; reflexivity.
    ljs_abort.
Qed.

(* TODO should occur earlier *)
Lemma state_invariant_includes_init_ctx : forall BR jst jc c st i v v',
    state_invariant BR jst jc c st ->
    L.id_binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'.
Proof.
    introv Hinv.
    unfold state_invariant, includes_init_ctx in Hinv.
    jauto.
Qed.

Lemma builtin_assoc : forall k BR jst jc c st st' i v r,
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (L.expr_id i)) (L.out_ter st' r) ->
    Mem (i, v) LjsInitEnv.ctx_items ->
    st = st' /\ r = L.res_value v.
Proof.
    introv Hinv Hlred Hmem.
    inverts Hlred.
    forwards Hic : state_invariant_includes_init_ctx Hinv; eauto.
    substs; eauto.
Qed.

Lemma red_spec_to_boolean_ok : forall k' k jst jc c st st' r je BR, 
    (k <= k')%nat ->
    ih_expr k' ->
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (E.to_bool (js_expr_to_ljs je))) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value_conv J.spec_to_boolean je) 
       (fun jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
           r = L.res_value (L.bool_to_value b)).
Proof.
    introv Hleq IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    forwards (Hlol1&Hlol2) : builtin_assoc Hinv H4.
    unfold LjsInitEnv.ctx_items.
    repeat (eapply Mem_here || apply Mem_next). (* TODO VERY SLOW! *)
    clear H4.
    substs.

    inv_internal_fwd_ljs.
    inv_internal_fwd_ljs.
    ljs_out_redh_ter.

    apply_ih_expr.
    destr_concl.

    inv_internal_fwd_ljs.
    inv_internal_fwd_ljs.

    autoforwards Hbool : ljs_to_bool_lemma.
    destruct_hyp Hbool.
    solve [repeat intuition jauto_js].

    inv_internal_ljs.
    inv_internal_fwd_ljs.

    jauto_js.

    solve [repeat intuition jauto_js].
Qed.

Lemma res_related_abort : forall BR jst jst' st jr r,
    res_related BR jst st jr r ->
    J.abort (J.out_ter jst' jr) ->
    L.res_is_control r.
Proof.
    introv Hrel Hab.
    inverts Hrel.
    inverts Hab. unfold J.res_is_normal in *. simpls. false.
    eapply L.res_is_control_exception.
    eapply L.res_is_control_break.
Qed.

Lemma red_stat_if2_ok : forall k je jt1 jt2,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt1 (Some jt2)).
Proof.
    introv IHt IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.
    autoforwards Hh : red_spec_to_boolean_ok. 
    destr_concl.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs. 
    apply_ih_stat.
    jauto_js.
    (* abort *)
    inv_internal_ljs; jauto_js.
Qed.

(* TODO move *)
Ltac inv_literal_ljs := 
    let H := match goal with
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_empty) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_true) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_false) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_null) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic L.expr_undefined) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic (L.expr_number _)) _ |- _ => constr:H
    | H : L.red_exprh _ _ _ (L.expr_basic (L.expr_string _)) _ |- _ => constr:H
    end in inverts H.

Lemma red_stat_if1_ok : forall k je jt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt None).
Proof.
    introv IHt IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.
    autoforwards Hh : red_spec_to_boolean_ok. 
    destr_concl.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs.
    inv_literal_ljs.
    jauto_js.
    (* abort *)
    inv_internal_ljs; jauto_js.
Qed.

Lemma red_stat_if_ok : forall k je jt ojt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt ojt).
Proof.
    introv IHt IHe.
    destruct ojt.
    applys red_stat_if2_ok; eassumption.
    applys red_stat_if1_ok; eassumption.
Qed.

Lemma red_stat_throw_ok : forall k je,
    ih_expr k ->
    th_stat k (J.stat_throw je).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred as Hlred'.
    ljs_out_redh_ter.
    inverts Hlred'.
    repeat inv_internal_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_expr.
    destr_concl. (* TODO seems like something to automate *)
        repeat inv_internal_fwd_ljs.
        jauto_js.
        skip. (* TODO *)
        skip. (* TODO *)
    inv_internal_ljs.
    jauto_js.
    inv_internal_ljs.
    jauto_js.
Qed.

Lemma red_stat_return_ok : forall k oje,
    ih_expr k ->
    th_stat k (J.stat_return oje).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.
    destruct oje as [je|].
    apply_ih_expr.
    inv_internal_ljs.
    jauto_js.
    injects.
    jauto_js.
    jauto_js.
    ljs_abort.
    simpls.
    inv_literal_ljs.
    inv_internal_fwd_ljs.
    jauto_js.
Qed.

Lemma main_lemma : forall k, (forall jt, th_stat k jt) /\ (forall je, th_expr k je).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    asserts IHt : (ih_stat k). unfolds. introv Hle. specializes IH Hle. jauto.
    asserts IHe : (ih_expr k). unfolds. introv Hle. specializes IH Hle. jauto.
    clear IH.
    splits.
    (* STATEMENTS *)
    destruct 0.
    (* stat_expr *)
    applys red_stat_expr_ok; eassumption.
    (* stat_label *)
    skip.
    (* stat_block *)
    skip.
    (* stat_var_decl *)
    skip.
    (* stat_if *)
    applys red_stat_if_ok; eassumption.
    (* stat_do_while *)
    skip.
    (* stat_while *)
    skip.
    (* stat_with *)
    skip.
    (* stat_throw *)
    applys red_stat_throw_ok; eassumption.
    (* stat_return *)
    applys red_stat_return_ok; eassumption.
    (* stat_break *)
    skip.
    (* stat_continue *)
    skip.
    (* stat_try *)
    skip.
    (* stat_for *)
    skip.
    (* stat_for_var *)
    skip.
    (* stat_for_in *)
    skip.
    (* stat_for_in_var *)
    skip.
    (* stat_debugger *)
    skip.
    (* stat_switch *)
    skip.
    (* EXPRESSIONS *)
    destruct 0.
    (* expr_this *)
    skip.
    (* expr_identifier *)
    skip.
    (* expr_literal *)
    eapply red_expr_literal_ok.
    (* expr_object *)
    skip.
    (* expr_function *)
    skip.
    (* expr_access *)
    skip.
    (* expr_member *)
    skip.
    (* expr_new *)
    skip.
    (* expr_call *)
    skip.
    (* expr_unary_op *)
    skip.
    (* expr_binary_op *)
    skip.
    (* expr_conditional *)
    skip.
    (* expr_assign *)
    skip.
Qed.

(*

Lemma red_identifier_ok : forall jst jc st c o i BR,
    heaps_bisim BR jst st ->
    L.red_expr c st (js_expr_to_ljs (J.expr_identifier i)) o ->
    exists jo,
    J.red_expr jst jc (J.expr_basic (J.expr_identifier i)) jo /\
    out_related BR jo o.
Proof.
*)
