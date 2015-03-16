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
Include LjsCommon.
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
Implicit Type jt : J.stat.
Implicit Type jee : J.ext_expr.
Implicit Type jet : J.ext_stat.
Implicit Type jes : J.ext_spec.
Implicit Type jc : J.execution_ctx.
Implicit Type jo : J.out.
Implicit Type jr : J.res.
Implicit Type jv : J.value.
Implicit Type jptr : J.object_loc.
Implicit Type jobj : J.object.
Implicit Type jrv : J.resvalue.
Implicit Type jref : J.ref.
Implicit Type jl : J.label.

Definition object_bisim := J.object_loc -> L.object_ptr -> Prop.

Implicit Type BR : object_bisim.

Inductive value_related BR : J.value -> L.value -> Prop :=
| value_related_null : value_related BR (J.value_prim J.prim_null) L.value_null
| value_related_undefined : value_related BR (J.value_prim J.prim_undef) L.value_undefined
| value_related_number : forall n, value_related BR (J.value_prim (J.prim_number n)) (L.value_number n)
| value_related_string : forall s, value_related BR (J.value_prim (J.prim_string s)) (L.value_string s)
| value_related_bool : forall b, value_related BR (J.value_prim (J.prim_bool b)) (L.value_bool b)
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

Definition object_attributes_related BR jobj obj := forall s, 
    ~J.Heap.indom (J.object_properties_ jobj) s /\ ~index (L.object_properties obj) s \/
    exists jptr ptr, 
        J.Heap.binds (J.object_properties_ jobj) s jptr /\ binds (L.object_properties obj) s ptr /\
        attributes_related BR jptr ptr.

Definition object_prim_related BR jobj obj := 
    J.object_class_ jobj = L.object_class obj /\
    J.object_extensible_ jobj = L.object_extensible obj.

Definition object_related BR jobj obj :=
    object_prim_related BR jobj obj /\
    object_attributes_related BR jobj obj.

Definition heaps_bisim_lfun BR :=
    forall jptr ptr1 ptr2, BR jptr ptr1 -> BR jptr ptr2 -> ptr1 = ptr2.

Definition heaps_bisim_rfun BR :=
    forall jptr1 jptr2 ptr, BR jptr1 ptr -> BR jptr2 ptr -> jptr1 = jptr2.

Definition heaps_bisim_ltotal BR jst :=
    forall jptr, J.object_indom jst jptr -> exists ptr, BR jptr ptr.

Definition heaps_bisim_lnoghost BR jst :=
    forall jptr ptr, BR jptr ptr -> J.object_indom jst jptr.

Definition heaps_bisim_rnoghost BR st :=
    forall jptr ptr, BR jptr ptr -> index st ptr.

Definition heaps_bisim BR jst st := forall jptr ptr jobj obj, 
     BR jptr ptr -> 
     J.object_binds jst jptr jobj ->
     binds st ptr obj ->
     object_related BR jobj obj.

Record heaps_bisim_consistent BR jst st : Prop := {
    heaps_bisim_consistent_bisim : heaps_bisim BR jst st;
    heaps_bisim_consistent_lfun : heaps_bisim_lfun BR;
    heaps_bisim_consistent_rfun : heaps_bisim_rfun BR;
    heaps_bisim_consistent_ltotal : heaps_bisim_ltotal BR jst;
    heaps_bisim_consistent_lnoghost : heaps_bisim_lnoghost BR jst;
    heaps_bisim_consistent_rnoghost : heaps_bisim_rnoghost BR st
}.

Definition js_literal_to_ljs jli := E.ejs_to_ljs (E.js_literal_to_ejs jli).
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
    res_related BR jst st (J.res_intro J.restype_normal jrv J.label_empty) 
        (L.res_value v)
| res_related_throw : forall jrv ptr obj v,
    binds st ptr obj ->
    js_exn_object obj v ->
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_throw jrv J.label_empty) 
        (L.res_exception (L.value_object ptr))
| res_related_return : forall jrv v,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_return jrv J.label_empty) 
        (L.res_break "%ret" v)
| res_related_break : forall jrv v jl,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_break jrv jl) 
        (L.res_break (E.js_label_to_ejs "%break" jl) v)
| res_related_continue : forall jrv v jl,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_continue jrv jl) 
        (L.res_break (E.js_label_to_ejs "%continue" jl) v)
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

Hint Extern 4 (js_exn_object _ _) => unfold js_exn_object : js_ljs.

Hint Constructors J.red_expr : js_ljs.
Hint Constructors J.red_stat : js_ljs.
Hint Constructors J.red_spec : js_ljs.
Hint Constructors J.abort : js_ljs.

Definition includes_init_ctx c :=
    forall i v v', binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'. 

Inductive state_invariant BR jst jc c st : Prop := {
    state_invariant_heaps_bisim_consistent : heaps_bisim_consistent BR jst st;
    state_invariant_includes_init_ctx : includes_init_ctx c
}.

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

Definition concl_spec {A : Type} BR jst jc c st st' r jes (P : A -> Prop) :=
    exists jst',
    state_invariant BR jst' jc c st' /\ 
    ((exists x, J.red_spec jst jc jes (J.specret_val jst' x) /\ P x) \/
     (exists jr, 
        J.red_spec jst jc jes (@J.specret_out A (J.out_ter jst' jr)) /\ 
        J.abort (J.out_ter jst' jr) /\
        res_related BR jst' st' jr r)).

Definition concl_expr_getvalue BR jst jc c st st' r je :=
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value je) 
       (fun jv => exists v, r = L.res_value v /\ value_related BR jv v).

Definition th_expr k je := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr_getvalue BR jst jc c st st' r je.

Definition th_stat k jt := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_stat_to_ljs jt)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r jt.

Definition th_spec {A : Type} k e jes (P : L.ctx -> L.store -> L.res -> A -> Prop) := 
    forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic e) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r jes (P c st' r).

Definition ih_expr k := forall je k', (k' < k)%nat -> th_expr k' je.

Definition ih_stat k := forall jt k', (k' < k)%nat -> th_stat k' jt.

Ltac ljs_abort := match goal with
    | H : L.abort (L.out_ter _ (L.res_value _)) |- _ => 
        let H1 := fresh "H" in 
        solve [invert H as H1; inverts H1]
    end.

Ltac inv_ljs_in H :=
    inversions H; try ljs_abort.

Ltac inv_fwd_ljs_in H :=
    (inversions H; try ljs_abort); [idtac].
 
Ltac with_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        match ee with 
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *)
        | _ => T H
        end
    end.

Ltac with_internal_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        match ee with 
        | L.expr_basic _ => fail 1
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *) 
        | _ => T H
        end
    end.

Ltac inv_internal_ljs := with_internal_red_exprh inv_ljs_in.

Ltac inv_fwd_ljs := with_red_exprh inv_fwd_ljs_in.

Ltac inv_internal_fwd_ljs := with_internal_red_exprh inv_fwd_ljs_in.

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

Ltac js_ljs_false_invert := match goal with 
    | H : J.abort_intercepted_stat _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_spec _ |- _ => solve [inverts H]
    | H : J.res_is_normal _ |- _ => inverts H
    end.

Hint Extern 10 => js_ljs_false_invert : js_ljs.

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
        let Hih := fresh "IH" in
        asserts Hle : (k < k')%nat; [omega | lets Hih : H Hle HS HR; clear Hle; clear HR]
    end.

Ltac apply_ih_stat := match goal with
    | H : ih_stat ?k', HS : state_invariant _ _ _ ?c ?st, 
      HR : L.red_exprh ?k ?c ?st (L.expr_basic _) _ |- _ => 
        let Hle := fresh "Hle" in
        asserts Hle : (k < k')%nat; [omega | lets Hih : H Hle HS HR; clear Hle; clear HR]
    end.

Hint Extern 1 (J.regular_unary_op _) =>
    solve [let H := fresh "H" in intro H; unfolds in H; destruct_hyp H; inverts H] : js_ljs.

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

Ltac jauto_js := repeat destr_concl; jauto_set; eauto with js_ljs bag typeclass_instances; 
    repeat (try unfold_concl; jauto_set; eauto with js_ljs bag typeclass_instances).

Ltac ijauto_js := repeat intuition jauto_js.

Ltac solve_ijauto_js := solve [ijauto_js].

(* HERE START PROOFS *)

(* Lemmas about invariants *)

Hint Extern 1 (?x <> _) => solve [intro; subst x; false]. (* TODO move *)

Lemma heaps_bisim_nindex_preserved : forall BR jst st ptr obj,
    ~index st ptr ->
    heaps_bisim_consistent BR jst st ->
    heaps_bisim_consistent BR jst (st \( ptr := obj)).
Proof.
    introv Hni Hbi.
    inverts Hbi as Hbisim Hlfun Hrfun Hltotal Hlnoghost Hrnoghost.
    constructor; auto.
    unfolds heaps_bisim.
    introv Hrel Hjb Hlb.
    specializes Hrnoghost Hrel.
    eapply Hbisim; try eassumption.
    eapply binds_update_diff_inv; try eassumption; auto. 
    unfolds heaps_bisim_rnoghost.
    prove_bag.
Qed.

Lemma state_invariant_nindex_preserved : forall BR jst jc c st ptr obj,
    ~index st ptr ->
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c (st \( ptr := obj )).
Proof.
    introv Hni Hinv.
    inverts Hinv.
    constructor.
    apply heaps_bisim_nindex_preserved; auto.
    assumption.
Qed.

Lemma state_invariant_fresh_preserved : forall BR jst jc c st obj,
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c (st \( fresh st := obj )).
Proof.
    introv Hinv.
    apply state_invariant_nindex_preserved; prove_bag.
Qed.

Hint Resolve state_invariant_fresh_preserved : js_ljs.

(* Prerequisites *)

Lemma ih_expr_leq : forall k k', (k' <= k)%nat -> ih_expr k -> ih_expr k'.
Proof.
    introv Hle He Hlt.
    apply He. omega.
Qed.

Lemma ih_stat_leq : forall k k', (k' <= k)%nat -> ih_stat k -> ih_stat k'.
Proof.
    introv Hle He Hlt.
    apply He. omega.
Qed.

Lemma ih_expr_S : forall k, ih_expr (S k) -> ih_expr k.
Proof.
    introv He. eapply ih_expr_leq; try eassumption; omega.
Qed.

Lemma ih_stat_S : forall k, ih_stat (S k) -> ih_stat k.
Proof.
    introv He. eapply ih_stat_leq; try eassumption; omega.
Qed.

(* TODO move this lemma! *)
Lemma get_closure_aux_lemma : forall k st clo, LjsCommon.get_closure_aux k st (L.value_closure clo) = L.result_some clo.
Proof.
    destruct k; reflexivity.
Qed.

Lemma get_closure_lemma : forall st clo, LjsCommon.get_closure st (L.value_closure clo) = L.result_some clo.
Proof.
    intros. unfolds. rewrite get_closure_aux_lemma. reflexivity.
Qed. 

Tactic Notation "if" tactic(t1) "then" tactic(t2) := match True with _ => (try (t1; fail 1); fail 1) || t2 end.

Ltac ljs_apply := 
    match goal with
    | H1 : LjsCommon.get_closure _ ?e = L.result_some ?clo, H2 : L.closure_ctx ?clo _ = L.result_some _ |- _ =>
        (try unfold e in H1); rewrite get_closure_lemma in H1; injects H1; injects H2
    end.

Ltac binds_inv := 
    match goal with
    | H : binds (_ \(?x:=?v1)) ?x ?v2 |- _ => 
        let He := fresh "H" in
        forwards He : (binds_update_same_inv _ _ _ _ H);
        subst v2; clear H
    end.

Lemma state_invariant_includes_init_ctx_lemma : forall BR jst jc c st i v v',
    state_invariant BR jst jc c st ->
    binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'.
Proof.
    introv Hinv.
    inverts Hinv.
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
    forwards Hic : state_invariant_includes_init_ctx_lemma Hinv; eauto.
    substs; eauto.
Qed.

Ltac ljs_get_builtin :=
    match goal with
    | Hinv : state_invariant _ _ _ ?c ?st,
      H : L.red_exprh _ ?c ?st (L.expr_basic (E.make_builtin _)) _ |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        forwards (H1&H2) : builtin_assoc Hinv H; [
        unfold LjsInitEnv.ctx_items;
        solve [repeat (eapply Mem_here || apply Mem_next)] | 
        clear H;
        subst_hyp H1; subst_hyp H2 ]
    end.

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
    eapply L.res_is_control_break.
    eapply L.res_is_control_break.
Qed.

Ltac ljs_abort_from_js := 
    match goal with
    | Hja : J.abort (J.out_ter ?jst ?jr), Hc : context [L.out_ter ?st ?r],
      Hrel : res_related _ ?jst ?st ?jr ?r |- _ => 
      not is_hyp (L.abort (L.out_ter st r));
      let H := fresh "H" in
      assert (H : L.abort (L.out_ter st r)); 
      [solve [applys L.abort_control (res_related_abort Hrel Hja)] | idtac] 
    end.

Hint Extern 0 (~ _) => solve [let H := fresh in intro H; inversion H].

Ltac ljs_propagate_abort :=
    match goal with
    | Habort : L.abort (L.out_ter ?st ?r), Hred : context [L.out_ter ?st ?r] |- _ =>
    match type of Hred with
    | L.red_exprh ?k ?c ?st0 ?ee (L.out_ter ?st' ?r') => 
        let H := fresh "H" in
        assert (H : L.red_exprh k c st0 ee (L.out_ter st r));
        [applys L.red_exprh_general_abort; solve [trivial] | idtac];
        let Hdet := fresh "H" in
        forwards Hdet : L.red_exprh_deterministic Hred H;
        injects Hdet;
        clear H Hred
    end
    end.

Ltac ljs_handle_abort := progress (repeat (ljs_propagate_abort || ljs_abort_from_js)); solve_ijauto_js.

Ltac specialize_th_spec H :=
    match type of H with
    | th_spec _ ?e _ _ => 
    match goal with
    | H1 : L.red_exprh _ ?c ?st (L.expr_basic ?e') _, H2 : state_invariant _ _ _ ?c ?st |- _ => 
        unify e e';
        specializes H H2 H1;
        clear H2; clear H1
    end
    end.

Ltac specialize_th_stat H :=
    match type of H with
    | th_stat ?k ?jt => 
    match goal with
    | H1 : L.red_exprh k ?c ?st (L.expr_basic ?e') _, H2 : state_invariant _ _ _ ?c ?st |- _ => 
        unify (js_stat_to_ljs jt) e';
        specializes H H2 H1;
        clear H2; clear H1 
    end 
    end.

Ltac forwards_th Hth := let H := fresh "H" in 
    (forwards H : Hth;
    first [is_var H; (specialize_th_spec H || specialize_th_stat H) | idtac];
    try (eapply ih_expr_leq; try eassumption; omega)); 
    [idtac].

Lemma res_related_invert_abort_lemma : forall BR jst st jr r,
    res_related BR jst st jr r ->
    (exists jrv v, 
        jr = J.res_intro J.restype_normal jrv J.label_empty /\
        r = L.res_value v /\ 
        resvalue_related BR jrv v) \/
    J.abort (J.out_ter jst jr) /\ L.abort (L.out_ter st r).
Proof.
    introv Hrel.
    inverts Hrel; ijauto_js.
Qed.

Ltac res_related_abort :=
    match goal with
    | H : res_related _ ?jst ?st ?jr ?r |- _ =>
        not is_hyp (J.abort (J.out_ter jst jr));
        let Hr := fresh "H" in
        forwards Hr : res_related_invert_abort_lemma H;
        destruct_hyp Hr; [clear H | idtac]
    end.

Ltac destr_concl_auto := destr_concl; res_related_abort; try ljs_handle_abort.

(* Lemmas about operators *)

(* TODO *)

(* Lemmas about the environment *)

Lemma ljs_to_bool_lemma : forall k BR jst jc c st st' r jv v,
    state_invariant BR jst jc c st ->
    value_related BR jv v -> 
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privToBoolean [v]) (L.out_ter st' r) ->
    st = st' /\
    exists b,
    r = L.res_value (L.value_bool b) /\
    J.red_expr jst jc (J.spec_to_boolean jv) 
        (J.out_ter jst (J.res_val (J.value_prim (J.prim_bool b)))).
Proof.
    introv Hinv Hrel Hlred.

    inverts Hlred.
    ljs_apply.
    repeat inv_fwd_ljs.

    binds_inv.

    inverts Hrel; try injects; jauto_js. 
    cases_if; 
    simpl; unfold J.convert_number_to_bool; cases_if; reflexivity.
    cases_if; 
    simpl; unfold J.convert_string_to_bool; cases_if; reflexivity.
    destruct b; injects; reflexivity.
Qed.

(* Internal operations *)

Lemma red_spec_to_boolean_ok : forall k je, 
    ih_expr k ->
    th_spec k (E.to_bool (js_expr_to_ljs je))
              (J.spec_expr_get_value_conv J.spec_to_boolean je) 
              (fun _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
                  r = L.res_value (L.value_bool b)).
Proof.
    introv IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    ljs_get_builtin.

    repeat inv_internal_fwd_ljs.
    ljs_out_redh_ter.

    apply_ih_expr.

    destr_concl; try ljs_handle_abort.

    repeat inv_internal_fwd_ljs.

    autoforwards Hbool : ljs_to_bool_lemma.
    destruct_hyp Hbool.
    solve_ijauto_js.
Qed.

(* Expressions *)

Lemma red_expr_literal_ok : forall k l,
    th_expr k (J.expr_literal l).
Proof.
    introv.
    unfolds.
    introv Hinv Hlred.
    destruct l as [ | [ | ] | | ]; inverts Hlred; ijauto_js.
Qed.

Lemma red_expr_identifier_ok : forall k i,
    th_expr k (J.expr_identifier i).
Proof.
    introv Hinv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.

    ljs_get_builtin.

    repeat inv_fwd_ljs.
    skip.
Qed.

Hint Extern 11 => match goal with |- context [If _ then _ else _] => case_if end : js_ljs.

Lemma red_expr_conditional_ok : forall k je1 je2 je3,
    ih_expr k ->
    th_expr k (J.expr_conditional je1 je2 je3).
Proof.
    introv IHe Hinv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.

    forwards_th red_spec_to_boolean_ok. 

    destr_concl.
    destruct b;
    inv_internal_fwd_ljs;
    apply_ih_expr.
    (* true *)
    repeat destr_concl; unfold_concl.
    jauto_set.
    jauto_js.
    left.
    jauto_set.
    econstructor;
    jauto_js.
    jauto_js.
    jauto_js.

    jauto_set.
    jauto_js.
    right.
    jauto_set.
    eapply J.red_spec_expr_get_value.
    eapply J.red_expr_conditional.
    eassumption.
    eapply J.red_expr_conditional_1.
    reflexivity.
    jauto_js.
    econstructor; ijauto_js.
    false_invert.
    eapply J.red_spec_abort.
    reflexivity.
    assumption. 
    ijauto_js.    
    ijauto_js.
    ijauto_js.
    (* false *)
    repeat destr_concl; unfold_concl.
    jauto_set.
    jauto_js.
    left.
    jauto_set.
    econstructor;
    jauto_js.
    jauto_js.
    jauto_js.

    jauto_set.
    jauto_js.
    right.
    jauto_set.
    eapply J.red_spec_expr_get_value.
    eapply J.red_expr_conditional.
    eassumption.
    eapply J.red_expr_conditional_1.
    reflexivity.
    jauto_js.
    econstructor; ijauto_js.
    false_invert.
    eapply J.red_spec_abort.
    reflexivity.
    assumption. 
    ijauto_js.    
    ijauto_js.
    ijauto_js.
    (* abort *)
    ljs_abort_from_js.
    ljs_propagate_abort.
    unfold_concl.
    jauto_set.
    eassumption.
    right.
    jauto_set.
    eapply J.red_spec_expr_get_value.
    eapply J.red_expr_conditional.
    eassumption.
    eapply J.red_expr_abort.
    reflexivity.
    eassumption.
    trivial.
    eapply J.red_spec_abort.
    reflexivity.
    eassumption.
    trivial.
    eassumption.
    eassumption.
Qed.

Lemma red_expr_assign0_ok : forall k je1 je2,
    ih_expr k ->
    th_expr k (J.expr_assign je1 None je2).
Proof.
Admitted.

Lemma red_expr_unary_op_not_ok : forall k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op J.unary_op_not je).
Proof.
    introv IHe Hinv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.
(* TODO better lemma about to_bool *)
    (* abort *)
(*
    repeat (ljs_propagate_abort || ljs_abort_from_js).
    inverts H2. skip.
    jauto_js.
    right; jauto_js.
    eapply J.red_spec_expr_get_value.
    eapply J.red_expr_unary_op.
    jauto_js.
    eapply H9.
    inverts H9. skip.
    eapply J.red_expr_unary_op_1.
    jauto_js.
    eapply J.red_expr_unary_op_not. *)
    skip.
Qed.

Lemma red_expr_unary_op_ok : forall op k je,
    ih_expr k ->
    th_expr k (J.expr_unary_op op je).
Proof.
    destruct op.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    skip.
    apply red_expr_unary_op_not_ok.
Qed.

(* Statements *)

Lemma list_rev_ind
     : forall (A : Type) (P : list A -> Prop),
       P [] ->
       (forall (a : A) (l : list A), P l -> P (l & a)) ->
       forall l : list A, P l.
Proof.
    introv Hbase Hstep.
    intro l.
    asserts (l'&Heq) : (exists l', l = rev l').
    exists (rev l). rew_rev. reflexivity.
    gen l.
    induction l'; intros; substs; rew_rev; auto.
Qed.

(* TODO move this lemma *)
Lemma list_map_tlc : forall A B (f : A -> B) l, 
    List.map f l = map f l.
Proof.
    induction l.
    reflexivity.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma stat_block_ejs_last_lemma : forall jts jt,
    E.js_stat_to_ejs (J.stat_block (jts & jt)) = 
        E.expr_seq (E.js_stat_to_ejs (J.stat_block jts)) (E.js_stat_to_ejs jt).
Proof.
    intros. 
    unfolds E.js_stat_to_ejs. 
    unfolds E.expr_seqs.
    rewrite_all list_map_tlc.
    rew_list.
    reflexivity.
Qed.

(* TODO move *)
Lemma res_related_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_normal jrv2))
        (L.res_value (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2.
    unfold J.res_overwrite_value_if_empty.
    cases_if; substs.
    (* empty *)
    inverts Hrel2.
    eapply res_related_normal.
    assumption.
    (* nonempty *)
    destruct jrv2;
    inverts Hrel2 as Hvrel2; tryfalse.
    inverts Hvrel2; jauto_js.
Qed.
    Hint Resolve res_related_overwrite_if_empty : js_ljs.

Lemma red_stat_block_ok : forall jts k, 
    ih_stat k -> 
    th_stat k (J.stat_block jts).
Proof.
    induction jts using list_rev_ind;
    introv IH Hinv Hlred.
    inv_fwd_ljs.
    jauto_js.
    unfolds js_stat_to_ljs.
    rewrite stat_block_ejs_last_lemma in *.
    inv_fwd_ljs.
    ljs_out_redh_ter.
    specializes IHjts (ih_stat_S IH). 

    specialize_th_stat IHjts.
    destr_concl_auto. 
    inv_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_stat.
    destr_concl_auto.

    inv_fwd_ljs.
    ijauto_js.
    econstructor 3; ijauto_js. (* TODO why auto does not handle this? *)
    econstructor 4; ijauto_js.

    skip. (* TODO! TODO! *)
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

Lemma red_stat_if2_ok : forall k je jt1 jt2,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt1 (Some jt2)).
Proof.
    introv IHt IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    forwards_th red_spec_to_boolean_ok. 

    destr_concl; try ljs_handle_abort.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs. 
    apply_ih_stat.
    jauto_js.
Qed.

Lemma red_stat_if1_ok : forall k je jt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_if je jt None).
Proof.
    introv IHt IHe Hinv Hlred.
    inverts Hlred.
    ljs_out_redh_ter.

    forwards_th red_spec_to_boolean_ok.
 
    destr_concl; try ljs_handle_abort.
    destruct b.
    (* true *)
    inv_internal_fwd_ljs.
    apply_ih_stat. 
    jauto_js.
    (* false *)
    inv_internal_fwd_ljs.
    inv_literal_ljs.
    jauto_js.
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
    inversions Hlred'.
    repeat inv_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_expr.
    destr_concl; try ljs_handle_abort.
(* TODO seems like something to automate *)
    repeat (ljs_out_redh_ter || inv_fwd_ljs).
    repeat injects.
    jauto_js.
    eapply res_related_throw; (* TODO why auto doesn't fire on this? *)
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

Lemma red_stat_break_ok : forall k jl,
    th_stat k (J.stat_break jl).
Proof.
    introv Hinv Hlred.
    repeat inv_fwd_ljs.
    jauto_js.
Qed.

Lemma red_stat_continue_ok : forall k jl,
    th_stat k (J.stat_continue jl).
Proof.
    introv Hinv Hlred.
    repeat inv_fwd_ljs.
    jauto_js.
Qed.

Lemma red_stat_label_ok : forall k s jt,
    ih_stat k ->
    th_stat k (J.stat_label s jt).
Proof.
    introv IHt Hinv Hlred.
    repeat inv_fwd_ljs.
    ljs_out_redh_ter.
    apply_ih_stat.

    destr_concl.
    inverts Hih3; (* TODO tactic *)
    repeat inv_fwd_ljs.
    jauto_js.

    skip. (* TODO cases, good tactics *)
    skip.
    skip.
    skip.
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
    applys red_stat_label_ok; eassumption.
    (* stat_block *)
    applys red_stat_block_ok; eassumption.
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
    applys red_stat_break_ok.
    (* stat_continue *)
    applys red_stat_continue_ok.
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
    eapply red_expr_identifier_ok.
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
    applys red_expr_conditional_ok; eassumption.
    (* expr_assign *)
    skip.
Qed.

