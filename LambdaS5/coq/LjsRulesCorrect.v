Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
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
Include JsSyntaxAux.
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
Implicit Type props : L.object_props.

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
Implicit Type jer : J.env_record.
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.

(* Desugaring for literals, expressions and statements. *)
Definition js_literal_to_ljs jli := E.ejs_to_ljs (E.js_literal_to_ejs jli).
Definition js_expr_to_ljs je := E.ejs_to_ljs (E.js_expr_to_ejs je).
Definition js_stat_to_ljs jt := E.ejs_to_ljs (E.js_stat_to_ejs jt).

(* Relates JS objects to LJS objects. 
 * Properties it should satisfy will be defined later. *)
Definition object_bisim := J.object_loc -> L.object_ptr -> Prop.

Implicit Type BR : object_bisim.

(* Relates JS values to LJS values.
 * Note that this implies that LJS lambdas and empty are never seen directly by JS code. *)
Inductive value_related BR : J.value -> L.value -> Prop :=
| value_related_null : value_related BR (J.value_prim J.prim_null) L.value_null
| value_related_undefined : value_related BR (J.value_prim J.prim_undef) L.value_undefined
| value_related_number : forall n, value_related BR (J.value_prim (J.prim_number n)) (L.value_number n)
| value_related_string : forall s, value_related BR (J.value_prim (J.prim_string s)) (L.value_string s)
| value_related_bool : forall b, value_related BR (J.value_prim (J.prim_bool b)) (L.value_bool b)
| value_related_object : forall jptr ptr, 
    (jptr, ptr) \in BR -> value_related BR (J.value_object jptr) (L.value_object ptr) 
.

(* Relates JS object attributes to LJS object attributes. *)
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

(* Relates attributes of JS objects to LJS.
 * States that for every attribute name, the attribute is undefined in both JS and LJS objects,
 * or it's defined in both and related. *)
Definition object_properties_related BR jprops props := forall s, 
    ~J.Heap.indom jprops s /\ ~index props s \/
    exists jptr ptr, 
        J.Heap.binds jprops s jptr /\ binds props s ptr /\
        attributes_related BR jptr ptr.

(* Relates internal fields of JS objects to JLS. *)
Definition object_prim_related BR jobj obj := 
    J.object_class_ jobj = L.object_class obj /\
    J.object_extensible_ jobj = L.object_extensible obj.

(* Relates JS objects to LJS objects. *)
Definition object_related BR jobj obj :=
    object_prim_related BR jobj obj /\
    object_properties_related BR (J.object_properties_ jobj) (L.object_properties obj).

(* Properties that must hold for heap bisimulations. *)
Definition heaps_bisim_ltotal BR jst :=
    forall jptr, J.object_indom jst jptr -> exists ptr, BR jptr ptr.

Definition heaps_bisim_lnoghost BR jst :=
    forall jptr ptr, BR jptr ptr -> J.object_indom jst jptr.

Definition heaps_bisim_rnoghost BR st :=
    forall jptr ptr, BR jptr ptr -> index st ptr.

Definition heaps_bisim BR jst st := forall jptr ptr jobj obj, 
     (jptr, ptr) \in BR -> 
     J.object_binds jst jptr jobj ->
     binds st ptr obj ->
     object_related BR jobj obj.

Record heaps_bisim_consistent BR jst st : Prop := {
    heaps_bisim_consistent_bisim : heaps_bisim BR jst st;
    heaps_bisim_consistent_lfun : functional BR;
    heaps_bisim_consistent_rfun : functional (flip BR);
    heaps_bisim_consistent_ltotal : heaps_bisim_ltotal BR jst;
(*    heaps_bisim_consistent_rtotal : heaps_bisim_rtotal BR st; TODO *)
    heaps_bisim_consistent_lnoghost : heaps_bisim_lnoghost BR jst;
    heaps_bisim_consistent_rnoghost : heaps_bisim_rnoghost BR st
}.

(* Relates JS resvalues ("maybe values") to LJS values. 
 * Resvalues are the results of statements. *)
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

(* Relates JS results to LJS results. *)
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

(* States that the initial LJS context ("the environment") can always be accessed
 * (and thus is never shadowed) *)
Definition includes_init_ctx c :=
    forall i v v', binds c i v -> Mem (i, v') LjsInitEnv.ctx_items -> v = v'. 

(* Relates declarative environment records *)
Definition decl_env_record_related BR jder props := forall s,
    ~J.Heap.indom jder s /\ ~index props s \/
    exists jmut jv acc, 
        J.Heap.binds jder s (jmut, jv) /\ 
        binds props s (L.attributes_accessor_of acc) /\
        True. (* TODO *)

(* Relates environment records *)
Inductive env_record_related BR : J.env_record -> L.object -> Prop :=
| env_record_related_decl : forall jder obj,
    decl_env_record_related BR jder (L.object_properties obj) ->
    env_record_related BR (J.env_record_decl jder) obj
(*
| env_record_related_object :
*)
.

(* Relates the lexical environment *)
Inductive lexical_env_related BR jst jc c st : J.lexical_env -> L.value -> Prop :=
| lexical_env_related_global : forall v,
    binds c "%globalContext" v ->
    lexical_env_related BR jst jc c st [J.env_loc_global_env_record] v
| lexical_env_related_cons : forall jeptr jlenv jer ptr obj,
    J.Heap.binds (J.state_env_record_heap jst) jeptr jer ->
    binds st ptr obj ->
    env_record_related BR jer obj ->
    lexical_env_related BR jst jc c st jlenv (L.object_proto obj) ->
    lexical_env_related BR jst jc c st (jeptr::jlenv) (L.value_object ptr)
.

(* Relates the lexical contexts *)
Record execution_ctx_related BR jst jc c st := {
    execution_ctx_related_this_binding : forall v,
        binds c "%this" v ->
        value_related BR (J.execution_ctx_this_binding jc) v;
    execution_ctx_related_strictness_flag : forall v, 
        binds c "#strict" v ->
        v = L.value_bool (J.execution_ctx_strict jc);
    execution_ctx_related_lexical_env : forall v ptr obj,
        binds c "%context" v ->
        lexical_env_related BR jst jc c st (J.execution_ctx_lexical_env jc) v
}.

(* States that the variable environment and lexical environment exist *)
Record env_records_exist jst jc := { 
    env_record_exist_variable_env : 
        Forall (J.Heap.indom (J.state_env_record_heap jst)) (J.execution_ctx_variable_env jc);
    env_record_exist_lexical_env : 
        Forall (J.Heap.indom (J.state_env_record_heap jst)) (J.execution_ctx_lexical_env jc)
}.

(* The complete set of invariants. *)
Record state_invariant BR jst jc c st : Prop := {
    state_invariant_heaps_bisim_consistent : heaps_bisim_consistent BR jst st;
    state_invariant_execution_ctx_related : execution_ctx_related BR jst jc c st;
    state_invariant_includes_init_ctx : includes_init_ctx c;
    state_invariant_env_records_exist : env_records_exist jst jc
}.

Definition concl_expr_value BR jst jc c st st' r je :=
    exists BR' jst' jr,
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_expr jst jc (J.expr_basic je) (J.out_ter jst' jr) /\ 
    res_related BR jst' st' jr r.

Definition concl_stat BR jst jc c st st' r jt :=
    exists BR' jst' jr,
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_stat jst jc (J.stat_basic jt) (J.out_ter jst' jr) /\ 
    res_related BR' jst' st' jr r.

Definition concl_spec {A : Type} BR jst jc c st st' r jes (P : object_bisim -> J.state -> A -> Prop) :=
    exists BR' jst',
    state_invariant BR' jst' jc c st' /\ 
    BR \c BR' /\
    ((exists x, J.red_spec jst jc jes (J.specret_val jst' x) /\ P BR' jst' x) \/
     (exists jr, 
        J.red_spec jst jc jes (@J.specret_out A (J.out_ter jst' jr)) /\ 
        J.abort (J.out_ter jst' jr) /\
        res_related BR' jst' st' jr r)).

Definition concl_expr_getvalue BR jst jc c st st' r je :=
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value je) 
       (fun BR' _ jv => exists v, r = L.res_value v /\ value_related BR' jv v).

Definition th_expr k je := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr_getvalue BR jst jc c st st' r je.

Definition th_stat k jt := forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic (js_stat_to_ljs jt)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r jt.

Definition th_spec {A : Type} k e jes 
    (P : object_bisim -> J.state -> J.execution_ctx -> L.ctx -> L.store -> L.res -> A -> Prop) := 
    forall BR jst jc c st st' r, 
    state_invariant BR jst jc c st ->
    L.red_exprh k c st (L.expr_basic e) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r jes (fun BR' jst' a => P BR' jst' jc c st' r a).

(* The form of the induction hypotheses. Height induction is used to make proofs simpler. *)

Definition ih_expr k := forall je k', (k' < k)%nat -> th_expr k' je.

Definition ih_stat k := forall jt k', (k' < k)%nat -> th_stat k' jt.

(* Automation *)

Create HintDb js_ljs discriminated.

Hint Constructors attributes_data_related : js_ljs.
Hint Constructors attributes_accessor_related : js_ljs. 
Hint Constructors attributes_related : js_ljs.
Hint Constructors value_related : js_ljs.
Hint Constructors resvalue_related : js_ljs.
Hint Constructors res_related : js_ljs.

Hint Extern 4 (js_exn_object _ _) => unfold js_exn_object : js_ljs.

Hint Extern 4 (res_related _ _ _ (J.res_throw _) _) => unfold J.res_throw : js_ljs.

Hint Constructors J.red_expr : js_ljs.
Hint Constructors J.red_stat : js_ljs.
Hint Constructors J.red_spec : js_ljs.
Hint Constructors J.abort : js_ljs.

Lemma res_related_break_hint : forall BR jst st jrv v jl s,
    resvalue_related BR jrv v -> s = E.js_label_to_ejs "%break" jl ->
    res_related BR jst st (J.res_intro J.restype_break jrv jl) 
        (L.res_break s v). 
Proof. intros. substs. eauto with js_ljs. Qed.

Lemma res_related_continue_hint : forall BR jst st jrv v jl s,
    resvalue_related BR jrv v -> s = E.js_label_to_ejs "%continue" jl ->
    res_related BR jst st (J.res_intro J.restype_continue jrv jl) 
        (L.res_break s v). 
Proof. intros. substs. eauto with js_ljs. Qed.

Hint Resolve res_related_break_hint : js_ljs.
Hint Resolve res_related_continue_hint : js_ljs.

Ltac ljs_abort := match goal with
    | H : L.abort (L.out_ter _ (L.res_value _)) |- _ => 
        let H1 := fresh "H" in 
        solve [invert H as H1; inverts H1]
    end.

Ltac inv_ljs_in H :=
    inversions H; try ljs_abort; tryfalse.

Ltac inv_fwd_ljs_in H :=
    (inversions H; try ljs_abort; tryfalse); [idtac].

Inductive inv_ljs_stop : L.ext_expr -> Prop := red_exprh_no_invert_intro : forall ee, inv_ljs_stop ee.

Ltac inv_ljs_stop ee := let STOP := fresh "STOP" in lets STOP : red_exprh_no_invert_intro ee.
 
Ltac with_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        match ee with 
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *)
        | _ => is_hyp (inv_ljs_stop ee); fail 1
        | _ => T H
        end
    end.

Ltac with_internal_red_exprh T :=
    match goal with
    | H	: L.red_exprh _ _ _ ?ee _ |- _ => 
        match ee with 
        | L.expr_basic _ => fail 1
        | L.expr_app_2 _ _ => fail 1 (* so that lemmas can be easily applied *) 
        | _ => is_hyp (inv_ljs_stop ee); fail 1
        | _ => T H
        end
    end.

Ltac inv_ljs := with_red_exprh inv_ljs_in.

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
    | H : J.abort_intercepted_expr _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_stat _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_spec _ |- _ => solve [inverts H]
    | H : J.abort_intercepted_stat (J.stat_label_1 _ _) |- _ => 
        solve [let H' := fresh "H" in inverts H as H'; [discriminate H' || injects H']; tryfalse]
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

Tactic Notation "jauto_js" integer(k) := repeat destr_concl; jauto_set; eauto with js_ljs bag typeclass_instances; 
    repeat (try unfold_concl; jauto_set; eauto k with js_ljs bag typeclass_instances).

Tactic Notation "jauto_js" := jauto_js 5.

Ltac solve_jauto_js := solve [jauto_js 50].

Ltac ijauto_js := repeat intuition jauto_js.

Ltac solve_ijauto_js := solve [ijauto_js; solve_jauto_js].

(* HERE START PROOFS *)

(* Lemmas about invariants *)

Lemma heaps_bisim_consistent_nindex_preserved : forall BR jst st ptr obj,
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

Lemma lexical_env_related_nindex_preserved : forall BR jst jc c st ptr obj jle v,
    ~index st ptr ->
    lexical_env_related BR jst jc c st jle v ->
    lexical_env_related BR jst jc c (st \( ptr := obj )) jle v.
Proof.
Admitted.

Lemma execution_ctx_related_nindex_preserved : forall BR jst jc c st ptr obj,
    ~index st ptr ->
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc c (st \( ptr := obj)).
Proof.
    introv Hni Hbi.
    inverts Hbi; constructor.
    auto.
    auto.
    intros. apply lexical_env_related_nindex_preserved; auto.
Qed.

Lemma state_invariant_nindex_preserved : forall BR jst jc c st ptr obj,
    ~index st ptr ->
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c (st \( ptr := obj )).
Proof.
    introv Hni Hinv.
    inverts Hinv.
    constructor.
    apply heaps_bisim_consistent_nindex_preserved; auto.
    apply execution_ctx_related_nindex_preserved; auto.
    assumption.
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

Lemma includes_init_ctx_incl_preserved : forall c c',
    c' \c c ->
    includes_init_ctx c ->
    includes_init_ctx c'.
Proof.
    unfolds includes_init_ctx.
    prove_bag.
Qed.

Lemma lexical_env_related_incl_preserved : forall BR jst jc c c' st jle v,
    c' \c c ->
    lexical_env_related BR jst jc c st jle v ->
    lexical_env_related BR jst jc c' st jle v.
Proof.
Admitted.

Lemma execution_ctx_related_incl_preserved : forall BR jst jc c c' st,
    c' \c c ->
    execution_ctx_related BR jst jc c st ->
    execution_ctx_related BR jst jc c' st.
Proof.
    introv Hincl Hrel.
    inverts Hrel.
    constructor.
    prove_bag.
    prove_bag.
    intros; eapply lexical_env_related_incl_preserved; prove_bag.
Qed.

Lemma state_invariant_ctx_incl_preserved : forall BR jst jc c c' st,
    c' \c c ->
    state_invariant BR jst jc c st ->
    state_invariant BR jst jc c' st.
Proof.
    introv Hincl Hinv.
    inverts Hinv.
    constructor.
    assumption.
    eapply execution_ctx_related_incl_preserved; eassumption.
    eapply includes_init_ctx_incl_preserved; eassumption.
    assumption.
Qed.

Hint Resolve state_invariant_ctx_incl_preserved : js_ljs.

Lemma value_related_bisim_incl_preserved : forall BR1 BR2 jv v,
    BR1 \c BR2 ->
    value_related BR1 jv v ->
    value_related BR2 jv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js. 
Qed.

Hint Resolve value_related_bisim_incl_preserved : js_ljs.

Lemma resvalue_related_bisim_incl_preserved : forall BR1 BR2 jrv v,
    BR1 \c BR2 ->
    resvalue_related BR1 jrv v ->
    resvalue_related BR2 jrv v.
Proof.
    introv Hs Hrel.
    inverts Hrel; jauto_js.
Qed.

Hint Resolve resvalue_related_bisim_incl_preserved : js_ljs.

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

(* TODO move utility tactic! *)
Tactic Notation "if" tactic(t1) "then" tactic(t2) := match True with _ => (try (t1; fail 1); fail 1) || t2 end.

(* TODO move S5-only tactics! *)
Ltac ljs_inv_value_is_closure :=
    match goal with
    | H : L.value_is_closure _ ?v _ |- _ => 
        unfold v in H; ljs_inv_value_is_closure 
    | H : L.value_is_closure _ (L.value_closure _) _ |- _ =>
        inverts H
    end.

Ltac ljs_inv_closure_ctx :=
    match goal with
    | H : L.closure_ctx (L.closure_intro _ _ _ _) _ _ |- _ =>
        let Hz := fresh "H" in
        inverts H as Hz; repeat (inverts Hz as Hz) (* crunching Zip *)
    end.

Ltac ljs_apply := progress repeat (ljs_inv_value_is_closure || ljs_inv_closure_ctx).

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
    rewrite from_list_update in H3.
    repeat rewrite from_list_empty in H3.
    rew_bag_simpl in H3.
(*    rew_bag_simpl in H3. *)
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
              (fun _ _ _ _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
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

(* TODO move *)
Lemma overwrite_value_if_empty_assoc : assoc L.overwrite_value_if_empty.
Proof.
    intros v1 v2 v3. destruct v3; reflexivity.
Qed.

Lemma overwrite_value_if_empty_left_empty : 
    neutral_l L.overwrite_value_if_empty L.value_empty.
Proof.
    intros v. destruct v; reflexivity.
Qed.

Lemma overwrite_value_if_empty_right_empty : 
    neutral_r L.overwrite_value_if_empty L.value_empty.
Proof.
    intros v. reflexivity.
Qed.

Lemma res_overwrite_value_if_empty_lemma : forall jrv jr,
    J.res_overwrite_value_if_empty jrv jr = 
        J.res_intro (J.res_type jr) (J.res_value (J.res_overwrite_value_if_empty jrv jr)) (J.res_label jr).
Proof.
    intros.
    unfold J.res_overwrite_value_if_empty.
    cases_if; substs; destruct jr;
    reflexivity.    
Qed.

Definition resvalue_overwrite_value_if_empty jrv1 jrv2 :=
    ifb jrv2 = J.resvalue_empty then jrv1 else jrv2.

Lemma resvalue_overwrite_value_if_empty_lemma : forall jrv1 jrv2 jrt jl,
    J.res_value (J.res_overwrite_value_if_empty jrv1 (J.res_intro jrt jrv2 jl)) =
        resvalue_overwrite_value_if_empty jrv1 jrv2.
Proof.
    introv. 
    unfold J.res_overwrite_value_if_empty.
    cases_if; substs; unfold resvalue_overwrite_value_if_empty; cases_if; reflexivity.
Qed.

Lemma resvalue_overwrite_value_if_empty_hint1 : forall jr jrv,
    (If J.res_value jr <> J.resvalue_empty then J.res_value jr else jrv) =
        J.res_value (J.res_overwrite_value_if_empty jrv jr).
Proof.
    intros. unfolds J.res_overwrite_value_if_empty. 
    repeat cases_if; destruct jr; reflexivity. 
Qed.

Hint Rewrite resvalue_overwrite_value_if_empty_lemma : js_ljs.
Hint Rewrite resvalue_overwrite_value_if_empty_hint1 : js_ljs.

Hint Extern 20 => progress autorewrite with js_ljs.

Lemma resvalue_related_overwrite_if_empty : forall BR jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    resvalue_related BR 
        (resvalue_overwrite_value_if_empty jrv1 jrv2) 
        (L.overwrite_value_if_empty v1 v2).
Proof.
    introv Hrel1 Hrel2.
    unfold resvalue_overwrite_value_if_empty.
    cases_if; substs. 
    (* empty *)
    inverts Hrel2.
    assumption.
    (* nonempty *)
    destruct jrv2;
    inverts Hrel2 as Hvrel2; tryfalse.
    inverts Hvrel2; jauto_js.
Qed.

Lemma resvalue_related_res_overwrite_if_empty : forall BR jrv1 jrv2 v1 v2 jrt jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    resvalue_related BR 
        (J.res_value (J.res_overwrite_value_if_empty jrv1 (J.res_intro jrt jrv2 jl))) 
        (L.overwrite_value_if_empty v1 v2).
Proof.
    introv Hrel1 Hrel2.
    rewrite resvalue_overwrite_value_if_empty_lemma.
    eauto using resvalue_related_overwrite_if_empty.
Qed.

Lemma res_related_value_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_normal jrv2))
        (L.res_value (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_normal. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma res_related_break_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2 s jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    s = E.js_label_to_ejs "%break" jl ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_intro J.restype_break jrv2 jl))
        (L.res_break s (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2 Hs. substs. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_break. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma res_related_continue_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2 s jl,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    s = E.js_label_to_ejs "%continue" jl ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_intro J.restype_continue jrv2 jl))
        (L.res_break s (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2 Hs. substs. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_continue. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Lemma res_related_return_overwrite_if_empty : forall BR jst st jrv1 jrv2 v1 v2,
    resvalue_related BR jrv1 v1 ->
    resvalue_related BR jrv2 v2 ->
    res_related BR jst st 
        (J.res_overwrite_value_if_empty jrv1 (J.res_intro J.restype_return jrv2 J.label_empty))
        (L.res_break "%ret" (L.overwrite_value_if_empty v1 v2)).
Proof.
    introv Hrel1 Hrel2. rewrite res_overwrite_value_if_empty_lemma.
    eapply res_related_return. 
    eauto using resvalue_related_res_overwrite_if_empty.
Qed.

Hint Resolve resvalue_related_overwrite_if_empty : js_ljs.
Hint Resolve res_related_value_overwrite_if_empty : js_ljs.
Hint Resolve res_related_break_overwrite_if_empty : js_ljs.
Hint Resolve res_related_continue_overwrite_if_empty : js_ljs.
Hint Resolve res_related_return_overwrite_if_empty : js_ljs.

Lemma res_related_invert_continue : forall BR jst st jr jl v,
    res_related BR jst st jr (L.res_break (E.js_label_to_ejs "%continue" jl) v) ->
    exists jrv,
    jr = J.res_intro J.restype_continue jrv jl /\
    resvalue_related BR jrv v.
Proof.
    introv Hrel.
    inverts Hrel.
    destruct jl; destruct jl0; repeat injects; tryfalse; eauto.
Qed.

Lemma res_related_invert_break : forall BR jst st jr jl v,
    res_related BR jst st jr (L.res_break (E.js_label_to_ejs "%break" jl) v) ->
    exists jrv,
    jr = J.res_intro J.restype_break jrv jl /\
    resvalue_related BR jrv v.
Proof.
    introv Hrel.
    inverts Hrel.
    destruct jl; destruct jl0; repeat injects; tryfalse; eauto.
Qed.

Ltac res_related_invert :=
    match goal with
    | H : res_related ?BR ?jst ?st ?jr ?r |- _ =>
(*      match goal with H1 : resvalue_related BR jst st _ _ |- _ => fail 2 | _ => idtac end; *)
        is_var jr; (* TODO better condition *)
        match r with
        | L.res_break (E.js_label_to_ejs "%continue" _) _ => 
            lets (?jrv&?H1&?H2) : (res_related_invert_continue H); subst jr
        | L.res_break (E.js_label_to_ejs "%break" _) _ => 
            lets (?jrv&?H1&?H2) : (res_related_invert_break H); subst jr
        | _ => inverts keep H 
        end
    end. 

(* workaround *)
Lemma stat_block_1_hint : forall (S0 S : JsSyntax.state) (C : JsSyntax.execution_ctx)
         (t : JsSyntax.stat) jrv jo jo1,
       J.red_stat S C (J.stat_basic t) jo1 ->
       J.red_stat S C (J.stat_block_2 jrv jo1) jo ->
       J.red_stat S0 C (J.stat_block_1
            (J.out_ter S (J.res_intro J.restype_normal jrv J.label_empty)) t) jo.
Proof. intros. fold (J.res_normal jrv). jauto_js. Qed.
Hint Resolve stat_block_1_hint : js_ljs.

Hint Extern 11 => match goal with |- context [If _ then _ else _] => case_if end : js_ljs.

Lemma label_set_mem_lemma : forall jl jls, Mem jl jls -> J.label_set_mem jl jls.
Proof.
    introv Hmem.
    unfolds.
    rew_refl.
    assumption.
Qed.

Lemma res_label_in_lemma : forall jl jrt jrv jls, 
    Mem jl jls -> J.res_label_in (J.res_intro jrt jrv jl) jls.
Proof.
    introv Hmem.
    unfolds.
    auto using label_set_mem_lemma.
Qed.

Lemma label_set_mem_inv_lemma : forall jl jls, J.label_set_mem jl jls -> Mem jl jls.
Proof.
    introv Hjls.
    unfolds in Hjls.
    rew_refl in Hjls.
    assumption.
Qed.

Lemma res_label_in_inv_lemma : forall jl jrv jls,
    J.res_label_in (J.res_intro J.restype_continue jrv jl) jls -> Mem jl jls.
Proof.
    introv Hmem.
    unfolds in Hmem.
    auto using label_set_mem_inv_lemma.
Qed.

Hint Resolve res_label_in_inv_lemma : js_ljs.
Hint Resolve res_label_in_lemma : js_ljs.

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
    jauto_js.
    left.
    solve_jauto_js.

    jauto_js.
    right.
    solve_jauto_js. 
    (* false *)
    repeat destr_concl; unfold_concl.
    jauto_js.
    left.
    solve_jauto_js.

    jauto_js.
    right.
    solve_jauto_js. 
    (* abort *)
    ljs_abort_from_js.
    ljs_propagate_abort.
    ijauto_js. (* TODO think if jauto_js can be used instead *)
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

    destr_concl;
    res_related_invert; repeat inv_fwd_ljs; 
    ijauto_js.
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

(* TODO move *)
Lemma string_append_right_empty : forall s, s ++ "" = s.
Proof.
    induction s. auto. simpl. rewrite IHs. reflexivity.
Qed.

Lemma string_append_right_injective : forall s1 s2 s, s ++ s1 = s ++ s2 -> s1 = s2.
Proof.
    induction s. auto. introv Heq. injects. auto.
Qed.

(* TODO move *)
Lemma js_label_to_ejs_injective_label : forall s jl1 jl2,
    E.js_label_to_ejs s jl1 = E.js_label_to_ejs s jl2 -> jl1 = jl2.
Proof.
    introv Heq.
    destruct jl1; destruct jl2; unfolds E.js_label_to_ejs; 
    apply string_append_right_injective in Heq; auto; tryfalse. 
    injects. reflexivity.
Qed.

Lemma red_exprh_le : forall k k' c st ee o, L.red_exprh k c st ee o -> (k <= k')%nat -> L.red_exprh k' c st ee o.
Proof.
    introv.
    destruct (classic (k = k')).
    subst. auto.
    intros. 
    asserts Hlt : (k < k')%nat. omega. 
    eauto using L.red_exprh_lt.
Qed.

Inductive label_set_hyp jls s : L.res -> L.res -> Prop := 
| label_set_hyp_break : forall jl v, 
    Mem jl jls -> 
    label_set_hyp jls s (L.res_break (E.js_label_to_ejs s jl) v) (L.res_value v)
| label_set_hyp_nomatch : forall jl v,
    ~Mem jl jls -> 
    label_set_hyp jls s (L.res_break (E.js_label_to_ejs s jl) v) (L.res_break (E.js_label_to_ejs s jl) v)
| label_set_hyp_fallthru : forall r,
    (forall jl v, r <> L.res_break (E.js_label_to_ejs s jl) v) ->
    label_set_hyp jls s r r.

Lemma label_set_invert_lemma : forall jls k c st0 s ee st r,
    L.red_exprh k c st0 (L.expr_basic (E.ejs_to_ljs (E.js_label_set_to_labels s jls ee))) (L.out_ter st r) ->
    exists r',
    L.red_exprh k c st0 (L.expr_basic (E.ejs_to_ljs ee)) (L.out_ter st r') /\
    label_set_hyp jls s r' r.
Proof.
    induction jls;
    introv Hlred.
    jauto_set. eassumption. 
    destruct (classic (forall jl v, r <> L.res_break (E.js_label_to_ejs s jl) v)).
    eapply label_set_hyp_fallthru; auto.
    rew_logic in H. destruct H as (jl&H).
    rew_logic in H. destruct H as (v&H).
    rew_logic in H. substs. 
    eapply label_set_hyp_nomatch. trivial. 

    inverts Hlred as Hlred' Hlred''.
    ljs_out_redh_ter.
    specializes IHjls Hlred'. clear Hlred'.
    destruct IHjls as (r'&IHred&IHjls).
    eexists.
    splits.
    inverts Hlred'';
    (eapply red_exprh_le; [eassumption | omega]).

    clear IHred.
    inverts IHjls as HypIH; inverts Hlred'' as Hfff.

    eapply label_set_hyp_break. apply Mem_next. assumption.
    
    eapply label_set_hyp_nomatch. intro Hmem.
    inverts Hmem. eapply Hfff. reflexivity. tryfalse.

    apply js_label_to_ejs_injective_label in Hfff. substs. 
    eapply label_set_hyp_break. apply Mem_here.

    apply label_set_hyp_fallthru.
    introv Hr. substs. eapply HypIH. reflexivity.

    false. eapply HypIH. reflexivity.
Qed.

(* TODO move *)
Fixpoint list_pairs {A:Type} (l : list A) :=
    match l with
    | h1::t1 =>
        match t1 with
        | h2::t2 => (h1,h2)::list_pairs t1
        | _ => []
        end
    | _ => []
    end.

Fixpoint init {A : Type} (l : list A) :=
    match l with
    | [] => []
    | [h] => []
    | h :: t => h :: init t
    end.

Lemma init_lemma : forall A l (a a' : A), 
    init (a :: a' :: l) = a :: init (a' :: l).
Proof. auto. Qed.

Inductive First {A : Type} : list A -> A -> Prop :=
    | First_here : forall a t, First (a :: t) a.

Inductive Last {A : Type} : list A -> A -> Prop :=
    | Last_here : forall a, Last [a] a
    | Last_next : forall a h1 h2 t, Last (h2 :: t) a -> Last (h1 :: h2 :: t) a.

Definition while_step k c e1 e2 e3 st2 v2 st1 v1 : Prop := 
    exists st' st'' v v',
    L.red_exprh k c st1 (L.expr_basic e1) (L.out_ter st' (L.res_value L.value_true)) /\
    L.red_exprh k c st' (L.expr_basic e2) (L.out_ter st'' (L.res_value v)) /\
    L.red_exprh k c st'' (L.expr_basic e3) (L.out_ter st2 (L.res_value v')) /\
    v2 = L.overwrite_value_if_empty v1 v.

Definition while_final k c e1 e2 e3 st r st' v : Prop := 
    (exists v', L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st r) /\
        r = L.res_exception v') \/
    (exists s v', L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st (L.res_break s v')) /\
        r = L.res_break s (L.overwrite_value_if_empty v v')) \/
    L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st (L.res_value L.value_false)) /\
        r = L.res_value v \/
    exists st'',
    L.red_exprh k c st' (L.expr_basic e1) (L.out_ter st'' (L.res_value L.value_true)) /\ (
    (exists v', L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st r) /\ 
        r = L.res_exception v') \/
    (exists s v', L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st (L.res_break s v')) /\ 
        r = L.res_break s (L.overwrite_value_if_empty v v')) \/
    exists st''' v', 
    L.red_exprh k c st'' (L.expr_basic e2) (L.out_ter st''' (L.res_value v')) /\ (
    (exists v'', L.red_exprh k c st''' (L.expr_basic e3) (L.out_ter st r) /\ 
        r = L.res_exception v'') \/
    (exists s v'', L.red_exprh k c st''' (L.expr_basic e3) (L.out_ter st (L.res_break s v'')) /\
        r = L.res_break s (L.overwrite_value_if_empty v (L.overwrite_value_if_empty v' v''))))). 

Inductive while_unroll k c e1 e2 e3 st r : L.store -> L.value -> Prop :=
| while_unroll_final : forall st0 v0, 
    while_final k c e1 e2 e3 st r st0 v0 -> 
    while_unroll k c e1 e2 e3 st r st0 v0
| while_unroll_step : forall st0 v0 st' v',
    while_step k c e1 e2 e3 st' v' st0 v0 ->
    while_unroll k c e1 e2 e3 st r st' v' ->
    while_unroll k c e1 e2 e3 st r st0 v0.

Hint Extern 4 (L.red_exprh _ ?c ?st ?e ?r) =>
    match goal with
    | H : L.red_exprh _ c st e _ |- _ => 
        eapply red_exprh_le; [eapply H | omega]
    end.

Lemma ljs_out_ter_cases : forall st r, (exists v, r = L.res_value v) \/ L.abort (L.out_ter st r).
Proof. intros. destruct r; iauto. Qed.
Ltac ljs_cases_res ee := 
    match goal with
    | H : L.red_exprh _ _ _ ee (L.out_ter ?st ?r) |- _ =>
        is_var r;
        let H := fresh "H" in let v := fresh "v" in
        destruct (ljs_out_ter_cases st r) as [(v&H)|H]; [subst r | idtac] 
    end.

Ltac ljs_abort_inv := 
    match goal with
    | H : L.abort (L.out_ter _ _ ) |- _ => 
        let H' := fresh "H" in
        inverts H as H'; inverts H'
    end.

Lemma while_step_overwrite_lemma : forall k c e1 e2 e3 st v st0 v0 v',
    while_step k c e1 e2 e3 st v st0 v0 ->
    while_step k c e1 e2 e3 st (L.overwrite_value_if_empty v' v) st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hstep.
    unfolds while_step.
    destruct_hyp Hstep.
    repeat eexists; eauto.
    rewrite overwrite_value_if_empty_assoc. reflexivity.
Qed.

Lemma while_final_overwrite_value_lemma : forall k c e1 e2 e3 st st0 v v0 v',
    while_final k c e1 e2 e3 st (L.res_value v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_value (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse; iauto.
Qed.

Lemma while_unroll_overwrite_value_lemma : forall k c e1 e2 e3 st st0 v v0 v',
    while_unroll k c e1 e2 e3 st (L.res_value v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_value (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hwhile. 
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_overwrite_value_lemma.
    (* step *)
    eapply while_unroll_step.
    eauto using while_step_overwrite_lemma.
    assumption.
Qed.

Lemma while_final_overwrite_break_lemma : forall k c e1 e2 e3 st st0 v v0 v' s,
    while_final k c e1 e2 e3 st (L.res_break s v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_break s (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof. 
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse.
    right. left. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
    right. right. right. eexists. split. eassumption. 
        right. left. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
    right. right. right. eexists. split. eassumption. right. right. do 2 eexists. split. eassumption.
        right. do 2 eexists. split. eassumption. rewrite overwrite_value_if_empty_assoc. reflexivity.
Qed.

Lemma while_unroll_overwrite_break_lemma : forall k c e1 e2 e3 st st0 v v0 v' s,
    while_unroll k c e1 e2 e3 st (L.res_break s v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_break s (L.overwrite_value_if_empty v' v)) 
        st0 (L.overwrite_value_if_empty v' v0).
Proof.
    introv Hwhile. 
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_overwrite_break_lemma.
    (* step *)
    eapply while_unroll_step.
    eauto using while_step_overwrite_lemma.
    assumption.
Qed.

Lemma while_final_exception_lemma : forall k c e1 e2 e3 st st0 v v0 v1,
    while_final k c e1 e2 e3 st (L.res_exception v) st0 v0 ->
    while_final k c e1 e2 e3 st (L.res_exception v) st0 v1.
Proof.
    introv Hfinal.
    unfolds while_final.
    destruct_hyp Hfinal; repeat injects; tryfalse.
    iauto.
    right. right. right. eexists. split. eassumption. left. iauto.
    right. right. right. eexists. split. eassumption. 
        right. right. do 2 eexists. split. eassumption. left. iauto. 
Qed.

Lemma while_step_exception_lemma : forall k c e1 e2 e3 st v st0 v0 v0',
    while_step k c e1 e2 e3 st v st0 v0 -> exists v',
    while_step k c e1 e2 e3 st v' st0 v0'.
Proof.
    introv Hstep.
    unfolds while_step.
    destruct_hyp Hstep.
    repeat eexists; eauto. 
Qed.

Lemma while_unroll_exception_lemma : forall k c e1 e2 e3 st st0 v v0 v1,
    while_unroll k c e1 e2 e3 st (L.res_exception v) st0 v0 ->
    while_unroll k c e1 e2 e3 st (L.res_exception v) st0 v1.
Proof.
    introv Hwhile.
    gen v1.
    inductions Hwhile; intros.
    (* final *)
    eapply while_unroll_final.
    eauto using while_final_exception_lemma.
    (* step *)
    forwards Hl : while_step_exception_lemma. eassumption.
    destruct Hl as (v_arb&Hl).
    eapply while_unroll_step; [apply Hl | eapply IHHwhile].
Qed.

Lemma while_final_leq_lemma : forall k k' c e1 e2 e3 st r st0 v0,
    while_final k c e1 e2 e3 st r st0 v0 ->
    (k' >= k)%nat -> 
    while_final k' c e1 e2 e3 st r st0 v0.
Proof.
    introv Hfinal Hleq.
    unfolds while_final.
    destruct_hyp Hfinal; repeat (eexists || iauto || right).
Qed.

Lemma while_step_leq_lemma : forall k k' c e1 e2 e3 st v st0 v0,
    while_step k c e1 e2 e3 st v st0 v0 ->
    (k' >= k)%nat -> 
    while_step k' c e1 e2 e3 st v st0 v0.
Proof.
    introv Hstep Hleq.
    unfolds while_step.
    destruct_hyp Hstep; repeat eexists; iauto.
Qed.

Lemma while_unroll_leq_lemma : forall k k' c e1 e2 e3 st r st0 v0,
    while_unroll k c e1 e2 e3 st r st0 v0 ->
    (k' >= k)%nat -> 
    while_unroll k' c e1 e2 e3 st r st0 v0.
Proof.
    introv Hwhile Hleq.
    inductions Hwhile.
    (* final *)
    eapply while_unroll_final.
    eapply while_final_leq_lemma. eassumption. omega.
    (* step *)
    eapply while_unroll_step.
    eapply while_step_leq_lemma. eassumption. omega.
    eauto.
Qed.

(* TODO: move to utils *)
Definition freeze (P : Prop) : Prop := P.
Lemma freeze_intro : forall (P : Prop), P -> freeze P. Proof. auto. Qed. 
Lemma freeze_elim : forall (P : Prop), freeze P -> P. Proof. auto. Qed.

Opaque freeze. 

Ltac freeze E := apply freeze_intro in E.
Ltac unfreeze E := apply freeze_elim in E.

Definition ejs_while_body_closure c ee1 ee2 ee3 := L.value_closure 
        (L.closure_intro (to_list c) (Some "%while_loop") [] 
            (E.while_body (E.ejs_to_ljs ee1) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3))).

Lemma ejs_while_body_lemma : forall k c c' st0 ee1 ee2 ee3 st r,
    c = (c' \("%while_loop" := ejs_while_body_closure c' ee1 ee2 ee3)) ->
    L.red_exprh k c st0 (L.expr_basic (E.while_body (E.ejs_to_ljs ee1) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3)))
        (L.out_ter st r) ->
    while_unroll k c (E.to_bool (E.ejs_to_ljs ee1)) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3) st r st0 L.value_empty.
Proof.
    introv Hctx Heq.
    asserts Hbinds : (binds c "%while_loop" (ejs_while_body_closure c' ee1 ee2 ee3)).
    substs. prove_bag.
    unfolds ejs_while_body_closure.
    freeze Hctx. 
    inv_ljs_stop (L.expr_basic (E.to_bool (E.ejs_to_ljs ee1))).
    inv_ljs_stop (L.expr_basic (E.ejs_to_ljs ee1)).
    inv_ljs_stop (L.expr_basic (E.ejs_to_ljs ee2)).
    gen st0 st r.
    induction_wf IH : lt_wf k.
    introv Hlred.
    inv_fwd_ljs.
    ljs_out_redh_ter.
    inv_internal_ljs. 
    (* condition true *)
    inv_fwd_ljs.
    ljs_out_redh_ter.
    inv_internal_ljs.
    (* body returns a value *)
    inv_fwd_ljs.
    repeat ljs_out_redh_ter.
    ljs_cases_res (L.expr_basic (E.ejs_to_ljs ee3)).
    (* after returns a value *)
    repeat inv_fwd_ljs.
    binds_determine. substs.
    inverts H9. (* TODO! *)
    ljs_apply.
    rewrite from_list_empty in H13.
    repeat rew_bag_simpl in H13.
    unfreeze Hctx.
    rewrite <- Hctx in H13.
    freeze Hctx.
    specializes IH H13. omega.
    eapply while_unroll_step.
    repeat eexists. eauto. eauto. eauto.
    inv_internal_ljs. 
    rewrite overwrite_value_if_empty_left_empty.
    eapply while_unroll_overwrite_value_lemma in IH.
    rewrite overwrite_value_if_empty_right_empty in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.
    eapply while_unroll_exception_lemma in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.
    rewrite overwrite_value_if_empty_left_empty.
    eapply while_unroll_overwrite_break_lemma in IH.
    rewrite overwrite_value_if_empty_right_empty in IH.
    eapply while_unroll_leq_lemma. eassumption. omega.    
    (* after aborted *)
    apply while_unroll_final. right. right. right. eexists. split. eauto. right. right. do 2 eexists. split. eauto.
    ljs_abort_inv; repeat inv_fwd_ljs.
    iauto.
    right. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto.
    (* body aborted *)
    apply while_unroll_final. right. right. right. eexists. split. eauto.
    ljs_abort_inv.
    left. eexists. eauto.
    right. left. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto. 
    (* condition false *)
    inv_fwd_ljs.
    apply while_unroll_final. unfolds. iauto. 
    (* condition aborted *)
    apply while_unroll_final.
    ljs_abort_inv.
    left. iauto.
    right. left. do 2 eexists. rewrite overwrite_value_if_empty_left_empty. eauto.
Qed.

Lemma exprjs_while_lemma : forall k c c' st0 ee1 ee2 ee3 st r,
    c = c'\("%while_loop" := ejs_while_body_closure c' ee1 ee2 ee3) ->
    L.red_exprh k c' st0 (L.expr_basic (E.ejs_to_ljs (E.expr_while ee1 ee2 ee3))) (L.out_ter st r) ->
    exists k', 
    while_unroll k' c (E.to_bool (E.ejs_to_ljs ee1)) (E.ejs_to_ljs ee2) (E.ejs_to_ljs ee3) st r st0 L.value_empty /\ 
    (k' < k) % nat.
Proof.
    introv Hctx Hlred.
    substs.
    repeat inv_fwd_ljs.
    binds_inv.
    inverts H6. (* TODO *)

    unfolds L.add_closure.
    ljs_apply.
    rewrite from_list_empty in H8. (* TODO *)
    rew_bag_simpl in H8.
    eexists. split.
    eapply ejs_while_body_lemma. reflexivity. eassumption.
    omega.
Qed.

Definition while_body_closure c je jt := ejs_while_body_closure c (E.js_expr_to_ejs je) (E.js_stat_to_ejs jt).

Definition js_labelset_stat_to_ljs jls jt :=
    E.ejs_to_ljs (E.js_label_set_to_labels "%continue" jls (E.js_stat_to_ejs jt)).

Definition js_expr_to_bool_ljs je := E.to_bool (js_expr_to_ljs je).

Lemma red_stat_while_lemma : forall k k' jls je jt v jrv,
    ih_stat k ->
    ih_expr k ->
    (k' < k)%nat ->
    forall BR jst jc c st st' r r', 
    while_unroll k' c (js_expr_to_bool_ljs je) (js_labelset_stat_to_ljs jls jt) L.expr_undefined st' r' st v ->
    label_set_hyp jls "%break" r' r ->
    resvalue_related BR jrv v ->
    state_invariant BR jst jc c st ->
    exists BR' jst' jr,
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_stat jst jc (J.stat_while_1 jls je jt jrv) (J.out_ter jst' jr) /\ 
    res_related BR' jst' st' jr r.
Proof.
    introv IHt IHe Hlt Hwhile.
    inductions Hwhile gen jrv jst BR;
    introv Hlabel_brk Haccum Hinv.
    (* final *)
    destruct H as [Hwf|[Hwf|[Hwf|(?st&Hcond&Hwf1)]]]; try destruct_hyp Hwf.
    (* condition throws *)
    forwards_th red_spec_to_boolean_ok.
    inverts Hlabel_brk. 
    destr_concl. tryfalse.
    jauto_js.
    (* condition breaks, IMPOSSIBLE *)
    skip. (* TODO *)
    (* condition false *)
    forwards_th red_spec_to_boolean_ok.
    inverts Hlabel_brk.
    destr_concl.   
    injects.
    jauto_js. 
    eauto with js_ljs. (* jauto_js. EXISTENTIAL VARIABLES *) 
    (* condition true *)
    forwards_th red_spec_to_boolean_ok.
    destr_concl; try js_abort_rel_contr; [idtac].
    injects.
    destruct Hwf1 as [Hwf|[Hwf|(?st&?v&Hstat&Hwf1)]]; try destruct_hyp Hwf.
    (* statement throws *) 
    apply label_set_invert_lemma in Hwf0.
    destruct Hwf0 as (r''&Hlred&Hlabel_cont). (* TODO add tactic *)
    apply_ih_stat.
    destr_concl. 
    inverts Hlabel_brk.
    inverts Hlabel_cont.
    res_related_invert. 
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_5_not_break. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_6_abort. eauto with js_ljs. (* TODO: try trivial first in jauto_js *) 
    (* statement breaks *)
    apply label_set_invert_lemma in Hwf0.
    destruct Hwf0 as (r''&Hlred&Hlabel_cont). (* TODO add tactic *)
    apply_ih_stat.
    destr_concl.
    inverts Hlabel_cont. 
    (* continue with wrong label *)
    inverts Hlabel_brk.
    res_related_invert.
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. jauto_js.
    eapply J.red_stat_while_5_not_break. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    autorewrite with js_ljs.
    skip. (* eapply J.red_stat_while_6_abort. *) (* TODO SPECIFICATION PROBLEM! ASK ALAN *)
    (* not continue *)
    inverts Hlabel_brk.
    (* actual break *)
    res_related_invert.
    jauto_js. 
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    autorewrite with js_ljs.
    eapply J.red_stat_while_5_break. jauto_js.
    (* break with wrong label *)
    res_related_invert.
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_5_not_break. jauto_js. 
    autorewrite with js_ljs.
    skip. (* eapply J.red_stat_while_6_abort. *) (* TODO SPECIFICATION PROBLEM! ASK ALAN *)
    (* only return remains *)
    (* TODO: add to res_related that returning empty is not possible! *)
    skip. (* TODO *) 
    (* statement returns a value *)
    apply label_set_invert_lemma in Hstat.
    destruct Hstat as (r''&Hlred&Hlabel_cont). (* TODO add tactic *) 
    apply_ih_stat. 
    destr_concl. 
    inverts Hlabel_cont. 
    (* statement continued *)
    destruct_hyp Hwf1; inv_ljs.
    (* statement not continued *)
    destruct_hyp Hwf1; inv_ljs.
    (* step *)
    destruct H as (?st&?st&?v&?v&Hcond&Hstat&Hafter&EQv').
    substs.
    inverts Hafter. 
    apply label_set_invert_lemma in Hstat.
    destruct Hstat as (?r&Hstat&Hlabel_cont).
    forwards_th red_spec_to_boolean_ok.
    destr_concl.
    injects.
    apply_ih_stat.
    destr_concl.
    inverts Hlabel_cont.
    (* statement continued *)
    res_related_invert.
    specializes IHHwhile Hlabel_brk ___.
    jauto_js.
    jauto_js 8.
    (* statement not continued *)
    res_related_invert.
    specializes IHHwhile Hlabel_brk ___.
    jauto_js.
    jauto_js.
    eapply J.red_stat_while_1. eassumption.
    eapply J.red_stat_while_2_true. eassumption.
    eapply J.red_stat_while_3. reflexivity.
    eapply J.red_stat_while_4_not_continue. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_5_not_break. simpls. intro. jauto_set. tryfalse. (* TODO! to jauto_js *)
    eapply J.red_stat_while_6_normal. reflexivity. autorewrite with js_ljs. jauto_js. (* TODO! *)

    res_related_invert. eauto with js_ljs. (* TODO *)
Qed.

Lemma red_stat_while_ok : forall k jls je jt,
    ih_stat k ->
    ih_expr k ->
    th_stat k (J.stat_while jls je jt).
Proof.
    introv IHt IHe Hinv Hlred.
    unfolds js_stat_to_ljs. simpls. 
    apply label_set_invert_lemma in Hlred.
    destruct Hlred as (r'&Hlred&Hlabel).
    apply (exprjs_while_lemma eq_refl) in Hlred.
    sets_eq c' : (c\("%while_loop" := ejs_while_body_closure c (E.js_expr_to_ejs je)
        (E.js_label_set_to_labels "%continue" jls (E.js_stat_to_ejs jt)) E.expr_undefined)). 
    asserts Hinv' : (state_invariant BR jst jc c' st). skip. (* TODO state invariant lemma *)
    freeze EQc'.
    destruct Hlred as (k'&Hwhile&Hk).
    lets Hlemma : red_stat_while_lemma IHt IHe Hk Hwhile Hlabel.
    specializes Hlemma resvalue_related_empty Hinv'. (* TODO TLC lets too small ;) *)
    destruct_hyp Hlemma.
    jauto_js.
    skip. (* TODO state invariant lemma *)
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
    res_related_invert;
    repeat inv_fwd_ljs;
    unfolds E.js_label_to_ejs;
    repeat inv_fwd_ljs;
    try solve [jauto_js].
    destruct jl;
    inv_internal_ljs; try injects;
    jauto_js.
    destruct (classic (s = s0)).
    substs. specializes H4 st' v. 
    jauto_js.
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
    solve_jauto_js.
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

