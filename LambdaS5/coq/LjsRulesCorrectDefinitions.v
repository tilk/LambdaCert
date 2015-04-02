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

Global Coercion JsNumber.of_int : Z >-> JsNumber.number.

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

Export LjsPrettyRulesAux.Tactics.
Export LjsPrettyRulesIndexedAux.Tactics.

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
| res_related_return : forall jv v,
    value_related BR jv v ->
    res_related BR jst st (J.res_intro J.restype_return (J.resvalue_value jv) J.label_empty) 
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
        J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\
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
