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
Require Export JsBagAdapter.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Global Coercion JsNumber.of_int : Z >-> JsNumber.number.

(** ** Shorthand module names 
    These are used to refer to the different languages: S5, ExprJS and JS. *)

Module L. 
Include LjsSyntax.
Include LjsPrettyRules.
Include LjsPrettyRulesIndexed.
Include LjsPrettyRulesIndexedAux.
Include LjsPrettyInterm.
Include LjsStore.
Include LjsAuxiliary.
Include LjsOperators.
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
Include JsBagAdapter.JsCertExt.
End J.

Export LjsPrettyRulesAux.Tactics.
Export LjsPrettyRulesIndexedAux.Tactics.

(** ** Implicit Type declarations 
    They are common for all LjsRulesCorrect* libraries. *)

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
Implicit Type jeptr : J.env_loc.
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.
Implicit Type jlenv : J.lexical_env.
Implicit Type jpre : J.prealloc.

(** ** Composite desugaring functions 
    Desugaring for literals, expressions and statements. *)

Definition js_literal_to_ljs jli := E.ejs_to_ljs (E.js_literal_to_ejs jli).
Definition js_expr_to_ljs je := E.ejs_to_ljs (E.js_expr_to_ejs je).
Definition js_stat_to_ljs jt := E.ejs_to_ljs (E.js_stat_to_ejs jt).

(** ** Relating JS and S5 *)

(** *** Heap bisimulations 
    They relate JS objects to LJS objects. 
    Properties they should satisfy will be defined later. *)

Definition object_bisim := J.object_loc + J.env_loc -> L.object_ptr -> Prop.

Implicit Type BR : object_bisim.

(** *** Relating values
    Note that this definition implies that LJS lambdas and empty are never seen directly by JS code. 
    Also, relating objects is delegated to the bisimulation relation. *)

Inductive value_related BR : J.value -> L.value -> Prop :=
| value_related_null : value_related BR (J.value_prim J.prim_null) L.value_null
| value_related_undefined : value_related BR (J.value_prim J.prim_undef) L.value_undefined
| value_related_number : forall n, value_related BR (J.value_prim (J.prim_number n)) (L.value_number n)
| value_related_string : forall s, value_related BR (J.value_prim (J.prim_string s)) (L.value_string s)
| value_related_bool : forall b, value_related BR (J.value_prim (J.prim_bool b)) (L.value_bool b)
| value_related_object : forall jptr ptr, 
    (inl jptr, ptr) \in BR -> value_related BR (J.value_object jptr) (L.value_object ptr) 
.

(** *** Relating object properties
    Individual properties are related in a natural way. *)

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

(** Property sets are related so that for every property name, 
    either the attribute is undefined in both JS and LJS objects,
    or it's defined in both and related. *)

Definition object_properties_related BR jprops props := forall s, 
    ~index jprops s /\ ~index props s \/
    exists jptr ptr, 
        binds jprops s jptr /\ binds props s ptr /\
        attributes_related BR jptr ptr.

(** *** Relating objects
    To be related, objects must have related property sets and internal properties. *)

Definition object_prim_related BR jobj obj := 
    J.object_class_ jobj = L.object_class obj /\
    J.object_extensible_ jobj = L.object_extensible obj.

Definition object_related BR jobj obj :=
    object_prim_related BR jobj obj /\
    object_properties_related BR (J.object_properties_ jobj) (L.object_properties obj).

(** *** Relating environment records *)

(* Relates declarative environment records *)

Definition mutability_writable jmut := 
    match jmut with
    | J.mutability_immutable => false
    | _ => true
    end.

Definition mutability_configurable jmut :=
    match jmut with
    | J.mutability_nondeletable => false
    | _ => true
    end.

Definition decl_env_record_related BR jder props := forall s,
    ~index jder s /\ ~index props s \/
    exists jmut jv v, 
        binds jder s (jmut, jv) /\ 
        binds props s (L.attributes_data_of (L.attributes_data_intro v 
            (mutability_writable jmut) true (mutability_configurable jmut))) /\
        value_related BR jv v.

(* Relates environment records *)
Inductive env_record_related BR : J.env_record -> L.object -> Prop :=
| env_record_related_decl : forall jder obj,
    L.object_proto obj = L.value_null ->
    L.object_class obj = "DeclEnvRec" ->
    L.object_extensible obj = true ->
    decl_env_record_related BR jder (L.object_properties obj) ->
    env_record_related BR (J.env_record_decl jder) obj
| env_record_related_object : forall b ptr jptr obj,
    L.object_proto obj = L.value_null ->
    L.object_class obj = "ObjEnvRec" ->
    binds (L.object_properties obj) "provideThis" 
        (L.attributes_data_of (L.attributes_data_intro (L.value_bool b) false false false)) ->
    binds (L.object_properties obj) "bindings" 
        (L.attributes_data_of (L.attributes_data_intro (L.value_object ptr) false false false)) ->
    (inl jptr, ptr) \in BR ->
    env_record_related BR (J.env_record_object jptr b) obj
.

(** *** Properties of heap bisimulations
    Heap bisimulations must satisfy several properties in order to be useful
    in the proof:
    - They must be injective - every JS object has an unique corresponding S5 object.
    - The mapped adresses must actually correspond to some object in JS and S5 heaps. *)

Definition heaps_bisim_ltotal_inl BR jst :=
    forall jptr, index (J.state_object_heap jst) jptr -> exists ptr, BR (inl jptr) ptr.

Definition heaps_bisim_ltotal_inr BR jst :=
    forall jeptr, index (J.state_env_record_heap jst) jeptr -> exists ptr, BR (inr jeptr) ptr.

Definition heaps_bisim_lnoghost_inl BR jst :=
    forall jptr ptr, BR (inl jptr) ptr -> index (J.state_object_heap jst) jptr.

Definition heaps_bisim_lnoghost_inr BR jst :=
    forall jeptr ptr, BR (inr jeptr) ptr -> index (J.state_env_record_heap jst) jeptr.

Definition heaps_bisim_rnoghost BR st :=
    forall xptr ptr, BR xptr ptr -> index st ptr.

Definition heaps_bisim_inl BR jst st := forall jptr ptr jobj obj, 
     (inl jptr, ptr) \in BR -> 
     binds jst jptr jobj ->
     binds st ptr obj ->
     object_related BR jobj obj.

Definition heaps_bisim_inr BR jst st := forall jeptr ptr jer obj, 
     (inr jeptr, ptr) \in BR -> 
     binds jst jeptr jer ->
     binds st ptr obj ->
     env_record_related BR jer obj.

Record heaps_bisim_consistent BR jst st : Prop := {
    heaps_bisim_consistent_bisim_inl : heaps_bisim_inl BR jst st;
    heaps_bisim_consistent_bisim_inr : heaps_bisim_inr BR jst st;
    heaps_bisim_consistent_lfun : functional BR;
    heaps_bisim_consistent_rfun : functional (flip BR);
    heaps_bisim_consistent_ltotal_inl : heaps_bisim_ltotal_inl BR jst;
    heaps_bisim_consistent_ltotal_inr : heaps_bisim_ltotal_inr BR jst;
    heaps_bisim_consistent_lnoghost_inl : heaps_bisim_lnoghost_inl BR jst;
    heaps_bisim_consistent_lnoghost_inr : heaps_bisim_lnoghost_inr BR jst;
    heaps_bisim_consistent_rnoghost : heaps_bisim_rnoghost BR st
}.

(** *** Relating result values
    Result values are the JavaScript's "maybe values",
    they are the results of evaluating statements. *)

Inductive resvalue_related BR : J.resvalue -> L.value -> Prop :=
| resvalue_related_empty :  
    resvalue_related BR J.resvalue_empty L.value_empty
| resvalue_related_value : forall jv v,
    value_related BR jv v ->
    resvalue_related BR (J.resvalue_value jv) v
.

(** *** Relating results
    Results are the ways a given statement can terminate. They correspond to
    completion types in the specification. *)

(** JavaScript exceptions are wrapped in a S5 object, to be distinguished
    from internal S5 exceptions. *)

Definition js_exn_object obj v := 
    binds (L.object_properties obj) "%js-exn" 
        (L.attributes_data_of (L.attributes_data_intro v false false false)).

(** The relationship is as follows:
    - Normal results in JS map to normal results in S5.
    - Throws in JS translate to throws with a wrapper in S5.
    - Returns in JS translate to S5 breaks to a special label "%%ret".
    - Breaks in JS translate to S5 breaks, the label is tagged with "%%break".
    - Continues in JS translate to S5 breaks, the label is tagged with "%%continue". *)

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

(** ** Invariants 
    To relate JS and S5 programs, certain invariants must hold at all times. *)

(** *** S5 environment presence invariant 
    States that the initial LJS context ("the environment") can always be accessed
    (and thus is never shadowed). *)

Definition includes_init_ctx c :=
    forall i v v', binds c i v -> binds LjsInitEnv.init_ctx i v' -> v = v'. 

(** *** Relating lexical environments *)

(* Relates the lexical environment *)
Inductive lexical_env_related BR st : J.lexical_env -> L.value -> Prop :=
| lexical_env_related_nil : 
    lexical_env_related BR st nil L.value_null
| lexical_env_related_cons : forall jeptr jlenv ptr obj,
    (inr jeptr, ptr) \in BR ->
    binds st ptr obj ->
    lexical_env_related BR st jlenv (L.object_proto obj) ->
    lexical_env_related BR st (jeptr::jlenv) (L.value_object ptr)
.

(* Relates the lexical contexts *)
Record execution_ctx_related BR jc c st := {
    execution_ctx_related_this_binding : forall v,
        binds c "%this" v ->
        value_related BR (J.execution_ctx_this_binding jc) v;
    execution_ctx_related_strictness_flag : forall v, 
        binds c "%strict" v ->
        v = L.value_bool (J.execution_ctx_strict jc);
    execution_ctx_related_lexical_env : forall v,
        binds c "%context" v ->
        lexical_env_related BR st (J.execution_ctx_lexical_env jc) v
}.

Definition global_env_record_exists BR c := forall v ptr,
        binds c "%globalContext" v ->
        v = L.value_object ptr /\
        (inr J.env_loc_global_env_record, ptr) \in BR.

(* States that the variable environment and lexical environment exist *)
Record env_records_exist BR jc := { 
    env_record_exist_variable_env : 
        Forall (fun jeptr => exists ptr, (inr jeptr, ptr) \in BR) (J.execution_ctx_variable_env jc);
    env_record_exist_lexical_env : 
        Forall (fun jeptr => exists ptr, (inr jeptr, ptr) \in BR) (J.execution_ctx_lexical_env jc)
}.

(** *** Preallocated objects invariant
    States that EcmaScript preallocated objects can be found in the LJS context. *)

Definition prealloc_in_ctx_list := [
    (J.prealloc_native_error_proto J.native_error_eval, "%EvalErrorGlobalFuncObj");
    (J.prealloc_native_error_proto J.native_error_range, "%RangeErrorGlobalFuncObj");
    (J.prealloc_native_error_proto J.native_error_ref, "%ReferenceErrorGlobalFuncObj");
    (J.prealloc_native_error_proto J.native_error_syntax, "%SyntaxErrorGlobalFuncObj");
    (J.prealloc_native_error_proto J.native_error_type, "%TypeErrorGlobalFuncObj");
    (J.prealloc_native_error J.native_error_eval, "%EvalErrorProto");
    (J.prealloc_native_error J.native_error_range, "%RangeErrorProto");
    (J.prealloc_native_error J.native_error_ref, "%ReferenceErrorProto");
    (J.prealloc_native_error J.native_error_syntax, "%SyntaxErrorProto");
    (J.prealloc_native_error J.native_error_type, "%TypeErrorProto")
].

Definition prealloc_in_ctx BR c := forall jpre s v, 
    Mem (jpre, s) prealloc_in_ctx_list ->
    binds c s v ->
    exists ptr,
    v = L.value_object ptr /\
    (inl (J.object_loc_prealloc jpre), ptr) \in BR.

(** *** Initial bisimulation. *)

Parameter initBR : object_bisim. (* TODO *)

(** *** Invariant predicate
    The complete set of invariants, combined in one predicate to make proofs simpler. *)

Record state_invariant BR jst jc c st : Prop := {
    state_invariant_bisim_includes_init : initBR \c BR;
    state_invariant_heaps_bisim_consistent : heaps_bisim_consistent BR jst st;
    state_invariant_execution_ctx_related : execution_ctx_related BR jc c st;
    state_invariant_includes_init_ctx : includes_init_ctx c;
    state_invariant_env_records_exist : env_records_exist BR jc;
    state_invariant_prealloc_related : prealloc_in_ctx BR c;
    state_invariant_global_env_record_exists : global_env_record_exists BR c
}.

(** ** Theorem statement  
    Factored out, because it is used in many lemmas. *)

(** *** Theorem conclusions
    They state what must hold if the preconditions are satisfied. *)

Definition concl_ext_expr_value BR jst jc c st st' r jee P :=
    exists BR' jst' jr,
    ((exists jv, jr = J.res_val jv /\ P jv) \/
     J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw) /\
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_expr jst jc jee (J.out_ter jst' jr) /\ 
    res_related BR jst' st' jr r.

(* unused
Definition concl_expr_value BR jst jc c st st' r je :=  
    concl_ext_expr_value BR jst jc c st st' r (J.expr_basic je).
*)
Definition concl_stat BR jst jc c st st' r jt :=
    exists BR' jst' jr,
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    J.red_stat jst jc (J.stat_basic jt) (J.out_ter jst' jr) /\ 
    res_related BR' jst' st' jr r.

Definition concl_spec {A : Type} BR jst jc c st st' r jes 
    (P : object_bisim -> J.state -> A -> Prop) (Q : object_bisim -> J.state -> J.res -> Prop) :=
    exists BR' jst',
    state_invariant BR' jst' jc c st' /\ 
    BR \c BR' /\
    ((exists x, J.red_spec jst jc jes (J.specret_val jst' x) /\ P BR' jst' x) \/
     (exists jr, 
        J.red_spec jst jc jes (@J.specret_out A (J.out_ter jst' jr)) /\ 
        J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\
        res_related BR' jst' st' jr r /\ Q BR' jst' jr)).

Definition concl_expr_getvalue BR jst jc c st st' r je := 
    concl_spec BR jst jc c st st' r (J.spec_expr_get_value je) 
       (fun BR' _ jv => exists v, r = L.res_value v /\ value_related BR' jv v) (fun _ _ _ => True).

(** *** Theorem statements *)

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
    concl_spec BR jst jc c st st' r jes (fun BR' jst' a => P BR' jst' jc c st' r a) (fun _ _ _ => True).

Definition th_ext_expr_unary k v jeef P :=
    forall BR jst jc c st st' r v1 jv1, 
    state_invariant BR jst jc c st ->
    value_related BR jv1 v1 -> 
    L.red_exprh k c st (L.expr_app_2 v [v1]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (jeef jv1) P.

Definition th_ext_expr_binary k v jeef P :=
    forall BR jst jc c st st' r v1 jv1 v2 jv2, 
    state_invariant BR jst jc c st ->
    value_related BR jv1 v1 -> 
    value_related BR jv2 v2 -> 
    L.red_exprh k c st (L.expr_app_2 v [v1; v2]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (jeef jv1 jv2) P.

(** *** Inductive hypotheses 
    The form of the induction hypotheses, as used in the proof. 
    Height induction is used to make proofs simpler. *)

Definition ih_expr k := forall je k', (k' < k)%nat -> th_expr k' je.

Definition ih_stat k := forall jt k', (k' < k)%nat -> th_stat k' jt.
