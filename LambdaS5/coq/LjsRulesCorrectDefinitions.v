Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require LjsSyntax LjsPrettyRules LjsPrettyRulesAux LjsPrettyRulesIndexed LjsPrettyRulesIndexedAux
    LjsPrettyInterm LjsStore LjsAuxiliary LjsPrettyRulesSecurity.
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
Include LjsSyntaxAux.
Include LjsPrettyRules.
Include LjsPrettyRulesIndexed.
Include LjsPrettyRulesIndexedAux.
Include LjsPrettyRulesSecurity.
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
Implicit Type attrs : L.attributes.

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
Implicit Type jattrs : J.attributes.
Implicit Type jlenv : J.lexical_env.
Implicit Type jpre : J.prealloc.

(** ** Composite desugaring functions 
    Desugaring for literals, expressions and statements. *)

Definition js_literal_to_ljs jli := E.ejs_to_ljs (E.js_literal_to_ejs jli).
Definition js_expr_to_ljs je := E.ejs_to_ljs (E.js_expr_to_ejs je).
Definition js_stat_to_ljs jt := E.ejs_to_ljs (E.js_stat_to_ejs jt).

(** ** Relating JS and S5 *)

(** *** State fact set
    Used to carry information about the current state. Includes the heap bisimulation. *)

Inductive fact :=
| fact_js_obj : J.object_loc -> L.object_ptr -> fact
| fact_js_env : J.env_loc -> L.object_ptr -> fact
| fact_getter_proxy : L.object_ptr -> L.value -> fact
| fact_setter_proxy : L.object_ptr -> L.value -> fact
| fact_ctx_parent : L.object_ptr -> L.value -> fact
.

Definition fact_set := finset fact. (* TODO: lib-bag-ize set *)

Implicit Type BR : fact_set.

(** *** Relating types *)

Inductive type_related : J.type -> L.type -> Prop :=
| type_related_undef : type_related J.type_undef L.type_undefined
| type_related_null : type_related J.type_null L.type_null
| type_related_bool : type_related J.type_bool L.type_bool
| type_related_number : type_related J.type_number L.type_number
| type_related_string : type_related J.type_string L.type_string
| type_related_object : type_related J.type_object L.type_object.

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
    fact_js_obj jptr ptr \in BR -> value_related BR (J.value_object jptr) (L.value_object ptr) 
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
| attributes_accessor_related_intro : forall jv1 jv2 v1 v2 b1 b2 ptr1 ptr2, 
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    fact_getter_proxy ptr1 v1 \in BR ->
    fact_setter_proxy ptr2 v2 \in BR ->
    attributes_accessor_related BR
        (J.attributes_accessor_intro jv1 jv2 b1 b2) 
        (L.attributes_accessor_intro (L.value_object ptr1) (L.value_object ptr2) b1 b2)
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
    exists jattrs attrs, 
        binds jprops s jattrs /\ binds props s attrs /\
        attributes_related BR jattrs attrs.

(** *** Relating objects
    To be related, objects must have related property sets and internal properties. *)

Record object_prim_related BR jobj obj : Prop := {
    object_prim_related_class : J.object_class_ jobj = L.object_class obj;
    object_prim_related_extensible : J.object_extensible_ jobj = L.object_extensible obj
}.

Record object_related BR jobj obj : Prop := {
    object_related_prim : object_prim_related BR jobj obj;
    object_related_properties : object_properties_related BR (J.object_properties_ jobj) (L.object_properties obj)
}.

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
    fact_js_obj jptr ptr \in BR ->
    env_record_related BR (J.env_record_object jptr b) obj
.

(** *** Definitions of helper objects *)

Record getter_proxy obj v : Prop := {
    getter_proxy_proto : L.object_proto obj = L.value_null;
    getter_proxy_class : L.object_class obj = "GetterProxy";
    getter_proxy_extensible : L.object_extensible obj = false;
    getter_proxy_code : L.object_code obj = LjsInitEnv.privGetterProxyFun;
    getter_proxy_func : binds (L.object_properties obj) "func"
        (L.attributes_data_of (L.attributes_data_intro v false false false))
}.

Record setter_proxy obj v : Prop := {
    setter_proxy_proto : L.object_proto obj = L.value_null;
    setter_proxy_class : L.object_class obj = "SetterProxy";
    setter_proxy_extensible : L.object_extensible obj = false;
    setter_proxy_code : L.object_code obj = LjsInitEnv.privSetterProxyFun;
    setter_proxy_func : binds (L.object_properties obj) "func"
        (L.attributes_data_of (L.attributes_data_intro v false false false))
}.

Record js_exn_object obj v : Prop := { 
    js_exn_object_proto : L.object_proto obj = L.value_null;
    js_exn_object_class : L.object_class obj = "JSError";
    js_exn_object_extensible : L.object_extensible obj = false;
    js_exn_object_exn : binds (L.object_properties obj) "%js-exn" 
        (L.attributes_data_of (L.attributes_data_intro v false false false))
}.

(** *** Properties of heap bisimulations
    Heap bisimulations must satisfy several properties in order to be useful
    in the proof:
    - They must be injective - every JS object has an unique corresponding S5 object.
    - The mapped adresses must actually correspond to some object in JS and S5 heaps. *)

(*
Definition rel_functional A B (R : A -> B -> Prop) :=
  forall a b b', (a, b) \in R -> (a, b') \in R -> b = b'.
*)

Definition heaps_bisim_lfun_obj BR :=
     forall jptr ptr1 ptr2, fact_js_obj jptr ptr1 \in BR -> fact_js_obj jptr ptr2 \in BR -> ptr1 = ptr2.

Definition heaps_bisim_lfun_env BR :=
     forall jeptr ptr1 ptr2, fact_js_env jeptr ptr1 \in BR -> fact_js_env jeptr ptr2 \in BR -> ptr1 = ptr2.

Definition heaps_bisim_rfun_obj BR :=
     forall jptr1 jptr2 ptr, fact_js_obj jptr1 ptr \in BR -> fact_js_obj jptr2 ptr \in BR -> jptr1 = jptr2.

Definition heaps_bisim_rfun_env BR :=
     forall jeptr1 jeptr2 ptr, fact_js_env jeptr1 ptr \in BR -> fact_js_env jeptr2 ptr \in BR -> jeptr1 = jeptr2.

Definition heaps_bisim_ltotal_obj BR jst :=
    forall jptr, index jst jptr -> exists ptr, fact_js_obj jptr ptr \in BR.

Definition heaps_bisim_ltotal_env BR jst :=
    forall jeptr, index jst jeptr -> exists ptr, fact_js_env jeptr ptr \in BR.

Definition heaps_bisim_lnoghost_obj BR jst :=
    forall jptr ptr, fact_js_obj jptr ptr \in BR -> index jst jptr.

Definition heaps_bisim_lnoghost_env BR jst :=
    forall jeptr ptr, fact_js_env jeptr ptr \in BR -> index jst jeptr.

Definition heaps_bisim_rnoghost_obj BR st :=
    forall xptr ptr, fact_js_obj xptr ptr \in BR -> index st ptr.

Definition heaps_bisim_rnoghost_env BR st :=
    forall xptr ptr, fact_js_env xptr ptr \in BR -> index st ptr.

Definition heaps_bisim_obj BR jst st := forall jptr ptr jobj obj, 
     fact_js_obj jptr ptr \in BR -> 
     binds jst jptr jobj ->
     binds st ptr obj ->
     object_related BR jobj obj.

Definition heaps_bisim_env BR jst st := forall jeptr ptr jer obj, 
     fact_js_env jeptr ptr \in BR -> 
     binds jst jeptr jer ->
     binds st ptr obj ->
     env_record_related BR jer obj.

Record heaps_bisim_consistent BR jst st : Prop := {
    heaps_bisim_consistent_bisim_obj : heaps_bisim_obj BR jst st;
    heaps_bisim_consistent_bisim_env : heaps_bisim_env BR jst st;
    heaps_bisim_consistent_lfun_obj : heaps_bisim_lfun_obj BR;
    heaps_bisim_consistent_lfun_env : heaps_bisim_lfun_env BR;
    heaps_bisim_consistent_rfun_obj : heaps_bisim_rfun_obj BR;
    heaps_bisim_consistent_rfun_env : heaps_bisim_rfun_env BR;
    heaps_bisim_consistent_ltotal_obj : heaps_bisim_ltotal_obj BR jst;
    heaps_bisim_consistent_ltotal_env : heaps_bisim_ltotal_env BR jst;
    heaps_bisim_consistent_lnoghost_obj : heaps_bisim_lnoghost_obj BR jst;
    heaps_bisim_consistent_lnoghost_env : heaps_bisim_lnoghost_env BR jst;
    heaps_bisim_consistent_rnoghost_obj : heaps_bisim_rnoghost_obj BR st;
    heaps_bisim_consistent_rnoghost_env : heaps_bisim_rnoghost_env BR st
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

Inductive js_exn_object_ptr st ptr v : Prop :=
| js_exn_object_ptr_intro : forall obj, binds st ptr obj -> js_exn_object obj v -> js_exn_object_ptr st ptr v.

(** The relationship is as follows:
    - Normal results in JS map to normal results in S5.
    - Throws in JS translate to throws with a wrapper in S5.
    - Returns in JS translate to S5 breaks to a special label "%%ret".
    - Breaks in JS translate to S5 breaks, the label is tagged with "%%break".
    - Continues in JS translate to S5 breaks, the label is tagged with "%%continue". 
    Note that exceptions and breaks are never empty. *)

Inductive res_related BR jst st : J.res -> L.res -> Prop :=
| res_related_normal : forall jrv v,
    resvalue_related BR jrv v ->
    res_related BR jst st (J.res_intro J.restype_normal jrv J.label_empty) 
        (L.res_value v)
| res_related_throw : forall jv ptr v,
    js_exn_object_ptr st ptr v ->
    value_related BR jv v ->
    res_related BR jst st (J.res_intro J.restype_throw (J.resvalue_value jv) J.label_empty) 
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
Inductive lexical_env_related BR : J.lexical_env -> L.value -> Prop :=
| lexical_env_related_nil : 
    lexical_env_related BR nil L.value_null
| lexical_env_related_cons : forall jeptr jlenv ptr v,
    fact_js_env jeptr ptr \in BR ->
    fact_ctx_parent ptr v \in BR ->
    lexical_env_related BR jlenv v ->
    lexical_env_related BR (jeptr::jlenv) (L.value_object ptr)
.

(* Relates the lexical contexts *)
Record execution_ctx_related BR jc c := {
    execution_ctx_related_this_binding : forall v,
        binds c "$this" v ->
        value_related BR (J.execution_ctx_this_binding jc) v;
    execution_ctx_related_strictness_flag : forall v, 
        binds c "$strict" v ->
        v = L.value_bool (J.execution_ctx_strict jc);
    execution_ctx_related_lexical_env : forall v,
        binds c "$context" v ->
        lexical_env_related BR (J.execution_ctx_lexical_env jc) v
}.

Definition global_env_record_exists BR c := forall v,
        binds c "%globalContext" v ->
        exists ptr,
        v = L.value_object ptr /\
        fact_js_env J.env_loc_global_env_record ptr \in BR.

(* States that the variable environment and lexical environment exist *)
Record env_records_exist BR jc := { 
    env_record_exist_variable_env : 
        forall jeptr, Mem jeptr (J.execution_ctx_variable_env jc) -> exists ptr, fact_js_env jeptr ptr \in BR;
    env_record_exist_lexical_env : 
        forall jeptr, Mem jeptr (J.execution_ctx_lexical_env jc) -> exists ptr, fact_js_env jeptr ptr \in BR
}.

(** *** Preallocated objects invariant
    States that EcmaScript preallocated objects can be found in the LJS context. *)

Definition prealloc_in_ctx_list := [
    (J.prealloc_native_error J.native_error_eval, "%EvalErrorGlobalFuncObj");
    (J.prealloc_native_error J.native_error_range, "%RangeErrorGlobalFuncObj");
    (J.prealloc_native_error J.native_error_ref, "%ReferenceErrorGlobalFuncObj");
    (J.prealloc_native_error J.native_error_syntax, "%SyntaxErrorGlobalFuncObj");
    (J.prealloc_native_error J.native_error_type, "%TypeErrorGlobalFuncObj");
    (J.prealloc_native_error_proto J.native_error_eval, "%EvalErrorProto");
    (J.prealloc_native_error_proto J.native_error_range, "%RangeErrorProto");
    (J.prealloc_native_error_proto J.native_error_ref, "%ReferenceErrorProto");
    (J.prealloc_native_error_proto J.native_error_syntax, "%SyntaxErrorProto");
    (J.prealloc_native_error_proto J.native_error_type, "%TypeErrorProto")
].

Definition prealloc_in_ctx BR c := forall jpre s v, 
    Mem (jpre, s) prealloc_in_ctx_list ->
    binds c s v ->
    exists ptr,
    v = L.value_object ptr /\
    fact_js_obj (J.object_loc_prealloc jpre) ptr \in BR.

(** *** Other invariants *)

Definition ctx_parent_ok BR st :=
    forall ptr v,
    fact_ctx_parent ptr v \in BR ->
    exists obj,
    binds st ptr obj /\
    binds (L.object_internal obj) "parent" v.

Definition getter_proxy_ok BR st :=
    forall ptr v,
    fact_getter_proxy ptr v \in BR ->
    exists obj,
    binds st ptr obj /\
    getter_proxy obj v.

Definition setter_proxy_ok BR st :=
    forall ptr v,
    fact_setter_proxy ptr v \in BR ->
    exists obj,
    binds st ptr obj /\
    setter_proxy obj v.

(** *** Initial bisimulation. *)

Parameter initBR : fact_set. (* TODO *)

(** *** Invariant predicate
    The complete set of invariants, combined in one predicate to make proofs simpler. *)

Record state_invariant BR jst jc c st : Prop := {
    state_invariant_bisim_includes_init : initBR \c BR;
    state_invariant_heaps_bisim_consistent : heaps_bisim_consistent BR jst st;
    state_invariant_ctx_parent_ok : ctx_parent_ok BR st;
    state_invariant_getter_proxy_ok : getter_proxy_ok BR st;
    state_invariant_setter_proxy_ok : setter_proxy_ok BR st;
    state_invariant_execution_ctx_related : execution_ctx_related BR jc c;
    state_invariant_includes_init_ctx : includes_init_ctx c;
    state_invariant_env_records_exist : env_records_exist BR jc;
    state_invariant_prealloc_related : prealloc_in_ctx BR c;
    state_invariant_global_env_record_exists : global_env_record_exists BR c;
    state_invariant_js_state_fresh_ok : J.state_fresh_ok jst
}.

(** ** Theorem statement  
    Factored out, because it is used in many lemmas. *)

(** *** Theorem conclusions
    They state what must hold if the preconditions are satisfied. *)

Definition concl_ext_expr_value BR jst jc c st st' r jee P :=
    exists BR' jst' jr,
    J.red_expr jst jc jee (J.out_ter jst' jr) /\ 
    ((exists jv, jr = J.res_val jv /\ P jv) \/
     J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw) /\
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.

(* unused
Definition concl_expr_value BR jst jc c st st' r je :=  
    concl_ext_expr_value BR jst jc c st st' r (J.expr_basic je).
*)
Definition concl_stat BR jst jc c st st' r jt :=
    exists BR' jst' jr,
    J.red_stat jst jc (J.stat_basic jt) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' jc c st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.

Definition concl_spec {A : Type} BR jst jc c st st' r jes 
    (P : fact_set -> J.state -> A -> Prop) 
    (Q : fact_set -> J.state -> J.res -> Prop) :=
    exists BR' jst',
    ((exists x, J.red_spec jst jc jes (J.specret_val jst' x) /\ P BR' jst' x) \/
     (exists jr, 
        J.red_spec jst jc jes (@J.specret_out A (J.out_ter jst' jr)) /\ 
        J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\
        res_related BR' jst' st' jr r /\ Q BR' jst' jr)) /\
    state_invariant BR' jst' jc c st' /\ 
    BR \c BR'.

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
    (P : fact_set -> J.state -> J.execution_ctx -> L.ctx -> L.store -> L.res -> A -> Prop) := 
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
