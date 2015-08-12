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
| fact_iarray : L.object_ptr -> list L.value -> fact
| fact_ctx_parent : L.object_ptr -> L.value -> fact
.

Definition fact_set := finset fact. (* TODO: lib-bag-ize set *)

Implicit Type BR : fact_set.

Inductive fact_ptr : fact -> L.object_ptr -> Prop :=
| fact_ptr_js_obj : forall jptr ptr, fact_ptr (fact_js_obj jptr ptr) ptr
| fact_ptr_js_env : forall jeptr ptr, fact_ptr (fact_js_env jeptr ptr) ptr
| fact_ptr_getter_proxy : forall ptr v, fact_ptr (fact_getter_proxy ptr v) ptr
| fact_ptr_setter_proxy : forall ptr v, fact_ptr (fact_setter_proxy ptr v) ptr
| fact_ptr_iarray : forall ptr vs, fact_ptr (fact_iarray ptr vs) ptr
.

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

(** *** Relating lists of values
    Useful for function arguments. *)

Definition values_related BR : list J.value -> list L.value -> Prop := Forall2 (value_related BR).

(** *** Relating the JS lexical environment 
    Has to be defined early because of function objects. *)

Inductive lexical_env_related BR : J.lexical_env -> L.value -> Prop :=
| lexical_env_related_nil : 
    lexical_env_related BR nil L.value_null
| lexical_env_related_cons : forall jeptr jlenv ptr v,
    fact_js_env jeptr ptr \in BR ->
    fact_ctx_parent ptr v \in BR ->
    lexical_env_related BR jlenv v ->
    lexical_env_related BR (jeptr::jlenv) (L.value_object ptr)
.
(* States that the variable environment and lexical environment exist *)

Definition env_records_exist_env BR jle :=
    forall jeptr, Mem jeptr jle -> exists ptr, fact_js_env jeptr ptr \in BR.

(** *** S5 environment presence invariant 
    States that the initial LJS context ("the environment") can always be accessed
    (and thus is never shadowed). *)

Definition includes_init_ctx c :=
    forall i v v', binds c i v -> binds LjsInitEnv.init_ctx i v' -> v = v'. 

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

(* TODO move, should go to LibOption *)
Section OptionPred.
Variables A B C D : Type.

Inductive Option (P : A -> Prop) : option A -> Prop :=
| Option_some : forall a, P a -> Option P (Some a) 
| Option_none : Option P None 
.

Inductive Option2 (P : A -> B -> Prop) : option A -> option B -> Prop :=
| Option2_some : forall a a', P a a' -> Option2 P (Some a) (Some a')
| Option2_none : Option2 P None None
.

Inductive Option3 (P : A -> B -> C -> Prop) : option A -> option B -> option C -> Prop :=
| Option3_some : forall a a' a'', P a a' a'' -> Option3 P (Some a) (Some a') (Some a'')
| Option3_none : Option3 P None None None
.

Inductive Option4 (P : A -> B -> C -> D -> Prop) : option A -> option B -> option C -> option D -> Prop :=
| Option4_some : forall a a' a'' a''', P a a' a'' a''' -> Option4 P (Some a) (Some a') (Some a'') (Some a''')
| Option4_none : Option4 P None None None None
.

End OptionPred.

Definition option_value_related BR := Option2 (value_related BR).

Inductive prealloc_related : J.prealloc -> L.object_ptr -> Prop :=
| prealloc_related_global : 
    prealloc_related J.prealloc_global LjsInitEnv.ptr_privglobal
| prealloc_related_global_eval : 
    prealloc_related J.prealloc_global_eval LjsInitEnv.ptr_priveval
| prealloc_related_global_is_finite : 
    prealloc_related J.prealloc_global_is_finite LjsInitEnv.ptr_privisFinite
| prealloc_related_global_is_nan : 
    prealloc_related J.prealloc_global_is_nan LjsInitEnv.ptr_privisNaN
| prealloc_related_global_parse_float : 
    prealloc_related J.prealloc_global_parse_float LjsInitEnv.ptr_privparseFloat
| prealloc_related_global_parse_int : 
    prealloc_related J.prealloc_global_parse_int LjsInitEnv.ptr_privparseInt
| prealloc_related_object : 
    prealloc_related J.prealloc_object LjsInitEnv.ptr_privObjectGlobalFuncObj
| prealloc_related_object_proto : 
    prealloc_related J.prealloc_object LjsInitEnv.ptr_privObjectProto
| prealloc_related_object_get_proto_of : 
    prealloc_related J.prealloc_object_get_proto_of LjsInitEnv.ptr_privgpo
| prealloc_related_object_get_own_prop_descriptor : 
    prealloc_related J.prealloc_object_get_own_prop_descriptor LjsInitEnv.ptr_privgopd
| prealloc_related_object_get_own_prop_name : 
    prealloc_related J.prealloc_object_get_own_prop_name LjsInitEnv.ptr_privgopn
| prealloc_related_object_create : 
    prealloc_related J.prealloc_object_create LjsInitEnv.ptr_privcreate
| prealloc_related_object_define_prop : 
    prealloc_related J.prealloc_object_define_prop LjsInitEnv.ptr_privdefineProperty
| prealloc_related_object_define_props : 
    prealloc_related J.prealloc_object_define_props LjsInitEnv.ptr_privdefineProperties
| prealloc_related_object_seal : 
    prealloc_related J.prealloc_object_seal LjsInitEnv.ptr_privseal
| prealloc_related_object_freeze : 
    prealloc_related J.prealloc_object_freeze LjsInitEnv.ptr_privfreeze
| prealloc_related_object_prevent_extensions : 
    prealloc_related J.prealloc_object_prevent_extensions LjsInitEnv.ptr_privpreventExtensions
| prealloc_related_object_is_sealed : 
    prealloc_related J.prealloc_object_is_sealed LjsInitEnv.ptr_privisSealed
| prealloc_related_object_is_frozen : 
    prealloc_related J.prealloc_object_is_frozen LjsInitEnv.ptr_privisFrozen
| prealloc_related_object_is_extensible : 
    prealloc_related J.prealloc_object_is_extensible LjsInitEnv.ptr_privisExtensible
| prealloc_related_object_keys : 
    prealloc_related J.prealloc_object_keys LjsInitEnv.ptr_privkeys
| prealloc_related_object_proto_to_string : 
    prealloc_related J.prealloc_object_proto_to_string LjsInitEnv.ptr_privobjectToString
| prealloc_related_object_proto_value_of : 
    prealloc_related J.prealloc_object_proto_value_of LjsInitEnv.ptr_privobjectValueOf
| prealloc_related_object_proto_has_own_prop : 
    prealloc_related J.prealloc_object_proto_has_own_prop LjsInitEnv.ptr_privhasOwnProperty
| prealloc_related_object_proto_is_prototype_of : 
    prealloc_related J.prealloc_object_proto_is_prototype_of LjsInitEnv.ptr_privisPrototypeOf
| prealloc_related_object_proto_prop_is_enumerable : 
    prealloc_related J.prealloc_object_proto_prop_is_enumerable LjsInitEnv.ptr_privpropEnum
| prealloc_related_function : 
    prealloc_related J.prealloc_function LjsInitEnv.ptr_privFunctionGlobalFuncObj
| prealloc_related_function_proto : 
    prealloc_related J.prealloc_function_proto LjsInitEnv.ptr_privFunctionProto
| prealloc_related_function_to_string : 
    prealloc_related J.prealloc_function_proto_to_string LjsInitEnv.ptr_privfunctionToString
| prealloc_related_function_apply : 
    prealloc_related J.prealloc_function_proto_apply LjsInitEnv.ptr_privapply
| prealloc_related_function_bind : 
    prealloc_related J.prealloc_function_proto_bind LjsInitEnv.ptr_privbind
| prealloc_related_bool : 
    prealloc_related J.prealloc_bool LjsInitEnv.ptr_privBooleanGlobalFuncObj
| prealloc_related_bool_proto : 
    prealloc_related J.prealloc_bool_proto LjsInitEnv.ptr_privBooleanProto
| prealloc_related_bool_proto_to_string : 
    prealloc_related J.prealloc_bool_proto_to_string LjsInitEnv.ptr_privbooleanToString
| prealloc_related_bool_proto_value_of : 
    prealloc_related J.prealloc_bool_proto_value_of LjsInitEnv.ptr_privbooleanValueOf
| prealloc_related_number : 
    prealloc_related J.prealloc_number LjsInitEnv.ptr_privNumberGlobalFuncObj
| prealloc_related_number_proto : 
    prealloc_related J.prealloc_number_proto LjsInitEnv.ptr_privNumberProto
| prealloc_related_number_proto_to_string : 
    prealloc_related J.prealloc_number_proto_to_string LjsInitEnv.ptr_privnumberToString
| prealloc_related_number_proto_value_of : 
    prealloc_related J.prealloc_number_proto_value_of LjsInitEnv.ptr_privnumberValueOf
| prealloc_related_number_proto_to_fixed : 
    prealloc_related J.prealloc_number_proto_to_fixed LjsInitEnv.ptr_privtoFixed
| prealloc_related_number_proto_to_exponential : 
    prealloc_related J.prealloc_number_proto_to_exponential LjsInitEnv.ptr_privtoExponential
| prealloc_related_number_proto_to_precision : 
    prealloc_related J.prealloc_number_proto_to_precision LjsInitEnv.ptr_privtoPrecision
(* | prealloc_related_array : 
    prealloc_related J.prealloc_array LjsInitEnv.ptr_priv
| prealloc_related_array_is_array : 
    prealloc_related J.prealloc_array_is_array LjsInitEnv.ptr_priv
| prealloc_related_array_proto_to_string : 
    prealloc_related J.prealloc_array_proto_to_string LjsInitEnv.ptr_priv *)
| prealloc_related_string : 
    prealloc_related J.prealloc_string LjsInitEnv.ptr_privStringGlobalFuncObj
| prealloc_related_string_proto : 
    prealloc_related J.prealloc_string_proto LjsInitEnv.ptr_privStringProto
| prealloc_related_string_proto_to_string : 
    prealloc_related J.prealloc_string_proto_to_string LjsInitEnv.ptr_privstringToString
| prealloc_related_string_proto_value_of : 
    prealloc_related J.prealloc_string_proto_value_of LjsInitEnv.ptr_privstringValueOf
| prealloc_related_string_proto_char_at : 
    prealloc_related J.prealloc_string_proto_char_at LjsInitEnv.ptr_privcharAt
| prealloc_related_string_proto_char_code_at : 
    prealloc_related J.prealloc_string_proto_char_code_at LjsInitEnv.ptr_privcharCodeAt
| prealloc_related_error : 
    prealloc_related J.prealloc_error LjsInitEnv.ptr_privErrorGlobalFuncObj
| prealloc_related_error_proto : 
    prealloc_related J.prealloc_error_proto LjsInitEnv.ptr_privErrorProto
| prealloc_related_native_error_eval : 
    prealloc_related (J.prealloc_native_error J.native_error_eval) LjsInitEnv.ptr_privEvalErrorGlobalFuncObj
| prealloc_related_native_error_eval_proto : 
    prealloc_related (J.prealloc_native_error_proto J.native_error_eval) LjsInitEnv.ptr_privEvalErrorProto
| prealloc_related_native_error_range : 
    prealloc_related (J.prealloc_native_error J.native_error_range) LjsInitEnv.ptr_privRangeErrorGlobalFuncObj
| prealloc_related_native_error_range_proto : 
    prealloc_related (J.prealloc_native_error_proto J.native_error_range) LjsInitEnv.ptr_privRangeErrorProto
| prealloc_related_native_error_ref : 
    prealloc_related (J.prealloc_native_error J.native_error_ref) LjsInitEnv.ptr_privReferenceErrorGlobalFuncObj
| prealloc_related_native_error_ref_proto : 
    prealloc_related (J.prealloc_native_error_proto J.native_error_ref) LjsInitEnv.ptr_privReferenceErrorProto
| prealloc_related_native_error_syntax : 
    prealloc_related (J.prealloc_native_error J.native_error_syntax) LjsInitEnv.ptr_privSyntaxErrorGlobalFuncObj
| prealloc_related_native_error_syntax_proto : 
    prealloc_related (J.prealloc_native_error_proto J.native_error_syntax) LjsInitEnv.ptr_privSyntaxErrorProto
| prealloc_related_native_error_type : 
    prealloc_related (J.prealloc_native_error J.native_error_type) LjsInitEnv.ptr_privTypeErrorGlobalFuncObj
| prealloc_related_native_error_type_proto : 
    prealloc_related (J.prealloc_native_error_proto J.native_error_type) LjsInitEnv.ptr_privTypeErrorProto
.

Inductive call_prealloc_related : J.prealloc ->  L.value -> Prop :=
| call_prealloc_related_global_eval : 
    call_prealloc_related J.prealloc_global_eval LjsInitEnv.privevalCall
| call_prealloc_related_global_is_finite : 
    call_prealloc_related J.prealloc_global_is_finite LjsInitEnv.privisFiniteCall
| call_prealloc_related_global_is_nan : 
    call_prealloc_related J.prealloc_global_is_nan LjsInitEnv.privisNaNCall
| call_prealloc_related_global_parse_float : 
    call_prealloc_related J.prealloc_global_parse_float LjsInitEnv.privparseFloatCall
| call_prealloc_related_global_parse_int : 
    call_prealloc_related J.prealloc_global_parse_int LjsInitEnv.privparseIntCall
| call_prealloc_related_object : 
    call_prealloc_related J.prealloc_object LjsInitEnv.privObjectCall
| call_prealloc_related_object_get_proto_of : 
    call_prealloc_related J.prealloc_object_get_proto_of LjsInitEnv.privgpoCall
| call_prealloc_related_object_get_own_prop_descriptor : 
    call_prealloc_related J.prealloc_object_get_own_prop_descriptor LjsInitEnv.privgopdCall
| call_prealloc_related_object_get_own_prop_name : 
    call_prealloc_related J.prealloc_object_get_own_prop_name LjsInitEnv.privgopnCall
| call_prealloc_related_object_create : 
    call_prealloc_related J.prealloc_object_create LjsInitEnv.privcreateCall
| call_prealloc_related_object_define_prop : 
    call_prealloc_related J.prealloc_object_define_prop LjsInitEnv.privdefinePropertyCall
| call_prealloc_related_object_define_props : 
    call_prealloc_related J.prealloc_object_define_props LjsInitEnv.privdefinePropertiesCall
| call_prealloc_related_object_seal : 
    call_prealloc_related J.prealloc_object_seal LjsInitEnv.privsealCall
| call_prealloc_related_object_freeze : 
    call_prealloc_related J.prealloc_object_freeze LjsInitEnv.privfreezeCall
| call_prealloc_related_object_prevent_extensions : 
    call_prealloc_related J.prealloc_object_prevent_extensions LjsInitEnv.privpreventExtensionsCall
| call_prealloc_related_object_is_sealed : 
    call_prealloc_related J.prealloc_object_is_sealed LjsInitEnv.privisSealedCall
| call_prealloc_related_object_is_frozen : 
    call_prealloc_related J.prealloc_object_is_frozen LjsInitEnv.privisFrozenCall
| call_prealloc_related_object_is_extensible : 
    call_prealloc_related J.prealloc_object_is_extensible LjsInitEnv.privisExtensibleCall
| call_prealloc_related_object_keys : 
    call_prealloc_related J.prealloc_object_keys LjsInitEnv.privkeysCall
| call_prealloc_related_object_proto_to_string : 
    call_prealloc_related J.prealloc_object_proto_to_string LjsInitEnv.privobjectToStringCall
(* | call_prealloc_related_object_proto_value_of : 
    call_prealloc_related J.prealloc_object_proto_value_of LjsInitEnv.privvalueOfCall *)
| call_prealloc_related_object_proto_has_own_prop : 
    call_prealloc_related J.prealloc_object_proto_has_own_prop LjsInitEnv.privhasOwnPropertyCall
| call_prealloc_related_object_proto_is_prototype_of : 
    call_prealloc_related J.prealloc_object_proto_is_prototype_of LjsInitEnv.privisPrototypeOfCall
| call_prealloc_related_object_proto_prop_is_enumerable : 
    call_prealloc_related J.prealloc_object_proto_prop_is_enumerable LjsInitEnv.privpropEnumCall
| call_prealloc_related_function : 
    call_prealloc_related J.prealloc_function LjsInitEnv.privRunSelfConstructorCall
(* | call_prealloc_related_function_proto : 
    call_prealloc_related J.prealloc_function_proto LjsInitEnv.privCall *)
| call_prealloc_related_function_to_string : 
    call_prealloc_related J.prealloc_function_proto_to_string LjsInitEnv.privfunctionToStringCall
| call_prealloc_related_function_apply : 
    call_prealloc_related J.prealloc_function_proto_apply LjsInitEnv.privapplyCall
| call_prealloc_related_function_bind : 
    call_prealloc_related J.prealloc_function_proto_bind LjsInitEnv.privbindCall
| call_prealloc_related_bool : 
    call_prealloc_related J.prealloc_bool LjsInitEnv.privBooleanCall
| call_prealloc_related_bool_proto_to_string : 
    call_prealloc_related J.prealloc_bool_proto_to_string LjsInitEnv.privbooleanToStringCall
(* | call_prealloc_related_bool_proto_value_of : 
    call_prealloc_related J.prealloc_bool_proto_value_of LjsInitEnv.privCall *)
| call_prealloc_related_number : 
    call_prealloc_related J.prealloc_number LjsInitEnv.privNumberCall
| call_prealloc_related_number_proto_to_string : 
    call_prealloc_related J.prealloc_number_proto_to_string LjsInitEnv.privnumberToStringCall
(* | call_prealloc_related_number_proto_value_of : 
    call_prealloc_related J.prealloc_number_proto_value_of LjsInitEnv.privCall *)
| call_prealloc_related_number_proto_to_fixed : 
    call_prealloc_related J.prealloc_number_proto_to_fixed LjsInitEnv.privtoFixedCall
| call_prealloc_related_number_proto_to_exponential : 
    call_prealloc_related J.prealloc_number_proto_to_exponential LjsInitEnv.privtoExponentialCall
| call_prealloc_related_number_proto_to_precision : 
    call_prealloc_related J.prealloc_number_proto_to_precision LjsInitEnv.privtoPrecisionCall
(* | call_prealloc_related_array : 
    call_prealloc_related J.prealloc_array LjsInitEnv.privCall
| call_prealloc_related_array_is_array : 
    call_prealloc_related J.prealloc_array_is_array LjsInitEnv.privCall
| call_prealloc_related_array_proto_to_string : 
    call_prealloc_related J.prealloc_array_proto_to_string LjsInitEnv.privCall *)
| call_prealloc_related_string : 
    call_prealloc_related J.prealloc_string LjsInitEnv.privStringCall
| call_prealloc_related_string_proto_to_string : 
    call_prealloc_related J.prealloc_string_proto_to_string LjsInitEnv.privstringToStringCall
(* | call_prealloc_related_string_proto_value_of : 
    call_prealloc_related J.prealloc_string_proto_value_of LjsInitEnv.privCall *)
| call_prealloc_related_string_proto_char_at : 
    call_prealloc_related J.prealloc_string_proto_char_at LjsInitEnv.privcharAtCall
| call_prealloc_related_string_proto_char_code_at : 
    call_prealloc_related J.prealloc_string_proto_char_code_at LjsInitEnv.privcharCodeAtCall
| call_prealloc_related_error : 
    call_prealloc_related J.prealloc_error LjsInitEnv.privRunSelfConstructorCall
| call_prealloc_related_native_error_eval : 
    call_prealloc_related (J.prealloc_native_error J.native_error_eval) LjsInitEnv.privRunSelfConstructorCall
| call_prealloc_related_native_error_range : 
    call_prealloc_related (J.prealloc_native_error J.native_error_range) LjsInitEnv.privRunSelfConstructorCall
| call_prealloc_related_native_error_ref : 
    call_prealloc_related (J.prealloc_native_error J.native_error_ref) LjsInitEnv.privRunSelfConstructorCall
| call_prealloc_related_native_error_syntax : 
    call_prealloc_related (J.prealloc_native_error J.native_error_syntax) LjsInitEnv.privRunSelfConstructorCall
| call_prealloc_related_native_error_type : 
    call_prealloc_related (J.prealloc_native_error J.native_error_type) LjsInitEnv.privRunSelfConstructorCall
.

Inductive call_related : J.call -> L.value -> Prop :=
| call_related_prealloc : forall jpre v, call_prealloc_related jpre v -> call_related (J.call_prealloc jpre) v
| call_related_default : call_related J.call_default LjsInitEnv.privDefaultCall
| call_related_after_bind : call_related J.call_after_bind LjsInitEnv.privBindObjCall
.

Inductive option_call_related : option J.call -> L.value -> Prop :=
| option_call_related_some : forall jcall v, call_related jcall v -> option_call_related (Some jcall) v
| option_call_related_none : option_call_related None L.value_undefined
.

Inductive construct_prealloc_related : J.prealloc -> L.value -> Prop :=
| construct_prealloc_related_object : construct_prealloc_related J.prealloc_object LjsInitEnv.privObjectConstructor
| construct_prealloc_related_function : construct_prealloc_related J.prealloc_function LjsInitEnv.privFunctionConstructor
| construct_prealloc_related_bool : construct_prealloc_related J.prealloc_bool LjsInitEnv.privBooleanConstructor
| construct_prealloc_related_number : construct_prealloc_related J.prealloc_number LjsInitEnv.privNumberConstructor
| construct_prealloc_related_array : construct_prealloc_related J.prealloc_array LjsInitEnv.privArrayConstructor
| construct_prealloc_related_string : construct_prealloc_related J.prealloc_string LjsInitEnv.privStringConstructor
| construct_prealloc_related_error : construct_prealloc_related J.prealloc_error LjsInitEnv.privErrorConstructor
| construct_prealloc_related_native_error_eval : 
    construct_prealloc_related (J.prealloc_native_error J.native_error_eval) LjsInitEnv.privEvalErrorConstructor
| construct_prealloc_related_native_error_range : 
    construct_prealloc_related (J.prealloc_native_error J.native_error_range) LjsInitEnv.privRangeErrorConstructor
| construct_prealloc_related_native_error_ref : 
    construct_prealloc_related (J.prealloc_native_error J.native_error_ref) LjsInitEnv.privReferenceErrorConstructor
| construct_prealloc_related_native_error_syntax : 
    construct_prealloc_related (J.prealloc_native_error J.native_error_syntax) LjsInitEnv.privSyntaxErrorConstructor
| construct_prealloc_related_native_error_type : 
    construct_prealloc_related (J.prealloc_native_error J.native_error_type) LjsInitEnv.privTypeErrorConstructor
.

Inductive construct_related : J.construct -> L.value -> Prop :=
| construct_related_prealloc : forall jpre v, 
    construct_prealloc_related jpre v -> construct_related (J.construct_prealloc jpre) v
| construct_related_default : construct_related J.construct_default LjsInitEnv.privDefaultConstruct
| construct_related_after_bind : construct_related J.construct_after_bind LjsInitEnv.privBindConstructor
.

Definition option_construct_related := Option2 construct_related.

Definition funcbody_expr is jp := E.make_lambda_expr E.ejs_to_ljs E.make_fobj is (E.js_prog_to_ejs jp).

Definition funcbody_closure ctxl is jp := L.closure_intro ctxl None ["obj"; "$this"; "args"] (funcbody_expr is jp).

Record usercode_context_invariant BR jle b c : Prop := {
    usercode_context_invariant_includes_init_ctx : includes_init_ctx c;
    usercode_context_invariant_lexical_env_related : forall v,
        binds c "$context" v -> lexical_env_related BR jle v;
    usercode_context_invariant_strict : forall v,
        binds c "$strict" v -> v = L.value_bool b;
    usercode_context_invariant_env_records_exist : env_records_exist_env BR jle;
    usercode_context_invariant_has_strict : index c "$strict"
}.

Inductive usercode_related BR : J.funcbody -> list string -> J.lexical_env -> L.value -> Prop :=
| usercode_related_intro : forall jp s is jle c, 
    usercode_context_invariant BR jle (J.prog_intro_strictness jp) c ->
    usercode_related BR (J.funcbody_intro jp s) is jle 
        (L.value_closure (funcbody_closure (to_list c) is jp))
.

Definition option_usercode_related BR := Option4 (usercode_related BR).

Inductive codetxt_related : J.funcbody -> L.value -> Prop :=
| codetxt_related_intro : forall jp s, codetxt_related (J.funcbody_intro jp s) (L.value_string s)
.

Definition option_codetxt_related := Option2 codetxt_related.

Inductive func_strict_related : J.funcbody -> L.value -> Prop :=
| func_strict_related_intro : forall jfb, func_strict_related jfb (L.value_bool (J.funcbody_is_strict jfb))
.

Definition option_func_strict_related := Option2 func_strict_related.

Record object_prim_related BR jobj obj : Prop := {
    object_prim_related_class : J.object_class_ jobj = L.object_class obj;
    object_prim_related_extensible : J.object_extensible_ jobj = L.object_extensible obj;
    object_prim_related_prototype : value_related BR (J.object_proto_ jobj) (L.object_proto obj);
    object_prim_related_primval : 
        option_value_related BR (J.object_prim_value_ jobj) (L.object_internal obj\("primval"?));
    object_prim_related_call : option_call_related (J.object_call_ jobj) (L.object_code obj);
    object_prim_related_construct : 
        option_construct_related (J.object_construct_ jobj) (L.object_internal obj\("construct"?));
    object_prim_related_usercode :
        option_usercode_related BR (J.object_code_ jobj) (J.object_formal_parameters_ jobj)
            (J.object_scope_ jobj) (L.object_internal obj\("usercode"?));
    object_prim_related_codetxt :
        option_codetxt_related (J.object_code_ jobj) (L.object_internal obj\("codetxt"?));
    object_prim_related_func_strict :
        option_func_strict_related (J.object_code_ jobj) (L.object_internal obj\("strict"?))
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
    | J.mutability_immutable => false
    | _ => true
    end.

Definition decl_env_record_vars_related BR jder props := forall s,
    ~index jder s /\ ~index props s \/
    exists jmut jv v, 
        jmut <> J.mutability_uninitialized_immutable /\
        binds jder s (jmut, jv) /\ 
        binds props s (L.attributes_data_of (L.attributes_data_intro v 
            (mutability_writable jmut) true (mutability_configurable jmut))) /\
        value_related BR jv v.

(* Relates environment records *)
Record decl_env_record_related BR jder obj : Prop := {
    decl_env_record_related_proto : L.object_proto obj = L.value_null;
    decl_env_record_related_class : L.object_class obj = "DeclEnvRec";
    decl_env_record_related_extensible : L.object_extensible obj = true;
    decl_env_record_related_vars : decl_env_record_vars_related BR jder (L.object_properties obj)
}.

Record object_env_record_related BR jptr b ptr obj : Prop := {
    object_env_record_related_proto : L.object_proto obj = L.value_null;
    object_env_record_related_class : L.object_class obj = "ObjEnvRec";
    object_env_record_related_provideThis : binds (L.object_internal obj) "provideThis" (L.value_bool b);
    object_env_record_related_bindings : binds (L.object_internal obj) "bindings" (L.value_object ptr);
    object_env_record_related_bisim : fact_js_obj jptr ptr \in BR
}.

Inductive env_record_related BR : J.env_record -> L.object -> Prop :=
| env_record_related_decl : forall jder obj,
    decl_env_record_related BR jder obj ->
    env_record_related BR (J.env_record_decl jder) obj
| env_record_related_object : forall b ptr jptr obj,
    object_env_record_related BR jptr b ptr obj ->
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

Record iarray_object obj vs : Prop := {
    iarray_has_args : forall k v, 
        Nth k vs v -> 
        binds (L.object_properties obj) (string_of_nat k) 
            (L.attributes_data_of (L.attributes_data_intro v false false false));
    iarray_all_args : forall s,
        index (L.object_properties obj) s -> 
        exists k v, s = string_of_nat k /\ Nth k vs v
}.

(*
Inductive arg_list st : list L.value -> L.value -> Prop := 
| arg_list_intro : forall ptr obj vs, 
    binds st ptr obj -> arg_list_object obj vs -> arg_list st vs (L.value_object ptr).
*)

Inductive preftype_name : J.preftype -> string -> Type :=
| preftype_name_number : preftype_name J.preftype_number "number"
| preftype_name_string : preftype_name J.preftype_string "string"
.

Inductive option_preftype_name : option J.preftype -> string -> Type :=
| option_preftype_name_some : forall jprefo s, preftype_name jprefo s -> option_preftype_name (Some jprefo) s
| option_preftype_name_none : option_preftype_name None "number"
.

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

Definition heaps_bisim_rfun BR :=
    forall ptr f1 f2, f1 \in BR -> f2 \in BR -> fact_ptr f1 ptr -> fact_ptr f2 ptr -> f1 = f2.

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

Definition heaps_bisim_rnoghost BR st :=
    forall f ptr, f \in BR -> fact_ptr f ptr -> index st ptr.

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

Definition heaps_bisim_getter_proxy BR st :=
    forall ptr obj v,
    fact_getter_proxy ptr v \in BR ->
    binds st ptr obj ->
    getter_proxy obj v.

Definition heaps_bisim_setter_proxy BR st :=
    forall ptr obj v,
    fact_setter_proxy ptr v \in BR ->
    binds st ptr obj ->
    setter_proxy obj v.

Definition heaps_bisim_iarray BR st :=
    forall ptr obj vs,
    fact_iarray ptr vs \in BR ->
    binds st ptr obj ->
    iarray_object obj vs.

Record heaps_bisim_consistent BR jst st : Prop := {
    heaps_bisim_consistent_bisim_obj : heaps_bisim_obj BR jst st;
    heaps_bisim_consistent_bisim_env : heaps_bisim_env BR jst st;
    heaps_bisim_consistent_getter_proxy : heaps_bisim_getter_proxy BR st;
    heaps_bisim_consistent_setter_proxy : heaps_bisim_setter_proxy BR st;
    heaps_bisim_consistent_iarray : heaps_bisim_iarray BR st;
    heaps_bisim_consistent_lfun_obj : heaps_bisim_lfun_obj BR;
    heaps_bisim_consistent_lfun_env : heaps_bisim_lfun_env BR;
    heaps_bisim_consistent_rfun : heaps_bisim_rfun BR;    
    heaps_bisim_consistent_ltotal_obj : heaps_bisim_ltotal_obj BR jst;
    heaps_bisim_consistent_ltotal_env : heaps_bisim_ltotal_env BR jst;
    heaps_bisim_consistent_lnoghost_obj : heaps_bisim_lnoghost_obj BR jst;
    heaps_bisim_consistent_lnoghost_env : heaps_bisim_lnoghost_env BR jst;
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

(** ** Relating reference base values *)

Definition js_object_coercible jv := jv <> J.value_prim J.prim_undef /\ jv <> J.value_prim J.prim_null.

Inductive ref_base_type_related BR : J.ref_base_type -> L.value -> Prop :=
| ref_base_type_related_undefined : 
    ref_base_type_related BR (J.ref_base_type_value (J.value_prim J.prim_undef)) L.value_null
| ref_base_type_related_value : forall jv v,
    js_object_coercible jv ->
    value_related BR jv v ->
    ref_base_type_related BR (J.ref_base_type_value jv) v
| ref_base_type_related_env_loc : forall jeptr ptr,
    fact_js_env jeptr ptr \in BR ->
    ref_base_type_related BR (J.ref_base_type_env_loc jeptr) (L.value_object ptr)
.

(** ** Invariants 
    To relate JS and S5 programs, certain invariants must hold at all times. *)

(** *** Relating lexical environments *)

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
        lexical_env_related BR (J.execution_ctx_lexical_env jc) v;
    execution_ctx_related_variable_env : forall v,
        binds c "$vcontext" v ->
        lexical_env_related BR (J.execution_ctx_variable_env jc) v
}.

(** *** Initial bisimulation. *)

Parameter initBR : fact_set. (* TODO *)

(** *** Invariant predicate
    The complete set of invariants, combined in one predicate to make proofs simpler. *)

Definition ctx_parent_ok BR st :=
    forall ptr v,
    fact_ctx_parent ptr v \in BR ->
    exists jeptr obj,
    fact_js_env jeptr ptr \in BR /\
    binds st ptr obj /\
    binds (L.object_internal obj) "parent" v.

Record state_invariant BR jst st : Prop := {
    state_invariant_heaps_bisim_consistent : heaps_bisim_consistent BR jst st;
    state_invariant_ctx_parent_ok : ctx_parent_ok BR st;
    state_invariant_js_state_fresh_ok : J.state_fresh_ok jst
}.

(** *** For restoring invariants after function application *)

Record env_records_exist BR jc := { 
    env_record_exist_variable_env : env_records_exist_env BR (J.execution_ctx_variable_env jc);
    env_record_exist_lexical_env : env_records_exist_env BR (J.execution_ctx_lexical_env jc)
}.

Record context_invariant BR jc c : Prop := {
    context_invariant_bisim_includes_init : initBR \c BR;
    context_invariant_execution_ctx_related : execution_ctx_related BR jc c;
    context_invariant_includes_init_ctx : includes_init_ctx c;
    context_invariant_env_records_exist : env_records_exist BR jc
}.

(** ** Theorem statement  
    Factored out, because it is used in many lemmas. *)

(** *** Theorem conclusions
    They state what must hold if the preconditions are satisfied. *)

Definition concl_ext_expr_resvalue_gen BR jst jc c st st' r jee P Q :=
    exists BR' jst' jr,
    J.red_expr jst jc jee (J.out_ter jst' jr) /\ 
    ((exists jrv, jr = J.res_normal jrv /\ P BR' jst' jrv) \/
     J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\ Q) /\
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.

Definition concl_ext_expr_resvalue BR jst jc c st st' r jee P :=
    concl_ext_expr_resvalue_gen BR jst jc c st st' r jee (fun _ _ x => P x) True.

Definition concl_ext_expr_value_gen BR jst jc c st st' r jee P Q := (* TODO use resvalue ? *)
    exists BR' jst' jr,
    J.red_expr jst jc jee (J.out_ter jst' jr) /\ 
    ((exists jv, jr = J.res_val jv /\ P BR' jst' jv) \/
     J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\ Q) /\
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.

Definition concl_ext_expr_value BR jst jc c st st' r jee P :=
    concl_ext_expr_value_gen BR jst jc c st st' r jee (fun _ _ x => P x) True.

Definition concl_stat BR jst jc c st st' r jt :=
    exists BR' jst' jr,
    J.red_stat jst jc (J.stat_basic jt) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.

Definition concl_spec {A : Type} BR jst jc c st st' r jes 
    (P : fact_set -> J.state -> A -> Prop) :=
    exists BR' jst' sr,
    J.red_spec jst jc jes sr /\
    state_invariant BR' jst' st' /\ 
    BR \c BR' /\
    ((exists x, sr = J.specret_val jst' x /\ P BR' jst' x) \/
     (exists jr, sr = @J.specret_out A (J.out_ter jst' jr) /\ 
        J.abort (J.out_ter jst' jr) /\ 
        J.res_type jr = J.restype_throw /\
        res_related BR' jst' st' jr r)).

Inductive ejs_reference_producing : E.expr -> Prop :=
| ejs_reference_producing_get_field : forall ee1 ee2, ejs_reference_producing (E.expr_get_field ee1 ee2)
| ejs_reference_producing_var_id : forall s, ejs_reference_producing (E.expr_var_id s)
.

Inductive js_reference_producing : J.expr -> Prop :=
| js_reference_producing_access : forall je1 je2, js_reference_producing (J.expr_access je1 je2)
| js_reference_producing_member : forall je s, js_reference_producing (J.expr_member je s)
| js_reference_producing_identifier : forall s, js_reference_producing (J.expr_identifier s)
.

Inductive ref_base_type_var : J.ref_base_type -> Prop :=
| ref_base_type_var_undefined : ref_base_type_var (J.ref_base_type_value (J.value_prim J.prim_undef))
| ref_base_type_var_env_loc : forall jeptr, ref_base_type_var (J.ref_base_type_env_loc jeptr)
.

Inductive ref_base_type_obj : J.ref_base_type -> Prop :=
| ref_base_type_obj_coercible : forall jv, js_object_coercible jv -> ref_base_type_obj (J.ref_base_type_value jv)
.

Inductive js_reference_type : J.expr -> J.ref_base_type -> Prop :=
| js_reference_type_access : forall je1 je2 jrbt, 
    ref_base_type_obj jrbt -> js_reference_type (J.expr_access je1 je2) jrbt
| js_reference_type_member : forall je s jrbt, 
    ref_base_type_obj jrbt -> js_reference_type (J.expr_member je s) jrbt
| js_reference_type_identifier : forall s jrbt, 
    ref_base_type_var jrbt -> js_reference_type (J.expr_identifier s) jrbt
.

Inductive js_red_spec_get_value_or_abort : J.execution_ctx -> J.expr -> J.out -> J.specret J.value -> Prop :=
| js_red_spec_get_value_or_abort_abort : forall jc je jo, 
    J.abort jo -> js_red_spec_get_value_or_abort jc je jo (J.specret_out jo)
| js_red_spec_get_value_or_abort_value : forall jst jc je jv, 
    ~js_reference_producing je ->
    js_red_spec_get_value_or_abort jc je 
        (J.out_ter jst (J.res_normal (J.resvalue_value jv))) (J.specret_val jst jv)
| js_red_spec_get_value_or_abort_get_value : forall jst jc je jref jsr, 
    js_reference_producing je ->
    js_reference_type je (J.ref_base jref) ->
    J.red_spec jst jc (J.spec_get_value (J.resvalue_ref jref)) jsr -> 
    js_red_spec_get_value_or_abort jc je (J.out_ter jst (J.res_normal (J.resvalue_ref jref))) jsr
.

Record js_red_expr_getvalue jst jc je jo jsr : Prop := {
    js_red_expr_getvalue_red_expr : J.red_expr jst jc (J.expr_basic je) jo;
    js_red_expr_getvalue_red_spec : js_red_spec_get_value_or_abort jc je jo jsr
}.

Definition concl_expr_getvalue BR jst jc c st st' r je := 
    exists BR' jst' jo sr,
    js_red_expr_getvalue jst jc je jo sr /\
    state_invariant BR' jst' st' /\ 
    BR \c BR' /\
    ((exists jv, sr = J.specret_val jst' jv /\ exists v, r = L.res_value v /\ value_related BR' jv v) \/
     (exists jr, sr = @J.specret_out J.value (J.out_ter jst' jr) /\ 
        J.abort (J.out_ter jst' jr) /\ 
        J.res_type jr = J.restype_throw /\
        res_related BR' jst' st' jr r)).

(** *** Theorem statements *)

Definition th_expr k je := 
    forall BR jst jc c st st' r, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    L.red_exprh k c st (L.expr_basic (js_expr_to_ljs je)) (L.out_ter st' r) ->
    concl_expr_getvalue BR jst jc c st st' r je.

Definition th_stat k jt := 
    forall BR jst jc c st st' r, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    L.red_exprh k c st (L.expr_basic (js_stat_to_ljs jt)) (L.out_ter st' r) ->
    concl_stat BR jst jc c st st' r jt.

Definition th_spec {A : Type} k e jes 
    (P : fact_set -> J.state -> J.execution_ctx -> L.ctx -> L.store -> L.res -> A -> Prop) := 
    forall BR jst jc c st st' r, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    L.red_exprh k c st (L.expr_basic e) (L.out_ter st' r) ->
    concl_spec BR jst jc c st st' r jes (fun BR' jst' a => P BR' jst' jc c st' r a).

Definition th_ext_expr_unary k v jeef P :=
    forall BR jst jc c st st' r v1 jv1, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 -> 
    L.red_exprh k c st (L.expr_app_2 v [v1]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (jeef jv1) P.

Definition th_ext_expr_binary k v jeef P :=
    forall BR jst jc c st st' r v1 jv1 v2 jv2, 
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 -> 
    value_related BR jv2 v2 -> 
    L.red_exprh k c st (L.expr_app_2 v [v1; v2]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (jeef jv1 jv2) P.

Definition th_call_prealloc k jpre :=
    forall BR jst jc c st st' r jv v jvs vs v' v'' ptr,
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    values_related BR jvs vs ->
    fact_iarray ptr vs \in BR ->
    call_prealloc_related jpre v' ->
    L.red_exprh k c st (L.expr_app_2 v' [v''; v; L.value_object ptr]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_call_prealloc jpre jv jvs) (fun _ => True).

Definition th_construct_prealloc k jpre :=
    forall BR jst jc c st st' r jvs vs v' v'' ptr,
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    fact_iarray ptr vs \in BR ->
    construct_prealloc_related jpre v' ->
    L.red_exprh k c st (L.expr_app_2 v' [v''; L.value_object ptr]) (L.out_ter st' r) ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_construct_prealloc jpre jvs) (fun _ => True).

(** *** Inductive hypotheses 
    The form of the induction hypotheses, as used in the proof. 
    Height induction is used to make proofs simpler. *)

Definition ih_expr k := forall je k', (k' < k)%nat -> th_expr k' je.

Definition ih_stat k := forall jt k', (k' < k)%nat -> th_stat k' jt.

Definition ih_call_prealloc k := forall jpre k', (k' < k)%nat -> th_call_prealloc k' jpre.
