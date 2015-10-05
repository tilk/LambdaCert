Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

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

Lemma option_usercode_related_none_lemma : forall BR (m : finmap _ _) s,
     ~index m s ->
     option_usercode_related BR None None None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option_usercode_related_some_lemma : forall BR (m : finmap _ _) s jfb is jle v,
     binds m s v ->
     usercode_related BR jfb is jle v ->
     option_usercode_related BR (Some jfb) (Some is) (Some jle) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Resolve option_usercode_related_none_lemma option_usercode_related_some_lemma : js_ljs.

Lemma option2_none_lemma : forall T1 T2 (P : T1 -> T2 -> Prop) (m : finmap _ _) s,
     ~index m s ->
     Option2 P None (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma option2_some_lemma : forall T1 T2 (P : T1 -> T2 -> Prop) (m : finmap string T2) s x1 x2,
     binds m s x2 ->
     P x1 x2 ->
     Option2 P (Some x1) (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Lemma builtin_method_related_none_lemma : forall T (V : T) (P : T -> L.value -> Prop) (m : finmap _ _) s,
    ~index m s ->
    builtin_method_related V P V (m\(s?)).
Proof.
    intros.
    erewrite read_option_not_index_inv by prove_bag.
    eauto_js.
Qed.

Lemma builtin_method_related_some_lemma : forall T (V : T) (P : T -> L.value -> Prop) (m : finmap _ _) s x1 x2,
    binds m s x2 ->
    P x1 x2 ->
    builtin_method_related V P x1 (m\(s?)).
Proof.
    intros.
    erewrite read_option_binds_inv by prove_bag.
    eauto_js.
Qed.

Hint Extern 2 (option_construct_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_construct_related _ _) => eapply option2_some_lemma : js_ljs.
Hint Extern 2 (option_codetxt_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_codetxt_related _ _) => eapply option2_some_lemma : js_ljs.
Hint Extern 2 (option_func_strict_related _ _) => eapply option2_none_lemma : js_ljs.
Hint Extern 2 (option_func_strict_related _ _) => eapply option2_some_lemma : js_ljs.
Hint Extern 2 (builtin_get_related _ _) => eapply builtin_method_related_none_lemma : js_ljs.
Hint Extern 2 (builtin_get_related _ _) => eapply builtin_method_related_some_lemma : js_ljs.
Hint Extern 2 (builtin_get_own_prop_related _ _) => eapply builtin_method_related_none_lemma : js_ljs.
Hint Extern 2 (builtin_get_own_prop_related _ _) => eapply builtin_method_related_some_lemma : js_ljs.
Hint Extern 2 (builtin_define_own_prop_related _ _) => eapply builtin_method_related_none_lemma : js_ljs.
Hint Extern 2 (builtin_define_own_prop_related _ _) => eapply builtin_method_related_some_lemma : js_ljs.

Lemma nindex_update_diff : forall `{Index_update_diff_eq} M k k' x', 
    k <> k' -> ~index M k -> ~index (M \(k' := x')) k.
Proof.
    intros. rewrite index_update_diff_eq; eauto.
Qed.

Hint Resolve @nindex_update_diff : bag.

Lemma zero_arg_obj_lemma : forall BR k jst jc c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privzeroArgObj []) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' ptr,
    state_invariant BR' jst st' /\
    BR \c BR' /\
    st \c st' /\
    fact_iarray ptr [] \in BR' /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred Hcinv Hinv.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    evar (obj : L.object).
    cuts Hiobj : (iarray_object obj []); subst obj. {
        exists (\{fact_iarray (fresh st) []} \u BR) (fresh st).
        jauto_js.
    }
    constructor. 
    + introv Hnth. inverts Hnth.
    + introv Hindex. simpl in Hindex. rewrite index_empty_eq in Hindex. false.
Qed.

(* TODO move *)
Lemma state_invariant_bisim_obj_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    exists jobj,
    binds jst jptr jobj /\
    object_related BR jobj obj.
Proof.
    introv Hinv Hbs Hbinds.
    lets Hjbinds : heaps_bisim_consistent_lnoghost_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs.
    rewrite index_binds_eq in Hjbinds.
    destruct Hjbinds as (jobj&Hjbinds).
    lets Hrel : heaps_bisim_consistent_bisim_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs Hjbinds Hbinds.
    jauto.
Qed.

(* *** descriptors *)

Definition concl_ljs_new_descriptor st st' r desc :=
    exists ptr obj,
    property_descriptor desc obj /\
    r = L.res_value (L.value_object ptr) /\
    st \c st' /\
    binds st' ptr obj /\
    ~index st ptr.

(* TODO move to definitions *)
Inductive data_descriptor_attr : string -> bool -> Prop :=
| data_descriptor_attr_value : data_descriptor_attr "value" true
| data_descriptor_attr_writable : data_descriptor_attr "writable" true
| data_descriptor_attr_get : data_descriptor_attr "get" false
| data_descriptor_attr_set : data_descriptor_attr "set" false
| data_descriptor_attr_enumerable : data_descriptor_attr "enumerable" true
| data_descriptor_attr_configurable : data_descriptor_attr "configurable" true.

Inductive accessor_descriptor_attr : string -> bool -> Prop :=
| accessor_descriptor_attr_get : accessor_descriptor_attr "get" true
| accessor_descriptor_attr_set : accessor_descriptor_attr "set" true
| accessor_descriptor_attr_value : accessor_descriptor_attr "value" false
| accessor_descriptor_attr_writable : accessor_descriptor_attr "writable" false
| accessor_descriptor_attr_enumerable : accessor_descriptor_attr "enumerable" true
| accessor_descriptor_attr_configurable : accessor_descriptor_attr "configurable" true.

(* TODO move *)
Lemma ljs_descriptor_attr_read_option_lemma : forall desc obj s fu,
    property_descriptor desc obj ->
    ljs_descriptor_attr s fu ->
    L.object_properties obj\(s?) = LibOption.map frozen_data_attr (fu desc).
Proof.
    introv Hpdescr Hattr.
    destruct Hpdescr.
    destruct Hattr; assumption.
Qed.

(* TODO move *)
Lemma ljs_descriptor_attr_binds_lemma : forall desc obj s attrs fu,
    property_descriptor desc obj ->
    ljs_descriptor_attr s fu ->
    binds (L.object_properties obj) s attrs ->
    exists v,
    fu desc = Some v /\
    attrs = frozen_data_attr v.
Proof.
    introv Hpdesc Hattr Hbinds.
    lets Heq : ljs_descriptor_attr_read_option_lemma Hpdesc Hattr.
    erewrite read_option_binds_inv in Heq by eassumption.
    destruct (fu desc); simpl in Heq; tryfalse.
    injects. jauto.
Qed.

(* TODO move *)
Lemma ljs_descriptor_attr_index_lemma : forall desc obj s fu,
    property_descriptor desc obj ->
    ljs_descriptor_attr s fu ->
    index (L.object_properties obj) s ->
    exists v,
    fu desc = Some v.
Proof.
    introv Hpdesc Hattr Hindex.
    rewrite index_binds_eq in Hindex.
    destruct Hindex as (attrs&Hbinds).
    lets Hx : ljs_descriptor_attr_binds_lemma Hpdesc Hattr Hbinds.
    destruct_hyp Hx. jauto.
Qed.

(* TODO move *)
Lemma ljs_descriptor_attr_not_index_lemma : forall desc obj s fu,
    property_descriptor desc obj ->
    ljs_descriptor_attr s fu ->
    ~index (L.object_properties obj) s ->
    fu desc = None.
Proof.
    introv Hpdesc Hattr Hnindex.
    lets Heq : ljs_descriptor_attr_read_option_lemma Hpdesc Hattr.
    erewrite read_option_not_index_inv in Heq by eassumption.
    destruct (fu desc); simpl in Heq; tryfalse.
    reflexivity.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_read_option_lemma : forall desc obj s b,
    property_descriptor desc obj ->
    is_full_data_descriptor desc ->
    data_descriptor_attr s b ->
    is_some (L.object_properties obj\(s?)) = b.
Proof.
    introv Hpdesc Hfdd Hdattr.
    unfolds in Hfdd.
    destruct_hyp Hfdd.
    destruct Hpdesc.
    simpls.
    unfolds L.prop_name.
    destruct Hdattr; match goal with H : _\(_?) = _ |- _ => rewrite H end; reflexivity.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_index_lemma : forall desc obj s,
    property_descriptor desc obj ->
    is_full_data_descriptor desc ->
    data_descriptor_attr s true ->
    index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hdattr.
    lets Hs : is_full_data_descriptor_read_option_lemma Hpdesc Hfdd Hdattr.
    unfolds is_some. cases_match_option.
    prove_bag.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_not_index_lemma : forall desc obj s,
    property_descriptor desc obj ->
    is_full_data_descriptor desc ->
    data_descriptor_attr s false ->
    ~index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hdattr.
    lets Hs : is_full_data_descriptor_read_option_lemma Hpdesc Hfdd Hdattr.
    unfolds is_some. cases_match_option.
    prove_bag.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_binds_lemma_2 : forall desc obj s fu,
    property_descriptor desc obj ->
    is_full_data_descriptor desc ->
    ljs_descriptor_attr s fu ->
    data_descriptor_attr s true ->
    exists v,
    fu desc = Some v /\
    binds (L.object_properties obj) s (frozen_data_attr v).
Proof.
    introv Hpdesc Hfdd Hattr Hdattr.
    forwards Hidx : is_full_data_descriptor_index_lemma Hpdesc Hfdd Hdattr.
    rewrite index_binds_eq in Hidx.
    destruct Hidx as (attrs&Hbinds).
    forwards (v&Hfu&Hattrs) : ljs_descriptor_attr_binds_lemma Hpdesc Hattr Hbinds.
    subst_hyp Hattrs.
    jauto.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_not_index_lemma_2 : forall desc obj s fu,
    property_descriptor desc obj ->
    is_full_data_descriptor desc ->
    ljs_descriptor_attr s fu ->
    data_descriptor_attr s false ->
    fu desc = None /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hattr Hdattr.
    forwards Hidx : is_full_data_descriptor_not_index_lemma Hpdesc Hfdd Hdattr.
    forwards Hfu : ljs_descriptor_attr_not_index_lemma Hpdesc Hattr Hidx.
    jauto.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_read_option_lemma : forall desc obj s b,
    property_descriptor desc obj ->
    is_full_accessor_descriptor desc ->
    accessor_descriptor_attr s b ->
    is_some (L.object_properties obj\(s?)) = b.
Proof.
    introv Hpdesc Hfdd Hdattr.
    unfolds in Hfdd.
    destruct_hyp Hfdd.
    destruct Hpdesc.
    simpls.
    unfolds L.prop_name.
    destruct Hdattr; match goal with H : _\(_?) = _ |- _ => rewrite H end; reflexivity.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_index_lemma : forall desc obj s,
    property_descriptor desc obj ->
    is_full_accessor_descriptor desc ->
    accessor_descriptor_attr s true ->
    index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hdattr.
    lets Hs : is_full_accessor_descriptor_read_option_lemma Hpdesc Hfdd Hdattr.
    unfolds is_some. cases_match_option.
    prove_bag.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_not_index_lemma : forall desc obj s,
    property_descriptor desc obj ->
    is_full_accessor_descriptor desc ->
    accessor_descriptor_attr s false ->
    ~index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hdattr.
    lets Hs : is_full_accessor_descriptor_read_option_lemma Hpdesc Hfdd Hdattr.
    unfolds is_some. cases_match_option.
    prove_bag.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_binds_lemma_2 : forall desc obj s fu,
    property_descriptor desc obj ->
    is_full_accessor_descriptor desc ->
    ljs_descriptor_attr s fu ->
    accessor_descriptor_attr s true ->
    exists v,
    fu desc = Some v /\
    binds (L.object_properties obj) s (frozen_data_attr v).
Proof.
    introv Hpdesc Hfdd Hattr Hdattr.
    forwards Hidx : is_full_accessor_descriptor_index_lemma Hpdesc Hfdd Hdattr.
    rewrite index_binds_eq in Hidx.
    destruct Hidx as (attrs&Hbinds).
    forwards (v&Hfu&Hattrs) : ljs_descriptor_attr_binds_lemma Hpdesc Hattr Hbinds.
    subst_hyp Hattrs.
    jauto.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_not_index_lemma_2 : forall desc obj s fu,
    property_descriptor desc obj ->
    is_full_accessor_descriptor desc ->
    ljs_descriptor_attr s fu ->
    accessor_descriptor_attr s false ->
    fu desc = None /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hpdesc Hfdd Hattr Hdattr.
    forwards Hidx : is_full_accessor_descriptor_not_index_lemma Hpdesc Hfdd Hdattr.
    forwards Hfu : ljs_descriptor_attr_not_index_lemma Hpdesc Hattr Hidx.
    jauto.
Qed.

(* TODO to LibOption *)
Lemma unsome_default_map_lemma : forall A B (f : A -> B) a oa,
    unsome_default (f a) (LibOption.map f oa) = f (unsome_default a oa).
Proof.
    introv.
    destruct oa; reflexivity.
Qed.

(* TODO move *)
Lemma descriptor_attr_update_lemma : forall A (a : A) oa,
    Some (unsome_default a oa) = descriptor_attr_update (Some a) oa.
Proof.
    introv. destruct oa; reflexivity.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_implies_is_data_descriptor : forall desc,
    is_full_data_descriptor desc -> is_data_descriptor desc.
Proof.
    introv Hfdd. unfolds in Hfdd. destruct_hyp Hfdd.
    unfolds. eauto.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_implies_is_accessor_descriptor : forall desc,
    is_full_accessor_descriptor desc -> is_accessor_descriptor desc.
Proof.
    introv Hfdd. unfolds in Hfdd. destruct_hyp Hfdd.
    unfolds. eauto.
Qed.

(* TODO move *)
Lemma data_descriptor_is_not_accessor_descriptor : forall v1 b1 b2 b3,
    ~is_accessor_descriptor (data_descriptor v1 b1 b2 b3).
Proof.
    introv Had. destruct Had as [Had|Had]; simpl in Had; tryfalse.
Qed.

(* TODO move *)
Lemma accessor_descriptor_is_not_data_descriptor : forall v1 v2 b1 b2,
    ~is_data_descriptor (accessor_descriptor v1 v2 b1 b2).
Proof.
    introv Had. destruct Had as [Had|Had]; simpl in Had; tryfalse.
Qed.

(* TODO move *)
Lemma data_descriptor_is_data_descriptor : forall v1 b1 b2 b3,
    is_data_descriptor (data_descriptor v1 b1 b2 b3).
Proof.
    introv. left. auto.
Qed.

(* TODO move *)
Lemma accessor_descriptor_is_accessor_descriptor : forall v1 v2 b1 b2,
    is_accessor_descriptor (accessor_descriptor v1 v2 b1 b2).
Proof.
    introv. left. auto.
Qed.

(* TODO move *)
Lemma is_full_descriptor_data_lemma : forall desc,
    is_full_descriptor desc -> is_data_descriptor desc -> is_full_data_descriptor desc.
Proof.
    introv Hfd Hdd.
    destruct Hfd as [Hfdd|Hfad]; try assumption.
    unfolds is_full_accessor_descriptor.
    destruct_hyp Hfad.
    lets : accessor_descriptor_is_not_data_descriptor Hdd. tryfalse.
Qed.

(* TODO move *)
Lemma is_not_full_descriptor_lemma : forall desc,
    ~is_data_descriptor desc -> ~is_accessor_descriptor desc -> ~is_full_descriptor desc.
Proof.
    introv Hndd Hnad Hfd.
    destruct Hfd as [Hfdd|Hfad].
    + applys Hndd. applys is_full_data_descriptor_implies_is_data_descriptor. assumption.
    + applys Hnad. applys is_full_accessor_descriptor_implies_is_accessor_descriptor. assumption.
Qed.

(* TODO move *)
Lemma is_full_descriptor_accessor_lemma : forall desc,
    is_full_descriptor desc -> is_accessor_descriptor desc -> is_full_accessor_descriptor desc.
Proof.
    introv Hfd Hdd.
    destruct Hfd as [Hfdd|Hfad]; try assumption.
    unfolds is_full_data_descriptor.
    destruct_hyp Hfdd.
    lets : data_descriptor_is_not_accessor_descriptor Hdd. tryfalse.
Qed.

(* TODO move *)
Lemma is_full_data_descriptor_default_data_descriptor :
    is_full_data_descriptor default_data_descriptor.
Proof.
    unfolds. jauto.
Qed.

(* TODO move *)
Lemma is_full_accessor_descriptor_default_accessor_descriptor :
    is_full_accessor_descriptor default_accessor_descriptor.
Proof.
    unfolds. jauto.
Qed.

Lemma make_data_descriptor_ljs_lemma : forall k c st st' r v b1 b2 b3,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeDataDescriptor 
        [v; L.value_bool b1; L.value_bool b2; L.value_bool b3]) (L.out_ter st' r) ->
    concl_ljs_new_descriptor st st' r (data_descriptor v b1 b2 b3).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    unfolds.
    jauto_js.
    unfolds data_descriptor.
    constructor; try reflexivity; simpl; 
    (eapply read_option_binds_inv; rew_binds_eq) || (eapply read_option_not_index_inv; rew_index_eq);
    auto 10.
Qed.

Lemma make_accessor_descriptor_ljs_lemma : forall k c st st' r v1 v2 b1 b2,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeAccessorDescriptor 
        [v1; v2; L.value_bool b1; L.value_bool b2]) (L.out_ter st' r) ->
    concl_ljs_new_descriptor st st' r (accessor_descriptor v1 v2 b1 b2).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    unfolds.
    jauto_js.
    unfolds accessor_descriptor.
    constructor; try reflexivity; simpl; 
    (eapply read_option_binds_inv; rew_binds_eq) || (eapply read_option_not_index_inv; rew_index_eq);
    auto 10.
Qed.

Lemma make_value_only_descriptor_ljs_lemma : forall k c st st' r v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeValueOnlyDescriptor [v]) (L.out_ter st' r) ->
    concl_ljs_new_descriptor st st' r (ljs_descriptor_intro (Some v) None None None None None).
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    unfolds.
    jauto_js.
    constructor; try reflexivity; simpl; 
    (eapply read_option_binds_inv; rew_binds_eq) || (eapply read_option_not_index_inv; rew_index_eq);
    auto 10.
Qed.

Lemma default_data_descriptor_ljs_lemma : forall k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdefaultDataDescriptor []) (L.out_ter st' r) ->
    concl_ljs_new_descriptor st st' r default_data_descriptor.
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : make_data_descriptor_ljs_lemma.
    assumption.
Qed.

Lemma default_accessor_descriptor_ljs_lemma : forall k c st st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdefaultAccessorDescriptor []) (L.out_ter st' r) ->
    concl_ljs_new_descriptor st st' r default_accessor_descriptor.
Proof.
    introv Hlred.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : make_accessor_descriptor_ljs_lemma.
    assumption.
Qed.

Lemma is_data_descriptor_ljs_lemma : forall k c st st' r ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privisDataDescriptor [L.value_object ptr]) (L.out_ter st' r) ->
    binds st ptr obj ->
    property_descriptor desc obj ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (is_data_descriptor desc))).
Proof.
    introv Hlred Hbinds Hpdesc.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* has value field *)
        repeat ljs_autoforward.
        forwards (x&EQx) : ljs_descriptor_attr_index_lemma ljs_descriptor_attr_value; try eassumption.
        asserts Hdd : (is_data_descriptor desc). { unfolds. rewrite EQx. eauto. }
        cases_isTrue; tryfalse.
        eauto.
    }
    repeat ljs_autoforward.
    cases_decide as Hidx2. { (* has writable field *)
        repeat ljs_autoforward.
        forwards (x&EQx) : ljs_descriptor_attr_index_lemma ljs_descriptor_attr_writable; try eassumption.
        asserts Hdd : (is_data_descriptor desc). { 
            unfolds ljs_descriptor_writable_v.
            unfolds. right. intro EQy. rewrite EQy in EQx. tryfalse.
        }
        cases_isTrue; tryfalse.
        eauto.
    }
    forwards : ljs_descriptor_attr_not_index_lemma ljs_descriptor_attr_value; try eassumption.
    forwards : ljs_descriptor_attr_not_index_lemma ljs_descriptor_attr_writable; try eassumption.
    unfolds ljs_descriptor_writable_v.
    sets_eq bw : (ljs_descriptor_writable desc); destruct bw; tryfalse.
    symmetry in EQbw.
    asserts Hdd : (~is_data_descriptor desc). {
        intro Hdd. destruct Hdd as [Hdd|Hdd]; auto.
    }
    cases_isTrue; tryfalse.
    eauto.
Qed.

Lemma is_accessor_descriptor_ljs_lemma : forall k c st st' r ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privisAccessorDescriptor [L.value_object ptr]) (L.out_ter st' r) ->
    binds st ptr obj ->
    property_descriptor desc obj ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (is_accessor_descriptor desc))).
Proof.
    introv Hlred Hbinds Hpdesc.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* has get field *)
        repeat ljs_autoforward.
        forwards (x&EQx) : ljs_descriptor_attr_index_lemma ljs_descriptor_attr_get; try eassumption.
        asserts Hdd : (is_accessor_descriptor desc). { unfolds. rewrite EQx. eauto. }
        cases_isTrue; tryfalse.
        eauto.
    }
    repeat ljs_autoforward.
    cases_decide as Hidx2. { (* has set field *)
        repeat ljs_autoforward.
        forwards (x&EQx) : ljs_descriptor_attr_index_lemma ljs_descriptor_attr_set; try eassumption.
        asserts Hdd : (is_accessor_descriptor desc). { unfolds. rewrite EQx. eauto. }
        cases_isTrue; tryfalse.
        eauto.
    }
    forwards : ljs_descriptor_attr_not_index_lemma ljs_descriptor_attr_get; try eassumption.
    forwards : ljs_descriptor_attr_not_index_lemma ljs_descriptor_attr_set; try eassumption.
    asserts Hdd : (~is_accessor_descriptor desc). {
        intro Hdd. destruct Hdd as [Hdd|Hdd]; auto.
    }
    cases_isTrue; tryfalse.
    eauto.
Qed.

Lemma is_generic_descriptor_ljs_lemma : forall k c st st' r ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privisGenericDescriptor [L.value_object ptr]) (L.out_ter st' r) ->
    binds st ptr obj ->
    property_descriptor desc obj ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (is_generic_descriptor desc))).
Proof.
    introv Hlred Hbinds Hpdesc.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : is_accessor_descriptor_ljs_lemma; try eassumption.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    cases_isTrue in * as Heq1. { (* is accessor *)
        repeat ljs_autoforward.
        unfolds is_generic_descriptor.
        cases_isTrue as Heq3; iauto.
    }
    repeat ljs_autoforward.
    forwards_th Hx : is_data_descriptor_ljs_lemma; try eassumption.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    cases_isTrue in * as Heq2. { (* is data *)
        unfolds is_generic_descriptor.
        cases_isTrue as Heq3; iauto.
    }
    unfolds is_generic_descriptor.
    cases_isTrue as Heq3; iauto.
Qed.

Lemma descriptor_field_get_ljs_lemma : forall k c st st' r v s fu ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdescriptorFieldGet [L.value_object ptr; L.value_string s; v])
        (L.out_ter st' r) ->
    ljs_descriptor_attr s fu ->
    property_descriptor desc obj ->
    binds st ptr obj ->
    st = st' /\ r = L.res_value (unsome_default v (fu desc)).
Proof.
    introv Hlred Hattr Hpdesc Hbinds.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* has prop *)
        repeat ljs_autoforward.
        lets (vv&Hfu&Hattrs) : ljs_descriptor_attr_binds_lemma Hpdesc Hattr. eassumption.
        subst_hyp Hattrs. rewrite Hfu.
        jauto.
    }
    repeat ljs_autoforward.
    forwards Hfu : ljs_descriptor_attr_not_index_lemma Hpdesc Hattr. eassumption.
    rewrite Hfu.
    jauto.
Qed.

Lemma update_data_descriptor_ljs_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privupdateDataDescriptor [L.value_object ptr1; L.value_object ptr2]) 
        (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    is_full_data_descriptor desc1 ->
    concl_ljs_new_descriptor st st' r (descriptor_update desc1 desc2).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpdesc1 Hpdesc2 Hfdd.
    ljs_invert_apply.
    forwards (v1&Hfu1&Hpb1) : is_full_data_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_value data_descriptor_attr_value.
    forwards (v2&Hfu2&Hpb2) : is_full_data_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_writable data_descriptor_attr_writable.
    forwards (v3&Hfu3&Hpb3) : is_full_data_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_enumerable data_descriptor_attr_enumerable.
    forwards (v4&Hfu4&Hpb4) : is_full_data_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_configurable data_descriptor_attr_configurable.
    forwards (Hfu5&Hni1) : is_full_data_descriptor_not_index_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_get data_descriptor_attr_get.
    forwards (Hfu6&Hni2) : is_full_data_descriptor_not_index_lemma_2 Hpdesc1 Hfdd
        ljs_descriptor_attr_set data_descriptor_attr_set.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_value | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_writable | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_enumerable | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_configurable | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    unfolds ljs_descriptor_configurable_v.
    sets_eq b1 : (ljs_descriptor_configurable desc1). destruct b1; tryfalse. injects.
    unfolds ljs_descriptor_enumerable_v.
    sets_eq b2 : (ljs_descriptor_enumerable desc1). destruct b2; tryfalse. injects.
    unfolds ljs_descriptor_writable_v.
    sets_eq b3 : (ljs_descriptor_writable desc1). destruct b3; tryfalse. injects.
    repeat rewrite unsome_default_map_lemma in *.
    forwards_th Hz : make_data_descriptor_ljs_lemma.
    unfolds data_descriptor.
    repeat rewrite descriptor_attr_update_lemma in Hz.
    rewrite EQb1 in Hz. rewrite EQb2 in Hz. rewrite EQb3 in Hz. rewrite <- Hfu1 in Hz.
    unfolds descriptor_update.
    rewrite Hfu5. rewrite Hfu6. assumption.
Qed.

Lemma update_accessor_descriptor_ljs_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privupdateAccessorDescriptor [L.value_object ptr1; L.value_object ptr2]) 
        (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    is_full_accessor_descriptor desc1 ->
    concl_ljs_new_descriptor st st' r (descriptor_update desc1 desc2).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpdesc1 Hpdesc2 Hfdd.
    ljs_invert_apply.
    forwards (v1&Hfu1&Hpb1) : is_full_accessor_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_get accessor_descriptor_attr_get.
    forwards (v2&Hfu2&Hpb2) : is_full_accessor_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_set accessor_descriptor_attr_set.
    forwards (v3&Hfu3&Hpb3) : is_full_accessor_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_enumerable accessor_descriptor_attr_enumerable.
    forwards (v4&Hfu4&Hpb4) : is_full_accessor_descriptor_binds_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_configurable accessor_descriptor_attr_configurable.
    forwards (Hfu5&Hni1) : is_full_accessor_descriptor_not_index_lemma_2 Hpdesc1 Hfdd 
        ljs_descriptor_attr_value accessor_descriptor_attr_value.
    forwards (Hfu6&Hni2) : is_full_accessor_descriptor_not_index_lemma_2 Hpdesc1 Hfdd
        ljs_descriptor_attr_writable accessor_descriptor_attr_writable.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_get | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_set | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_enumerable | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_get_ljs_lemma; 
        [eapply ljs_descriptor_attr_configurable | eapply Hpdesc2 | eapply Hbinds2 | idtac].
    simpl in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    unfolds ljs_descriptor_configurable_v.
    sets_eq b1 : (ljs_descriptor_configurable desc1). destruct b1; tryfalse. injects.
    unfolds ljs_descriptor_enumerable_v.
    sets_eq b2 : (ljs_descriptor_enumerable desc1). destruct b2; tryfalse. injects.
    repeat rewrite unsome_default_map_lemma in *.
    unfolds ljs_descriptor_writable_v.
    sets_eq b3 : (ljs_descriptor_writable desc1). destruct b3; tryfalse.
    repeat rewrite unsome_default_map_lemma in *.
    forwards_th Hz : make_accessor_descriptor_ljs_lemma.
    unfolds accessor_descriptor.
    repeat rewrite descriptor_attr_update_lemma in Hz.
    rewrite EQb1 in Hz. rewrite EQb2 in Hz. rewrite <- Hfu1 in Hz. rewrite <- Hfu2 in Hz.
    unfolds descriptor_update.
    rewrite Hfu5. rewrite <- EQb3. assumption.
Qed.

Lemma update_descriptor_ljs_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privupdateDescriptor [L.value_object ptr1; L.value_object ptr2]) 
        (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    is_full_descriptor desc1 ->
    concl_ljs_new_descriptor st st' r (descriptor_update desc1 desc2).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpdesc1 Hpdesc2 Hfd.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : is_data_descriptor_ljs_lemma; try eassumption.
    destruct_hyp Hx.
    cases_isTrue as Hdd. { (* data descriptor *)
        repeat ljs_autoforward.
        lets Hfdd : is_full_descriptor_data_lemma Hfd Hdd.
        forwards_th : update_data_descriptor_ljs_lemma; try eassumption.
    }
    repeat ljs_autoforward.
    forwards_th Hx : is_accessor_descriptor_ljs_lemma; try eassumption.
    destruct_hyp Hx.
    cases_isTrue as Had. { (* accessor descriptor *)
        repeat ljs_autoforward.
        lets Hfad : is_full_descriptor_accessor_lemma Hfd Had.
        forwards_th : update_accessor_descriptor_ljs_lemma; try eassumption.
    }
    repeat ljs_autoforward.
    lets Hnfd : is_not_full_descriptor_lemma Hdd Had. false.
Qed.

(* TODO to LibBagExt *)
Class Incl_not_index `{BagIncl T} `{BagIndex T A} :=
    { incl_not_index : forall M1 M2 k, M1 \c M2 -> ~index M2 k -> ~index M1 k }.

Section InclBinds.
Context `{BagIncl T} `{BagBinds A B T}.

Global Instance incl_not_index_from_incl_index :
    forall `{BagIndex T A},
    Incl_index -> Incl_not_index.
Proof.
    constructor. introv Hsub. 
    apply contrapose_intro. intro Hidx.
    applys incl_index Hsub Hidx.
Qed.

End InclBinds.

(* Hint Resolve @incl_not_index : bag. *)

Lemma to_data_descriptor_ljs_lemma : forall k c st st' r ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privtoDataDescriptor [L.value_object ptr]) (L.out_ter st' r) ->
    binds st ptr obj ->
    property_descriptor desc obj ->
    concl_ljs_new_descriptor st st' r (to_data_descriptor desc).
Proof.
    introv Hlred Hbinds Hpd.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : default_data_descriptor_ljs_lemma.
    unfold concl_ljs_new_descriptor in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : update_data_descriptor_ljs_lemma; try prove_bag.
        apply is_full_data_descriptor_default_data_descriptor.
    unfold concl_ljs_new_descriptor in Hx. destruct_hyp Hx.
    unfolds. jauto_js.
    applys @incl_not_index; eauto.
Qed.

Lemma to_accessor_descriptor_ljs_lemma : forall k c st st' r ptr obj desc,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privtoAccessorDescriptor [L.value_object ptr]) (L.out_ter st' r) ->
    binds st ptr obj ->
    property_descriptor desc obj ->
    concl_ljs_new_descriptor st st' r (to_accessor_descriptor desc).
Proof.
    introv Hlred Hbinds Hpd.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : default_accessor_descriptor_ljs_lemma.
    unfold concl_ljs_new_descriptor in Hx. destruct_hyp Hx.
    repeat ljs_autoforward.
    forwards_th Hx : update_accessor_descriptor_ljs_lemma; try prove_bag.
        apply is_full_accessor_descriptor_default_accessor_descriptor.
    unfold concl_ljs_new_descriptor in Hx. destruct_hyp Hx.
    unfolds. jauto_js.
    applys @incl_not_index; eauto.
Qed.

Lemma descriptor_field_contains_ljs_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2 s fu,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdescriptorFieldContains 
        [L.value_object ptr1; L.value_object ptr2; L.value_string s]) 
        (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    ljs_descriptor_attr s fu ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (if_some_value_then_same (fu desc2) (fu desc1)))).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpd1 Hpd2 Hattr.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx1. {
        rewrite index_binds_eq in Hidx1. destruct Hidx1 as (attrs1&Habinds1).
        forwards (x&EQx&EQattrs1) : ljs_descriptor_attr_binds_lemma Habinds1; try eassumption.
        rewrite EQx. subst_hyp EQattrs1.
        repeat ljs_autoforward.
        cases_decide as Hidx2. {
            rewrite index_binds_eq in Hidx2. destruct Hidx2 as (attrs2&Habinds2).
            forwards (y&EQy&EQattrs2) : ljs_descriptor_attr_binds_lemma Habinds2; try eassumption.
            rewrite EQy. subst_hyp EQattrs2.
            repeat ljs_autoforward.
            rewrite decide_spec.
            auto.
        } {
            forwards EQy : ljs_descriptor_attr_not_index_lemma Hidx2; try eassumption.
            rewrite EQy.
            repeat ljs_autoforward.
            simpl. cases_isTrue; tryfalse.
            auto.
        }
    } {
        forwards EQx : ljs_descriptor_attr_not_index_lemma Hidx1; try eassumption.
        rewrite EQx.
        repeat ljs_autoforward.
        simpl. cases_isTrue as Ht; rew_logic in Ht; tryfalse.
        auto.
    }
Qed.

Local Ltac descriptor_contains_ljs_lemma_helper := 
    let Hdc := fresh in cases_isTrue as Hdc; [idtac | eauto]; destruct Hdc; solve [false].

Lemma descriptor_contains_ljs_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdescriptorContains [L.value_object ptr1; L.value_object ptr2]) 
        (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (descriptor_contains desc2 desc1))).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpd1 Hpd2.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_value.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv1; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_writable.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv2; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_get.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv3; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_set.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv4; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_enumerable.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv5; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    forwards_th Hx : descriptor_field_contains_ljs_lemma; try eassumption. eapply ljs_descriptor_attr_configurable.
    destruct_hyp Hx.
    cases_isTrue in * as Hiv6; repeat ljs_autoforward; try descriptor_contains_ljs_lemma_helper.
    cases_isTrue as Hdc; [eauto | idtac]. false; apply Hdc; constructor; assumption.
Qed.

(* TODO move *)
Lemma OptionSome2_Some_eq : forall T1 T2 (P : T1 -> T2 -> Prop) a1 a2,
    OptionSome2 P (Some a1) (Some a2) = P a1 a2.
Proof.
    introv. rew_logic. split; intro H.
    + inverts H. assumption.
    + constructor. assumption.
Qed.

Lemma OptionSome2_None1_eq : forall T1 T2 (P : T1 -> T2 -> Prop) oa2,
    OptionSome2 P None oa2 = False.
Proof.
    introv. rew_logic. split; intro H; tryfalse. inverts H.
Qed.

Lemma if_some_then_not_same_some_eq_lemma : forall v1 v2,
    if_some_then_not_same (Some v1) (Some v2) = ~L.same_value v1 v2.
Proof.
    introv. unfolds if_some_then_not_same. rewrite OptionSome2_Some_eq. reflexivity.
Qed.

Lemma if_some_then_not_same_none1_eq_lemma : forall v2,
    if_some_then_not_same None (Some v2) = False.
Proof.
    introv. unfolds if_some_then_not_same. rewrite OptionSome2_None1_eq. reflexivity.
Qed.

Lemma descriptor_field_not_same_lemma : forall k c st st' r ptr1 obj1 desc1 ptr2 obj2 desc2 s fu v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdescriptorFieldNotSame
        [L.value_object ptr1; L.value_object ptr2; L.value_string s]) (L.out_ter st' r) ->
    binds st ptr1 obj1 ->
    binds st ptr2 obj2 ->
    property_descriptor desc1 obj1 ->
    property_descriptor desc2 obj2 ->
    ljs_descriptor_attr s fu ->
    fu desc1 = Some v ->
    st = st' /\ r = L.res_value (L.value_bool (isTrue (if_some_then_not_same (fu desc2) (fu desc1)))).
Proof.
    introv Hlred Hbinds1 Hbinds2 Hpd1 Hpd2 Hattr EQy.
    rewrite EQy.
    lets Habinds' : ljs_descriptor_attr_read_option_lemma Hpd1 Hattr.
    rewrite EQy in Habinds'. simpl in Habinds'. erewrite read_option_binds_eq in Habinds'.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. {
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Habinds).
        forwards (x&EQx&EQattrs) : ljs_descriptor_attr_binds_lemma Habinds; try eassumption.
        rewrite EQx. subst_hyp EQattrs.
Opaque decide.
        repeat ljs_autoforward.
        simpl.
        rewrite if_some_then_not_same_some_eq_lemma.
        rewrite decide_spec. rew_refl. auto.
    } {
        forwards EQx : ljs_descriptor_attr_not_index_lemma Hidx; try eassumption.
        rewrite EQx.
        repeat ljs_autoforward.
        rewrite if_some_then_not_same_none1_eq_lemma. rew_refl. auto.
    }
Qed.

Lemma descriptor_related_lemma : forall BR ojv1 ov1 ojv2 ov2 ojv3 ov3 ob1 ob2 ob3,
    option_value_related BR ojv1 ov1 ->
    option_value_related BR ojv2 ov2 ->
    option_value_related BR ojv3 ov3 ->
    descriptor_related BR 
        (J.descriptor_intro ojv1 ob1 ojv2 ojv3 ob2 ob3) 
        (ljs_descriptor_intro ov1 ob1 ov2 ov3 ob2 ob3).
Proof.
    introv Hov1 Hov2 Hov3.
    constructor; eauto_js.
Qed.

Lemma data_descriptor_related_lemma : forall BR jv v b1 b2 b3,
    value_related BR jv v ->
    descriptor_related BR (J.descriptor_intro_data jv b1 b2 b3) (data_descriptor v b1 b2 b3).
Proof.
    introv Hvrel. unfolds J.descriptor_intro_data. unfolds data_descriptor.
    constructor; eauto_js.
Qed.

Lemma accessor_descriptor_related_lemma : forall BR jv1 v1 jv2 v2 b1 b2,
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    descriptor_related BR (J.descriptor_intro_accessor jv1 jv2 b1 b2) (accessor_descriptor v1 v2 b1 b2).
Proof.
    introv Hvrel. unfolds J.descriptor_intro_accessor. unfolds accessor_descriptor.
    constructor; eauto_js.
Qed.

Lemma default_data_descriptor_related_lemma : forall BR,
    data_descriptor_related BR J.attributes_data_default default_data_descriptor.
Proof.
    introv. unfolds J.attributes_data_default. unfolds default_data_descriptor.
    constructor; simpl; eauto_js.
Qed.

Lemma default_accessor_descriptor_related_lemma : forall BR,
    accessor_descriptor_related BR J.attributes_accessor_default default_accessor_descriptor.
Proof.
    introv. unfolds J.attributes_accessor_default. unfolds default_accessor_descriptor.
    constructor; simpl; eauto_js.
Qed.

Lemma accessor_to_data_descriptor_lemma : forall BR jacc desc,
    accessor_descriptor_related BR jacc desc ->
    data_descriptor_related BR (J.attributes_data_of_attributes_accessor jacc) (to_data_descriptor desc).
Proof.
    introv Hrel. destruct Hrel.
    unfolds J.attributes_data_of_attributes_accessor. unfolds to_data_descriptor. unfolds descriptor_update.
    rewrite <- accessor_descriptor_related_value.
    rewrite <- accessor_descriptor_related_writable.
    rewrite <- accessor_descriptor_related_enumerable.
    rewrite <- accessor_descriptor_related_configurable.
    constructor; simpl; eauto_js.
Qed.

Lemma data_to_accessor_descriptor_lemma : forall BR jdata desc,
    data_descriptor_related BR jdata desc ->
    accessor_descriptor_related BR (J.attributes_accessor_of_attributes_data jdata) (to_accessor_descriptor desc).
Proof.
    introv Hrel. destruct Hrel.
    unfolds J.attributes_accessor_of_attributes_data. unfolds to_accessor_descriptor. unfolds descriptor_update.
    rewrite <- data_descriptor_related_get.
    rewrite <- data_descriptor_related_set.
    rewrite <- data_descriptor_related_enumerable.
    rewrite <- data_descriptor_related_configurable.
    constructor; simpl; eauto_js.
Qed.

Lemma value_related_unsome_default_lemma : forall BR jv v ojv ov,
    value_related BR jv v ->
    option_value_related BR ojv ov ->
    value_related BR (unsome_default jv ojv) (unsome_default v ov).
Proof.
    introv Hvrel Hovrel.
    inverts Hovrel; eauto.
Qed.

Hint Resolve value_related_unsome_default_lemma : js_ljs.

Lemma attributes_data_update_lemma : forall BR jdata jdesc desc1 desc2,
    data_descriptor_related BR jdata desc1 ->
    descriptor_related BR jdesc desc2 ->
    data_descriptor_related BR (J.attributes_data_update jdata jdesc) (descriptor_update desc1 desc2).
Proof.
    introv Hrel1 Hrel2. destruct Hrel1. destruct Hrel2.
    destruct jdata. destruct jdesc. destruct desc1. destruct desc2.
    simpls. substs.
    inverts data_descriptor_related_value.
    constructor; simpl; eauto_js.
Qed.

Lemma attributes_accessor_update_lemma : forall BR jacc jdesc desc1 desc2,
    accessor_descriptor_related BR jacc desc1 ->
    descriptor_related BR jdesc desc2 ->
    accessor_descriptor_related BR (J.attributes_accessor_update jacc jdesc) (descriptor_update desc1 desc2).
Proof.
    introv Hrel1 Hrel2. destruct Hrel1. destruct Hrel2.
    destruct jacc. destruct jdesc. destruct desc1. destruct desc2.
    simpls. substs.
    inverts accessor_descriptor_related_get.
    inverts accessor_descriptor_related_set.
    constructor; simpl; eauto_js.
Qed.

Lemma attributes_update_lemma : forall BR jattrs jdesc desc1 desc2,
    attributes_descriptor_related BR jattrs desc1 ->
    descriptor_related BR jdesc desc2 ->
    attributes_descriptor_related BR (J.attributes_update jattrs jdesc) (descriptor_update desc1 desc2).
Proof.
    introv Hrel1 Hrel2.
    destruct Hrel1 as [Hrel1|Hrel1].
    + constructor. apply attributes_data_update_lemma; assumption.
    + constructor. apply attributes_accessor_update_lemma; assumption.
Qed.

Lemma attributes_data_of_descriptor_lemma : forall BR jdesc desc,
    descriptor_related BR jdesc desc ->
    data_descriptor_related BR (J.attributes_data_of_descriptor jdesc) (to_data_descriptor desc).
Proof.
    introv Hrel.
    apply attributes_data_update_lemma.
    apply default_data_descriptor_related_lemma. assumption.
Qed.

Lemma attributes_accessor_of_descriptor_lemma : forall BR jdesc desc,
    descriptor_related BR jdesc desc ->
    accessor_descriptor_related BR (J.attributes_accessor_of_descriptor jdesc) (to_accessor_descriptor desc).
Proof.
    introv Hrel.
    apply attributes_accessor_update_lemma.
    apply default_accessor_descriptor_related_lemma. assumption.
Qed.

Lemma descriptor_of_attributes_lemma : forall BR jattrs desc,
    attributes_descriptor_related BR jattrs desc ->
    descriptor_related BR (J.descriptor_of_attributes jattrs) desc.
Proof.
    introv Hrel.
    destruct desc.
    inverts Hrel as Hrel. {
        destruct Hrel.
        simpls. substs.
        constructor; eauto_js.
    } {
        destruct Hrel.
        simpls. substs.
        constructor; eauto_js.
    }
Qed.

Lemma descriptor_is_data_eq_lemma : forall BR jdesc desc,
    descriptor_related BR jdesc desc ->
    J.descriptor_is_data jdesc = is_data_descriptor desc.
Proof.
    introv Hrel.
    destruct jdesc. destruct desc. destruct Hrel.
    unfolds J.descriptor_is_data. unfolds is_data_descriptor.
    simpls. substs.
    rew_logic.
    asserts Eq : (forall A (a : A), (Some a <> None) = True). { 
        introv. rew_logic. split. auto. introv Ht H. tryfalse.
    }
    inverts descriptor_related_value; repeat rewrite Eq; iauto.
Qed.

Lemma descriptor_is_accessor_eq_lemma : forall BR jdesc desc,
    descriptor_related BR jdesc desc ->
    J.descriptor_is_accessor jdesc = is_accessor_descriptor desc.
Proof.
    introv Hrel.
    destruct jdesc. destruct desc. destruct Hrel.
    unfolds J.descriptor_is_accessor. unfolds is_accessor_descriptor.
    simpls. substs.
    rew_logic.
    asserts Eq : (forall A (a : A), (Some a <> None) = True). { 
        introv. rew_logic. split. auto. introv Ht H. tryfalse.
    }
    inverts descriptor_related_get; 
    inverts descriptor_related_set; repeat rewrite Eq; iauto.
Qed.

Lemma descriptor_is_generic_eq_lemma : forall BR jdesc desc,
    descriptor_related BR jdesc desc ->
    J.descriptor_is_generic jdesc = is_generic_descriptor desc.
Proof.
    introv Hrel. unfolds J.descriptor_is_generic. unfolds is_generic_descriptor.
    erewrite descriptor_is_data_eq_lemma by eassumption.
    erewrite descriptor_is_accessor_eq_lemma by eassumption.
    reflexivity.
Qed.

Hint Constructors L.same_value : js_ljs. (* TODO move *)

(* TODO move *)
Lemma same_value_eq_lemma : forall v1 v2, L.value_type v1 <> L.type_closure -> L.same_value v1 v2 = (v1 = v2).
Proof.
    introv Htype.
    rew_logic.
    split.
    introv Hsv. inverts Hsv; reflexivity.
    introv Heq. subst. destruct v2; simpls; tryfalse; eauto_js.
Qed.

(* TODO move *)
Definition heaps_bisim_bijective BR := 
    heaps_bisim_lfun_obj BR /\ heaps_bisim_lfun_env BR /\ heaps_bisim_rfun BR.

Lemma same_value_related_eq_lemma : forall BR jv1 jv2 v1 v2,
    heaps_bisim_bijective BR ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    J.same_value jv1 jv2 = L.same_value v1 v2.
Proof.
    introv Hbij Hv1 Hv2.
    destruct Hbij as (Hlfun1&Hlfun2&Hrfun).
    unfolds J.same_value.
    erewrite same_value_eq_lemma by (inverts Hv1; eauto_js).
    rew_logic. split; introv Heq; subst_hyp Heq; inverts Hv1 as Hf1; inverts Hv2 as Hf2; try reflexivity.
    + lets : Hlfun1 Hf1 Hf2. substs. reflexivity.
    + lets : Hrfun Hf1 Hf2 fact_ptr_js_obj fact_ptr_js_obj. injects. reflexivity.
Qed.

Lemma if_some_value_then_same_lemma : forall BR ojv1 ojv2 ov1 ov2,
    heaps_bisim_bijective BR ->
    option_value_related BR ojv1 ov1 ->
    option_value_related BR ojv2 ov2 ->
    J.if_some_value_then_same ojv1 ojv2 = if_some_value_then_same ov1 ov2.
Proof.
    introv Hbij Hov1 Hov2.
    inverts Hov1 as Hv; inverts Hov2 as Hv2; simpls; try reflexivity.
    eapply same_value_related_eq_lemma; eassumption.
Qed.

Lemma if_some_bool_then_same_lemma : forall ob1 ob2,
    J.if_some_bool_then_same ob1 ob2 = 
        if_some_value_then_same (LibOption.map L.value_bool ob1) (LibOption.map L.value_bool ob2).
Proof.
    introv.
    destruct ob1; destruct ob2; simpls; try reflexivity.
    erewrite same_value_eq_lemma by eauto_js.
    rew_logic. split; introv Heq. subst_hyp Heq; reflexivity. injects; reflexivity.
Qed.

Lemma descriptor_contains_eq_lemma : forall BR jdesc1 jdesc2 desc1 desc2,
    heaps_bisim_bijective BR ->
    descriptor_related BR jdesc1 desc1 ->
    descriptor_related BR jdesc2 desc2 ->
    J.descriptor_contains jdesc1 jdesc2 = descriptor_contains desc1 desc2.
Proof.
    introv Hbij Hrel1 Hrel2.
    destruct jdesc1. destruct jdesc2. destruct desc1. destruct desc2.
    inverts Hrel1. inverts Hrel2.
    simpls. substs.
    repeat erewrite if_some_value_then_same_lemma by eassumption.
    repeat rewrite if_some_bool_then_same_lemma.
    rew_logic; split; introv Hx. {
        destruct_hyp Hx. constructor; simpl; eauto_js.
    } { 
        inverts Hx. splits; eauto_js.
    }
Qed.

(* TODO move *)
Lemma OptionSome2_None2_eq : forall T1 T2 (P : T1 -> T2 -> Prop) oa1,
    OptionSome2 P oa1 None = False.
Proof.
    introv. rew_logic. split; intro H; tryfalse. inverts H.
Qed.

Lemma descriptor_enumerable_not_same_eq_lemma : forall BR jattrs jdesc desc1 desc2,
    attributes_descriptor_related BR jattrs desc1 ->
    descriptor_related BR jdesc desc2 -> 
    J.descriptor_enumerable_not_same jattrs jdesc = 
        if_some_then_not_same (ljs_descriptor_enumerable_v desc2) (ljs_descriptor_enumerable_v desc1).
Proof.
    introv Hrel1 Hrel2.
    destruct jdesc. destruct desc2.
    lets Henum : descriptor_related_enumerable Hrel2. clear Hrel2. simpl in Henum. subst ljs_descriptor_enumerable.
    unfolds ljs_descriptor_enumerable_v.
    asserts_rewrite (ljs_descriptor_enumerable desc1 = Some (J.attributes_enumerable jattrs)). {
        inverts Hrel1 as Hrel1; inverts Hrel1; symmetry; eassumption.
    }
    destruct descriptor_enumerable; unfolds J.descriptor_enumerable_not_same; simpl. {
        unfolds if_some_then_not_same. rewrites OptionSome2_Some_eq.
        erewrite same_value_eq_lemma by eauto_js.
        rew_logic. split; introv H.
        + intro He. injects. tryfalse.
        + intro He. substs. tryfalse.
    } {
        unfolds if_some_then_not_same. rewrite OptionSome2_None1_eq. reflexivity.
    }
Qed.

Lemma descriptor_value_not_same_eq_lemma : forall BR jdata jdesc desc1 desc2,
    heaps_bisim_bijective BR ->
    data_descriptor_related BR jdata desc1 ->
    descriptor_related BR jdesc desc2 -> 
    J.descriptor_value_not_same jdata jdesc = 
        if_some_then_not_same (ljs_descriptor_value desc2) (ljs_descriptor_value desc1).
Proof.
    introv Hbij Hrel1 Hrel2.
    destruct jdesc. destruct desc2.
    lets Hvalue : descriptor_related_value Hrel2. clear Hrel2. simpl in Hvalue.
    lets Hvalue2 : data_descriptor_related_value Hrel1. inverts Hvalue2 as Hvalue2.
    inverts Hvalue as Hvalue; unfolds J.descriptor_value_not_same; simpl. {
        unfolds if_some_then_not_same. rewrites OptionSome2_Some_eq.
        erewrite same_value_related_eq_lemma by eassumption. reflexivity.
    } {
        unfolds if_some_then_not_same. rewrite OptionSome2_None1_eq. reflexivity.
    }
Qed.

Lemma descriptor_get_not_same_eq_lemma : forall BR jacc jdesc desc1 desc2,
    heaps_bisim_bijective BR ->
    accessor_descriptor_related BR jacc desc1 ->
    descriptor_related BR jdesc desc2 -> 
    J.descriptor_get_not_same jacc jdesc = 
        if_some_then_not_same (ljs_descriptor_get desc2) (ljs_descriptor_get desc1).
Proof.
    introv Hbij Hrel1 Hrel2.
    destruct jdesc. destruct desc2.
    lets Hvalue : descriptor_related_get Hrel2. clear Hrel2. simpl in Hvalue.
    lets Hvalue2 : accessor_descriptor_related_get Hrel1. inverts Hvalue2 as Hvalue2.
    inverts Hvalue as Hvalue; unfolds J.descriptor_get_not_same; simpl. {
        unfolds if_some_then_not_same. rewrites OptionSome2_Some_eq.
        erewrite same_value_related_eq_lemma by eassumption. reflexivity.
    } {
        unfolds if_some_then_not_same. rewrite OptionSome2_None1_eq. reflexivity.
    }
Qed.

Lemma descriptor_set_not_same_eq_lemma : forall BR jacc jdesc desc1 desc2,
    heaps_bisim_bijective BR ->
    accessor_descriptor_related BR jacc desc1 ->
    descriptor_related BR jdesc desc2 -> 
    J.descriptor_set_not_same jacc jdesc = 
        if_some_then_not_same (ljs_descriptor_set desc2) (ljs_descriptor_set desc1).
Proof.
    introv Hbij Hrel1 Hrel2.
    destruct jdesc. destruct desc2.
    lets Hvalue : descriptor_related_set Hrel2. clear Hrel2. simpl in Hvalue.
    lets Hvalue2 : accessor_descriptor_related_set Hrel1. inverts Hvalue2 as Hvalue2.
    inverts Hvalue as Hvalue; unfolds J.descriptor_set_not_same; simpl. {
        unfolds if_some_then_not_same. rewrites OptionSome2_Some_eq.
        erewrite same_value_related_eq_lemma by eassumption. reflexivity.
    } {
        unfolds if_some_then_not_same. rewrite OptionSome2_None1_eq. reflexivity.
    }
Qed.

Lemma make_data_descriptor_lemma : forall BR k jst jc c st st' r v jv b1 b2 b3,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeDataDescriptor 
        [v; L.value_bool b1; L.value_bool b2; L.value_bool b3]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    state_invariant BR jst st' /\
    descriptor_related BR (J.descriptor_intro_data jv b1 b2 b3) (data_descriptor v b1 b2 b3) /\
    concl_ljs_new_descriptor st st' r (data_descriptor v b1 b2 b3).
Proof.
    introv Hlred Hcinv Hinv Hvrel.
    forwards Hx : make_data_descriptor_ljs_lemma Hlred.
    lets Hy : Hx.
    unfolds in Hx. destruct_hyp Hx.
    splits.
    + eapply state_invariant_store_incl_preserved; eassumption.
    + eapply data_descriptor_related_lemma; eassumption.
    + assumption.
Qed.

Lemma make_accessor_descriptor_lemma : forall BR k jst jc c st st' r v1 v2 jv1 jv2 b2 b3,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeAccessorDescriptor 
        [v1; v2; L.value_bool b2; L.value_bool b3]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    state_invariant BR jst st' /\
    descriptor_related BR (J.descriptor_intro_accessor jv1 jv2 b2 b3) (accessor_descriptor v1 v2 b2 b3) /\
    concl_ljs_new_descriptor st st' r (accessor_descriptor v1 v2 b2 b3).
Proof.
    introv Hlred Hcinv Hinv Hvrel1 Hvrel2.
    forwards Hx : make_accessor_descriptor_ljs_lemma Hlred.
    lets Hy : Hx.
    unfolds in Hx. destruct_hyp Hx.
    splits.
    + eapply state_invariant_store_incl_preserved; eassumption.
    + eapply accessor_descriptor_related_lemma; eassumption.
    + assumption.
Qed.

Lemma make_value_only_descriptor_lemma : forall BR k jst jc c st st' r v jv,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmakeValueOnlyDescriptor 
        [v]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    state_invariant BR jst st' /\
    descriptor_related BR (J.descriptor_intro (Some jv) None None None None None) 
        (ljs_descriptor_intro (Some v) None None None None None) /\
    concl_ljs_new_descriptor st st' r (ljs_descriptor_intro (Some v) None None None None None).
Proof.
    introv Hlred Hcinv Hinv Hvrel.
    forwards Hx : make_value_only_descriptor_ljs_lemma Hlred.
    lets Hy : Hx.
    unfolds in Hx. destruct_hyp Hx.
    splits.
    + eapply state_invariant_store_incl_preserved; eassumption.
    + constructor; eauto_js.
    + assumption.
Qed.

(* *** errors *)

Lemma make_native_error_lemma : forall BR k jst jc c st st' jv1 jv2 v1 v2 r,
    L.red_exprh k c st 
       (L.expr_app_2 LjsInitEnv.privMakeNativeError [v1; v2]) 
       (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    object_or_null v1 ->
    (v2 = L.value_undefined \/ exists s, v2 = L.value_string s) ->
    value_related BR jv1 v1 ->
    value_related BR jv2 v2 ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_build_error jv1 jv2) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hcinv Hinv Hon Hv Hvrel1 Hvrel2. 
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    repeat ljs_autoforward. {
        inverts Hvrel2.
        jauto_js 25.
    }
    (* has message *)
    inv_ljs;
    binds_inv. (* TODO *) simpls. false. rewrite binds_empty_eq in H8. eauto.
    repeat ljs_autoforward.
    inv_ljs; binds_inv. 
    repeat ljs_autoforward.
    rew_bag_simpl. 
    simpls.
    binds_inv.
    inverts Hvrel2.
    unfold_concl. jauto_set_slim. (* TODO automation? *)
    + eauto_js 15.
    + eauto_js.
    + eapply state_invariant_next_fresh_commute_object_preserved. rew_bag_simpl.
      eapply state_invariant_new_object_preserved; eauto_js 27.
    + eauto_js 7.
    + eauto_js 8.
    + simpls. false. prove_bag 8.
Qed.

Lemma priv_js_error_lemma : forall k c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privJSError [v]) (L.out_ter st' r) ->
    exists obj,
    r = L.res_value (L.value_object (fresh st)) /\
    st' = st \(fresh st := obj) /\
    js_exn_object obj v.
Proof.
    introv Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    repeat ljs_autoforward.
    jauto_js.
Qed.

Lemma native_error_lemma : forall BR k jst jc c st st' jne ptr v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privNativeError [L.value_object ptr; v]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) -> (* TODO error messages in jscert *)
    fact_js_obj (J.object_loc_prealloc (J.prealloc_native_error_proto jne)) ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error jne) (fun _ => False).
Proof.
    introv Hlred Hcinv Hinv Hv Hbr.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct_hyp Hv;
    (forwards_th : make_native_error_lemma; [eauto_js | eauto | idtac]);
    destr_concl; try ljs_handle_abort. { (* no error message *)
        res_related_invert.
        repeat inv_fwd_ljs.
        forwards_th Hy : priv_js_error_lemma. destruct_hyp Hy.
        repeat inv_fwd_ljs.
        resvalue_related_invert.
        jauto_js 8.
    }
    skip. (* TODO overspecification in jscert - https://github.com/resource-reasoning/jscert_dev/issues/14 *)
    skip.
Qed.

Lemma type_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privTypeError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_type) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma reference_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privReferenceError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_ref) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma syntax_error_lemma : forall BR k jst jc c st st' v r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privSyntaxError [v]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_syntax) (fun _ => False).
Proof.
    introv Hlred Hv Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma unbound_id_lemma : forall BR k jst jc c st st' s r,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privUnboundId [L.value_string s]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_error J.native_error_ref) (fun _ => False).
Proof.
    introv Hlred Hcinv Hinv.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat ljs_autoforward.
    forwards_th Hx : reference_error_lemma; try eassumption.
    jauto_js.
Qed.

Lemma native_error_or_void_lemma : forall BR k jst jc c st st' jne ptr v r b,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privNativeErrorOr [L.value_object ptr; v; L.value_empty; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) -> (* TODO error messages in jscert *)
    fact_js_obj (J.object_loc_prealloc (J.prealloc_native_error_proto jne)) ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_error_or_void b jne) 
        (fun jrv => !b /\ jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hv Hbr.
    ljs_invert_apply.
    repeat ljs_autoforward.
    destruct b. { (* strict *)
        repeat ljs_autoforward.
        forwards_th : native_error_lemma; try eassumption.
        destr_concl; tryfalse.
        ljs_handle_abort.
    } { (* non-strict *)
        repeat ljs_autoforward.
        jauto_js.
    }
Qed.

Lemma type_error_or_void_lemma : forall BR k jst jc c st st' v r b,
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privTypeErrorOr [v; L.value_empty; L.value_bool b]) 
        (L.out_ter st' r) ->
    (v = L.value_undefined \/ exists s, v = L.value_string s) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_error_or_void b J.native_error_type) 
        (fun jrv => !b /\ jrv = J.resvalue_empty).
Proof.
    introv Hlred Hv Hcinv Hinv.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : native_error_or_void_lemma; try eassumption.
    jauto_js.
Qed.

(* ** Accessing properties *)

Lemma object_method_builtin_default_lemma : forall T jst jptr jobj M (D : T) R,
    binds jst jptr jobj ->
    builtin_method_related D R (M jobj) None ->
    J.object_method M jst jptr D.
Proof.
    introv Hjbinds Hmeth.
    inverts Hmeth.
    unfolds. jauto_js.
Qed.

Lemma object_method_builtin_exotic_lemma : forall T jst jptr jobj M (D : T) R v,
    binds jst jptr jobj ->
    builtin_method_related D R (M jobj) (Some v) ->
    J.object_method M jst jptr (M jobj) /\
    R (M jobj) v.
Proof.
    introv Hjbinds Hmeth.
    inverts Hmeth.
    unfolds J.object_method.
    jauto_js.
Qed.

Lemma object_method_has_property_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_has_prop_ jst jptr J.builtin_has_prop_default.
Proof.
    introv Hinv Hf.
    lets Hjbinds : heaps_bisim_consistent_lnoghost_obj (state_invariant_heaps_bisim_consistent Hinv) Hf.
    rewrite index_binds_eq in Hjbinds.
    destruct Hjbinds as (jobj&Hjbinds).
    unfolds. exists jobj.
    destruct (J.object_has_prop_ jobj).
    jauto.
Qed.

Lemma object_method_get_property_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_get_prop_ jst jptr J.builtin_get_prop_default.
Proof.
    introv Hinv Hf.
    lets Hjbinds : heaps_bisim_consistent_lnoghost_obj (state_invariant_heaps_bisim_consistent Hinv) Hf.
    rewrite index_binds_eq in Hjbinds.
    destruct Hjbinds as (jobj&Hjbinds).
    unfolds. exists jobj.
    destruct (J.object_get_prop_ jobj).
    jauto.
Qed.

Lemma object_method_put_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_put_ jst jptr J.builtin_put_default.
Proof.
    introv Hinv Hf.
    lets Hjbinds : heaps_bisim_consistent_lnoghost_obj (state_invariant_heaps_bisim_consistent Hinv) Hf.
    rewrite index_binds_eq in Hjbinds.
    destruct Hjbinds as (jobj&Hjbinds).
    unfolds. exists jobj.
    destruct (J.object_put_ jobj).
    jauto.
Qed.

Lemma object_method_get_own_property_default_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_internal obj) "getprop" ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_get_own_prop (object_related_prim Horel).
    erewrite read_option_not_index_inv in Hbrel by eassumption.
    applys object_method_builtin_default_lemma; eassumption.
Qed.

Lemma object_method_get_own_property_exotic_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    index (L.object_internal obj) "getprop" ->
    exists jx x,
    exotic_get_own_prop_related jx x /\
    binds (L.object_internal obj) "getprop" x /\
    J.object_method J.object_get_own_prop_ jst jptr jx.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_get_own_prop (object_related_prim Horel).
    rewrite index_binds_eq in Hidx. destruct_hyp Hidx.
    erewrite read_option_binds_inv in Hbrel by eassumption.
    forwards Hex : object_method_builtin_exotic_lemma; try eassumption.
    destruct_hyp Hex. jauto_js.
Qed.

Lemma object_method_get_default_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_internal obj) "get" ->
    J.object_method J.object_get_ jst jptr J.builtin_get_default.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_get (object_related_prim Horel).
    erewrite read_option_not_index_inv in Hbrel by eassumption.
    applys object_method_builtin_default_lemma; eassumption.
Qed.

Lemma object_method_get_exotic_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    index (L.object_internal obj) "get" ->
    exists jx x,
    exotic_get_related jx x /\
    binds (L.object_internal obj) "get" x /\
    J.object_method J.object_get_ jst jptr jx.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_get (object_related_prim Horel).
    rewrite index_binds_eq in Hidx. destruct_hyp Hidx.
    erewrite read_option_binds_inv in Hbrel by eassumption.
    forwards Hex : object_method_builtin_exotic_lemma; try eassumption.
    destruct_hyp Hex. jauto_js.
Qed.

Lemma object_method_define_own_prop_default_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_internal obj) "defineprop" ->
    J.object_method J.object_define_own_prop_ jst jptr J.builtin_define_own_prop_default.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_define_own_prop (object_related_prim Horel).
    erewrite read_option_not_index_inv in Hbrel by eassumption.
    applys object_method_builtin_default_lemma; eassumption.
Qed.

Lemma object_method_define_own_prop_exotic_lemma : forall BR jst st jptr ptr obj,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    index (L.object_internal obj) "defineprop" ->
    exists jx x,
    exotic_define_own_prop_related jx x /\
    binds (L.object_internal obj) "defineprop" x /\
    J.object_method J.object_define_own_prop_ jst jptr jx.
Proof.
    introv Hinv Hf Hbinds Hidx.
    lets (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hbrel : object_prim_related_builtin_define_own_prop (object_related_prim Horel).
    rewrite index_binds_eq in Hidx. destruct_hyp Hidx.
    erewrite read_option_binds_inv in Hbrel by eassumption.
    forwards Hex : object_method_builtin_exotic_lemma; try eassumption.
    destruct_hyp Hex. jauto_js.
Qed.

(** *** ToObject *)

Ltac invert_stx_eq :=
    match goal with
    | H : L.stx_eq _ _  |- _ => inverts H
    end. 

(* TODO move *)
Ltac decide_stx_eq := 
    match goal with
    | H : context[decide (L.stx_eq ?v1 ?v2)] |- _ => 
        let EQ := fresh "EQ" in
        case_if_on (decide (L.stx_eq v1 v2)) as EQ;
        [applys_to EQ eq_true_r; rew_refl in EQ; try solve [inverts EQ]
        |applys_to EQ eq_false_r; rew_refl in EQ; try solve [false; apply EQ; jauto_js]]
    end.

(* TODO move *)
Hint Extern 3 (object_or_null _) => eapply object_or_null_object : js_ljs.

Lemma red_spec_to_object_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToObject J.spec_to_object
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply. clear Hcinv.
    repeat (ljs_autoforward || decide_stx_eq). { (* null *)
        destruct Hvrel; invert_stx_eq.
        forwards_th Hx : type_error_lemma. iauto. 
        destr_concl; tryfalse.
        jauto_js.
    } { (* undefined *)
        destruct Hvrel; invert_stx_eq.
        forwards_th Hx : type_error_lemma. iauto. 
        destr_concl; tryfalse.
        jauto_js.
    } { (* object *)
        destruct Hvrel; invert_stx_eq.
        jauto_js.
    } { (* string *)
        destruct Hvrel; invert_stx_eq.
        ljs_invert_apply.
        repeat ljs_autoforward.
        skip. (* TODO better handling of objects *)
    } { (* number *)
        destruct Hvrel; invert_stx_eq.
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js 35.
    } { (* boolean *)
        destruct Hvrel; invert_stx_eq.
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js 35.
    } { (* impossible *)
        destruct Hvrel; false; eauto_js.
    }
Qed.

(* ** Handling contexts *)

(* TODO move *)
Lemma decl_env_record_related_empty : forall BR,
    decl_env_record_vars_related BR \{} \{}.
Proof.
    introv. unfolds.
    intro s.
    left. splits; prove_bag.
Qed.

Hint Resolve decl_env_record_related_empty : js_ljs.

(* *** Creating new environment records *)

Lemma new_env_record_decl_lemma : forall BR k c st jlenv v st' r,
    lexical_env_related BR jlenv v ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    binds (L.object_internal obj) "parent" v /\
    env_record_related BR (J.env_record_decl J.decl_env_record_empty) obj.
Proof.
    introv Hlrel Hlred.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    reflexivity.
    reflexivity.
    prove_bag.
    econstructor; jauto_js.
Qed.

Lemma new_env_record_object_lemma : forall BR k c st jlenv v jptr ptr b st' r,
    lexical_env_related BR jlenv v ->
    value_related BR (J.value_object jptr) (L.value_object ptr) ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewObjEnvRec 
        [v; L.value_object ptr; L.value_bool b]) (L.out_ter st' r) ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    binds (L.object_internal obj) "parent" v /\
    env_record_related BR (J.env_record_object jptr b) obj.
Proof.
    introv Hlrel Hvrel Hlred.
    inverts Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    eexists.
    splits.
    reflexivity.
    reflexivity.
    prove_bag 10.
    econstructor.
    econstructor;
    prove_bag 10.
Qed.

(* *** State invariant for new environment records *)

Lemma only_state_invariant_new_env_record_decl_lemma : forall BR k jst jlenv c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    lexical_env_related BR jlenv v ->
    state_invariant BR jst st ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hlerel Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). { jauto_js. }
    forwards_th Hx : new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists. splits; try reflexivity.
    + eauto_js.
    + eauto_js 8.
Qed.

Lemma state_invariant_new_env_record_decl_lemma : forall BR k jst jc c st v st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v]) (L.out_ter st' r) ->
    binds c "$context" v ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)) /\
    context_invariant BR'
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))).
Proof.
    introv Hlred Hbinds Hcinv Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). jauto_js.
    lets Hlerel : context_invariant_lexical_env_related Hcinv Hbinds.
    forwards_th Hx : only_state_invariant_new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists. splits; try reflexivity; try assumption.
    eapply context_invariant_push_context_lemma.
    + eapply lexical_env_related_cons; eauto_js 15.
    + eauto_js 10.
    + eauto_js 10.
Qed.

Lemma state_invariant_new_env_record_object_lemma : forall BR k jst jc c st v jptr ptr b st' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privnewObjEnvRec 
        [v; L.value_object ptr; L.value_bool b]) (L.out_ter st' r) ->
    binds c "$context" v ->
    value_related BR (J.value_object jptr) (L.value_object ptr) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists obj,
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    state_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR) 
        (J.state_next_fresh (jst \(fresh jst := J.env_record_object jptr b))) 
        (st \(fresh st := obj)) /\
    context_invariant (\{fact_ctx_parent (fresh st) v} \u \{fact_js_env (fresh jst) (fresh st)} \u BR)
        (J.execution_ctx_with_lex jc (fresh jst::J.execution_ctx_lexical_env jc)) 
        (c \("$context" := L.value_object (fresh st))).
Proof.
    introv Hlred Hbinds Hvrel Hcinv Hinv.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). 
        prove_bag 10.
    asserts Hlerel : (lexical_env_related BR (J.execution_ctx_lexical_env jc) v).
    solve [eauto using context_invariant_lexical_env_related].
    forwards_th Hx : new_env_record_object_lemma. eauto_js.
    destruct_hyp Hx.
    eexists. splits; try reflexivity. (* TODO *)
    jauto_js 7. 
    eapply context_invariant_push_context_lemma.
    eapply lexical_env_related_cons; eauto_js 10. eauto_js 10.
    eauto_js.
Qed. 

(* ** More environment record manipulations TODO doc *)

(* TODO move *)
Lemma env_record_related_lookup_lemma : forall BR jeptr ptr jst st obj,
     state_invariant BR jst st ->
     fact_js_env jeptr ptr \in BR ->
     binds st ptr obj ->
     exists jer,
     binds jst jeptr jer /\
     env_record_related BR jer obj.
Proof.
    introv Hinv Hbs Hbinds.
    lets Hjindex : heaps_bisim_consistent_lnoghost_env (state_invariant_heaps_bisim_consistent Hinv) Hbs.
    lets (jer&Hjbinds) : index_binds Hjindex.
    lets Herel : heaps_bisim_consistent_bisim_env (state_invariant_heaps_bisim_consistent Hinv) Hbs Hbinds.
        eassumption.
    jauto.
Qed.

(* TODO move *)
Lemma stx_eq_string_eq_lemma : forall s1 s2,
    L.stx_eq (L.value_string s1) (L.value_string s2) = (s1 = s2).
Proof.
    introv. rew_logic. splits; introv Hx. {
       inverts Hx. reflexivity.
    } {
       substs. eauto_js.
    }
Qed.

(* TODO move *)
Lemma stx_eq_object_eq_lemma : forall ptr1 ptr2,
    L.stx_eq (L.value_object ptr1) (L.value_object ptr2) = (ptr1 = ptr2).
Proof.
    introv. rew_logic. splits; introv Hx. {
       inverts Hx. reflexivity.
    } {
       substs. eauto_js.
    }
Qed.

(* TODO move *)
Lemma stx_eq_empty_eq_lemma : forall v, L.stx_eq v L.value_empty = (v = L.value_empty).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* TODO move *)
Lemma stx_eq_null_eq_lemma : forall v, L.stx_eq v L.value_null = (v = L.value_null).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* TODO move *)
Lemma stx_eq_undefined_eq_lemma : forall v, L.stx_eq v L.value_undefined = (v = L.value_undefined).
Proof.
    introv. rew_logic. split; introv H. { inverts H. reflexivity. } { substs. eauto_js. }
Qed.

(* TODO move *)
Lemma object_property_not_index_lemma : forall BR jst st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_properties obj) s ->
    J.object_property jst jptr s None.
Proof.
    introv Hinv Hf Hbinds Hnindex.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hoprel : object_related_properties Horel s.
    destruct_hyp Hoprel; [idtac|false; prove_bag].
    exists (J.object_properties_ jobj). split. 
    + unfolds. jauto_js.
    + rew_heap_to_libbag. erewrite read_option_not_index_inv by eassumption. reflexivity.
Qed.

(* TODO move *)
Lemma object_property_index_lemma : forall BR jst st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    index (L.object_properties obj) s ->
    exists attrs jattrs,
    J.object_property jst jptr s (Some jattrs) /\
    binds (L.object_properties obj) s attrs /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hindex.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hoprel : object_related_properties Horel s.
    destruct_hyp Hoprel; [false; prove_bag|idtac].
    exists attrs jattrs.
    splits.
    + exists (J.object_properties_ jobj). split.
      - unfolds. jauto_js.
      - rew_heap_to_libbag. erewrite read_option_binds_inv by eassumption. reflexivity.
    + assumption.
    + assumption.
Qed.

(* TODO move *)
Lemma object_property_binds_lemma : forall BR jst st jptr ptr obj s attrs,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_properties obj) s attrs ->
    exists jattrs,
    J.object_property jst jptr s (Some jattrs) /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hbindsa.
    asserts Hindex : (index (L.object_properties obj) s). prove_bag.
    lets Hx : object_property_index_lemma Hinv Hf Hbinds Hindex.
    destruct_hyp Hx.
    binds_determine.
    jauto.
Qed.

Lemma object_method_get_own_property_default_not_index_lemma : forall BR jst jc st jptr ptr obj s,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    ~index (L.object_properties obj) s ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default ->
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) (J.ret jst J.full_descriptor_undef).
Proof.
    introv Hinv Hf Hbinds Hnindex Hmeth.
    lets Hx : object_property_not_index_lemma Hinv Hf Hbinds Hnindex.
    eauto_js.
Qed.

Lemma object_method_get_own_property_default_binds_lemma : forall BR jst jc st jptr ptr obj s attrs,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_properties obj) s attrs ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default ->
    exists jattrs,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) (J.ret jst (J.full_descriptor_some jattrs)) /\
    attributes_related BR jattrs attrs.
Proof.
    introv Hinv Hf Hbinds Hbinds2 Hmeth.
    lets Hx : object_property_binds_lemma Hinv Hf Hbinds Hbinds2.
    destruct_hyp Hx.
    jauto_js.
Qed.

Lemma object_related_proto_null_lemma : forall BR jobj obj,
    object_related BR jobj obj ->
    L.object_proto obj = L.value_null ->
    J.object_proto_ jobj = J.value_prim J.prim_null.
Proof.
    introv Horel Heq.
    lets Hvrel : object_prim_related_prototype (object_related_prim Horel).
    rewrite Heq in Hvrel.
    inverts Hvrel. reflexivity.
Qed.

Lemma object_proto_null_lemma : forall BR jst st ptr obj jptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_proto obj = L.value_null ->
    J.object_proto jst jptr (J.value_prim J.prim_null).
Proof.
    introv Hinv Hf Hbinds Heq.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hjeq : object_related_proto_null_lemma Horel Heq.
    unfolds. jauto.
Qed.

Lemma object_related_proto_not_null_lemma : forall BR jobj obj,
    object_related BR jobj obj ->
    L.object_proto obj <> L.value_null ->
    exists jptr ptr,
    L.object_proto obj = L.value_object ptr /\
    J.object_proto_ jobj = J.value_object jptr /\
    fact_js_obj jptr ptr \in BR.
Proof.
    introv Horel Heq.
    lets Hvrel : object_prim_related_prototype (object_related_prim Horel).
    lets Hobj : object_prim_related_prototype_object_or_null (object_related_prim Horel).
    inverts Hobj as Heq1; tryfalse.
    rewrite <- Heq1 in Hvrel.
    inverts Hvrel. jauto.
Qed.

Lemma object_proto_not_null_lemma : forall BR jst st ptr obj jptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_proto obj <> L.value_null ->
    exists jptr' ptr',
    L.object_proto obj = L.value_object ptr' /\
    J.object_proto jst jptr (J.value_object jptr') /\
    fact_js_obj jptr' ptr' \in BR.
Proof.
    introv Hinv Hf Hbinds Heq.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hjeq : object_related_proto_not_null_lemma Horel Heq.
    destruct_hyp Hjeq.
    unfolds J.object_proto.
    jauto.
Qed.

Lemma object_extensible_lemma : forall BR jst st ptr obj jptr b,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_extensible obj = b ->
    J.object_extensible jst jptr b.
Proof.
    introv Hinv Hf Hbinds Heq.
    forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf Hbinds.
    lets Hpeq : object_prim_related_extensible (object_related_prim Horel).
    unfolds. jauto.
Qed.

Lemma get_own_property_default_lemma : forall BR k jst jc c st st' r jptr ptr s v_d v_a v_u,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetOwnPropertyDefault 
        [L.value_object ptr; L.value_string s; v_d; v_a; v_u]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_get_own_prop_ jst jptr J.builtin_get_own_prop_default ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jfd st'' c' k', 
      jsr = J.specret_val jst'' jfd /\
      ((jfd = J.full_descriptor_undef /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_u []) (L.out_ter st' r)) /\
        state_invariant BR' jst'' st'' \/
       (exists jv1 v1 b1 b2 b3, 
        jfd = J.full_descriptor_some (J.attributes_data_of (J.attributes_data_intro jv1 b1 b2 b3)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_d [v1; L.value_bool b1; L.value_bool b2; L.value_bool b3]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1) \/
       (exists v1 jv1 v2 jv2 b1 b2, 
        jfd = J.full_descriptor_some (J.attributes_accessor_of (J.attributes_accessor_intro jv1 jv2 b1 b2)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_a [v1; v2; L.value_bool b1; L.value_bool b2]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1 /\ value_related BR' jv2 v2 /\ 
        object_or_undefined v1 /\ object_or_undefined v2)) /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k /\ jst'' = jst)  ). 
Proof.
    introv Hlred Hcinv Hinv Hf Hmeth.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* found *)
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Hbinds).
        forwards Hgop : object_method_get_own_property_default_binds_lemma; try eassumption.
        destruct_hyp Hgop.
        repeat ljs_autoforward.
        cases_decide as Hacc. { (* is accessor *)
            inverts Hacc.
            inverts Hgop1 as Harel. inverts Harel.
            repeat ljs_autoforward. simpls.
            jauto_set_slim; eauto_js 20. eauto_js. (* TODO *)
        } { (* is data *)
            inverts Hgop1 as Harel; try solve [false; apply Hacc; eapply L.is_accessor_accessor]. inverts Harel.
            repeat ljs_autoforward. simpls.
            jauto_set_slim; eauto_js 20. eauto_js. (* TODO *)
        }
    } { (* not found *)
        forwards Hgop : object_method_get_own_property_default_not_index_lemma; try eassumption.
        repeat ljs_autoforward.
        jauto_set_slim; eauto_js 20. eauto_js. (* TODO *)
    }
Qed.

Lemma get_own_property_lemma : forall BR k jst jc c st st' r jptr ptr s v_d v_a v_u,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetOwnProperty 
        [L.value_object ptr; L.value_string s; v_d; v_a; v_u]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jfd st'' c' k', 
      jsr = J.specret_val jst'' jfd /\
      ((jfd = J.full_descriptor_undef /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_u []) (L.out_ter st' r)) /\
        state_invariant BR' jst'' st'' \/
       (exists jv1 v1 b1 b2 b3, 
        jfd = J.full_descriptor_some (J.attributes_data_of (J.attributes_data_intro jv1 b1 b2 b3)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_d [v1; L.value_bool b1; L.value_bool b2; L.value_bool b3]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1) \/
       (exists v1 jv1 v2 jv2 b1 b2, 
        jfd = J.full_descriptor_some (J.attributes_accessor_of (J.attributes_accessor_intro jv1 jv2 b1 b2)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_a [v1; v2; L.value_bool b1; L.value_bool b2]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1 /\ value_related BR' jv2 v2 /\ 
        object_or_undefined v1 /\ object_or_undefined v2)) /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k /\ jst'' = jst)  ). 
Proof.
    introv Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* exotic object *)
        skip. (* TODO *)
    } { (* default impl *)
        repeat ljs_autoforward.
        forwards Hmeth : object_method_get_own_property_default_lemma; try eassumption.
        forwards_th Hx : get_own_property_default_lemma; try eassumption.
        destruct_hyp Hx; jauto_js.
    }
Qed.

(* TODO: factorize the theorem statement *)
Lemma get_property_lemma : forall k BR jst jc c st st' r jptr ptr s v_d v_a v_u,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetProperty 
        [L.value_object ptr; L.value_string s; v_d; v_a; v_u]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jfd st'' c' k', 
      jsr = J.specret_val jst'' jfd /\
      ((jfd = J.full_descriptor_undef /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_u []) (L.out_ter st' r)) /\
        state_invariant BR' jst'' st'' \/
       (exists jv1 v1 b1 b2 b3, 
        jfd = J.full_descriptor_some (J.attributes_data_of (J.attributes_data_intro jv1 b1 b2 b3)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_d [v1; L.value_bool b1; L.value_bool b2; L.value_bool b3]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1) \/
       (exists v1 jv1 v2 jv2 b1 b2, 
        jfd = J.full_descriptor_some (J.attributes_accessor_of (J.attributes_accessor_intro jv1 jv2 b1 b2)) /\
        L.red_exprh k' c' st'' (L.expr_app_2 v_a [v1; v2; L.value_bool b1; L.value_bool b2]) 
            (L.out_ter st' r) /\
        state_invariant BR' jst'' st'' /\
        value_related BR' jv1 v1 /\ value_related BR' jv2 v2 /\
        object_or_undefined v1 /\ object_or_undefined v2)) /\
      context_invariant BR' jc c' /\ BR \c BR' /\
      k' < k /\ jst'' = jst) ). (*\/ (* no state changes by the lookup - OK in ES5 *)
      exists jr, 
      jsr = @J.specret_out J.full_descriptor (J.out_ter jst'' jr) /\
      J.abort (J.out_ter jst'' jr) /\ J.res_type jr = J.restype_throw /\ 
      state_invariant BR' jst'' st' /\
      res_related BR' jst'' st' jr r /\ BR \c BR'). *)
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    forwards : object_method_get_property_lemma; try eassumption.
    repeat ljs_autoforward.
    forwards_th Hx : get_own_property_lemma. eassumption.
    destruct_hyp Hx; try ljs_handle_abort. { (* own property undefined, recurse *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        cases_decide as Hprnul; rewrite stx_eq_null_eq_lemma in Hprnul. { (* prototype is null *)
            forwards Hjproto : object_proto_null_lemma; try prove_bag.
            repeat ljs_autoforward.
            jauto_js 30.
        } { (* prototype not null *)
            forwards Hjproto : object_proto_not_null_lemma; try prove_bag.
            destruct Hjproto as (jptr'&ptr'&Heq1&Heq2&Hf').
            repeat ljs_autoforward.
            unfolds L.object_proto. rewrite Heq1 in *.
            forwards_th Hx : IH. math. prove_bag.
            destruct_hyp Hx; try ljs_handle_abort;
            jauto_set_slim; eauto_js 20. (* TODO *)
        }
    } { (* found data *)
        jauto_set_slim; eauto_js 20. (* TODO *)
    } { (* found accessor *)
        jauto_set_slim; eauto_js 20. (* TODO *)
    }
Qed.

(* TODO move *)
Lemma js_attributes_acccessor_of_descriptor_lemma : forall jv1 jv2 b1 b2,
    J.attributes_accessor_of_descriptor (J.descriptor_intro_accessor jv1 jv2 b1 b2) =
    J.attributes_accessor_intro jv1 jv2 b1 b2.
Proof.
    introv. reflexivity.
Qed.

(* TODO move *)
Lemma js_attributes_data_of_descriptor_lemma : forall jv1 b1 b2 b3,
    J.attributes_data_of_descriptor (J.descriptor_intro_data jv1 b1 b2 b3) =
    J.attributes_data_intro jv1 b1 b2 b3.
Proof.
    introv. reflexivity.
Qed.

Lemma get_own_property_descriptor_lemma : forall BR k jst jc c st st' r jptr ptr s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetOwnPropertyDescriptor
        [L.value_object ptr; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    exists BR' jst'' jsr,
    J.red_spec jst jc (J.spec_object_get_own_prop jptr s) jsr /\
    js_specret_state jsr jst'' /\
    ((exists jattrs desc ptr1 obj,
      jsr = J.specret_val jst'' (J.full_descriptor_some jattrs) /\
      r = L.res_value (L.value_object ptr1) /\
      binds st' ptr1 obj /\
      property_descriptor desc obj /\
      attributes_descriptor_related BR' jattrs desc) \/
     (jsr = J.specret_val jst'' J.full_descriptor_undef /\
      r = L.res_value L.value_undefined)) /\
    jst'' = jst /\
    BR \c BR'.
Proof.
    introv Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : get_own_property_lemma; try eassumption.
    destruct_hyp Hx. { (* no field *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    } { (* data *)
        forwards_th Hy : make_data_descriptor_lemma.
        destruct Hy as (?&?&Hy).
        unfolds in Hy. destruct_hyp Hy. (* TODO *)
        forwards Hattr : attributes_data_of_descriptor_lemma. eassumption.
        rewrite js_attributes_data_of_descriptor_lemma in Hattr.
        apply attributes_descriptor_related_data in Hattr.
        jauto_js.
    } { (* accessor *)
        repeat ljs_autoforward.
        forwards_th Hy : make_accessor_descriptor_lemma.
        destruct Hy as (?&?&Hy).
        unfolds in Hy. destruct_hyp Hy. (* TODO *)
        forwards Hattr : attributes_accessor_of_descriptor_lemma. eassumption.
        rewrite js_attributes_acccessor_of_descriptor_lemma in Hattr.
        apply attributes_descriptor_related_accessor in Hattr.
        jauto_js.
    }
Qed.

Lemma has_property_lemma : forall k BR jst jc c st st' r jptr ptr s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privHasProperty [L.value_object ptr; L.value_string s]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_has_prop jptr s) 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards : object_method_has_property_lemma; try eassumption.
    forwards_th Hx : get_property_lemma; try eassumption.
    destruct_hyp Hx. { (* not found *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    } { (* found data *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    } { (* found accessor *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    }
Qed.

(** *** defineOwnProperty *)

Lemma define_own_property_default_lemma : forall BR k jst jc c st st' r ptr s ptr' b jptr jdesc desc obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdefineOwnPropertyDefault 
        [L.value_object ptr; L.value_string s; L.value_object ptr'; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr' obj ->
    property_descriptor desc obj ->
    descriptor_related BR jdesc desc ->
    concl_ext_expr_value BR jst jc c st st' r
        (J.spec_object_define_own_prop_1 J.builtin_define_own_prop_default jptr s jdesc b) (fun _ => True).
Proof.
    introv Hlred Hcinv Hinv Hf Hbinds Hpdesc Hdrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : get_own_property_descriptor_lemma. eassumption.
    destruct_hyp Hx. { (* field exists *)
        repeat ljs_autoforward.
        skip.
    } { (* field not found *)
        repeat ljs_autoforward.
        skip.
    }
Qed.

Lemma define_own_property_lemma : forall BR k jst jc c st st' r ptr s ptr' b jptr jdesc desc obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privdefineOwnProperty 
        [L.value_object ptr; L.value_string s; L.value_object ptr'; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr' obj ->
    property_descriptor desc obj ->
    descriptor_related BR jdesc desc ->
    concl_ext_expr_value BR jst jc c st st' r
        (J.spec_object_define_own_prop jptr s jdesc b) (fun _ => True).
Proof.
    introv Hlred Hcinv Hinv Hf Hbinds Hpdesc Hdrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* exotic *)
        skip. (* TODO *)
    } { (* default *)
        repeat ljs_autoforward.
        forwards : object_method_define_own_prop_default_lemma; try eassumption.
        forwards_th : define_own_property_default_lemma; try eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js.
    }
Qed.

Lemma attributes_related_configurable_eq_lemma : forall BR attrs jattrs,
    attributes_related BR jattrs attrs ->    
    L.attributes_configurable attrs = J.attributes_configurable jattrs.
Proof.
    introv Hrel.
    inverts Hrel as Hrel; inverts Hrel; trivial.
Qed.

(* TODO move to LibBagExt *)
Lemma js_object_rem_property_lemma : forall jst jptr jobj s,
    binds jst jptr jobj ->
    JsPreliminary.object_rem_property jst jptr s
        (jst \(jptr := J.object_map_properties jobj (fun jprops => J.Heap.rem jprops s))).
Proof.
    introv Hbinds. unfolds. unfolds. jauto.
Qed.

(* TODO move to Common *)
Hint Resolve js_object_rem_property_lemma : js_ljs.

(* TODO move to common *)
Lemma object_properties_related_delete_lemma : forall BR jprops props s,
    object_properties_related BR jprops props ->
    object_properties_related BR (J.Heap.rem jprops s) (props \-- s). (* TODO heap delete in libbag *)
Proof.
    introv Hrel. intro s'.
    destruct (classic (s' = s)) as [Heq|Heq]. { (* equal *)
        skip. (* TODO *)
    } { (* different *)
        specializes Hrel s'.
        destruct_hyp Hrel.
        skip. skip. (* TODO *)
    }
Qed.

Hint Resolve object_properties_related_delete_lemma : js_ljs.

(* TODO move to common *)
Lemma object_prim_related_delete_lemma : forall BR jobj obj s,
    object_prim_related BR jobj obj ->
    object_prim_related BR jobj (L.delete_object_property obj s).
Proof.
    introv Hrel.
    destruct obj. simpls.
    inverts Hrel. constructor; assumption.
Qed.

Hint Resolve object_prim_related_delete_lemma : js_ljs.

(* TODO move to common *)
Lemma object_related_delete_lemma : forall BR jobj obj s,
    object_related BR jobj obj ->
    object_related BR
        (J.object_map_properties jobj (fun jprops => J.Heap.rem jprops s))
        (L.delete_object_property obj s).
Proof.
    introv Horel. destruct Horel.
    destruct obj.
    apply object_related_map_properties_preserved. 
    + eauto_js.
    + simpl. eauto_js.
Qed.

Hint Resolve object_related_delete_lemma : js_ljs.

Lemma delete_lemma : forall BR k jst jc c st st' r jptr ptr s b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDelete [L.value_object ptr; L.value_string s; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_delete_1 J.builtin_delete_default jptr s b) 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    forwards : object_method_get_own_property_default_lemma; try eassumption. skip. skip.  (* TODO FIX!!! *)
Opaque decide. (* TODO *)
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* field found *)
        rewrite index_binds_eq in Hidx. destruct Hidx as (attrs&Hbinds).
        forwards Hgop : object_method_get_own_property_default_binds_lemma; try eassumption.
        destruct_hyp Hgop.
        repeat ljs_autoforward.
        sets_eq b1 : (L.attributes_configurable attrs).
        destruct b1; symmetry in EQb1;
        erewrite attributes_related_configurable_eq_lemma in EQb1 by eassumption. { (* configurable *)
            forwards (jobj&Hjbinds&Horel) : state_invariant_bisim_obj_lemma Hinv Hf. eassumption.
            repeat ljs_autoforward.
            jauto_js 8.
        } { (* unconfigurable *)
            repeat ljs_autoforward.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th : type_error_lemma. eauto.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* non-strict *)
                repeat ljs_autoforward.
                jauto_js.
            }
        }
    } { (* field not found *)
        forwards Hgop : object_method_get_own_property_default_not_index_lemma; try eassumption.
        repeat ljs_autoforward.
        jauto_js.
    }
Admitted. (* TODO FIX!!!*)

(* ** More environment record manipulations TODO doc *)

(* TODO move *)
Lemma decl_env_record_vars_related_index_lemma : forall BR jx x s,
    decl_env_record_vars_related BR jx x ->
    index jx s = index x s.
Proof.
    introv Hder.
    specializes Hder s.
    destruct Hder as [(Hder1&Hder2)|(?&?&?&Hder0&Hder1&Hder2)]. {
        apply prop_eq_False_back in Hder1.
        apply prop_eq_False_back in Hder2.
        rewrite Hder1. rewrite Hder2. reflexivity.
    } {
        apply index_binds_inv in Hder0.
        apply index_binds_inv in Hder1.
        rew_logic; split; auto. 
    }
Qed.

(* TODO move *)
Lemma decl_env_record_vars_related_binds_lemma : forall BR jder props s attrs,
    decl_env_record_vars_related BR jder props ->
    binds props s attrs ->
    exists jmut jv v,
    attrs = L.attributes_data_of (L.attributes_data_intro v  
            (mutability_writable jmut) true (mutability_configurable jmut)) /\
    binds jder s (jmut, jv) /\ 
    decl_env_record_var_related BR jmut jv v.
Proof.
    introv Hder Hbinds.
    specializes Hder s.
    destruct Hder as [(Hder1&Hder2)|(jmut&jv&v&Hjxbinds&Hxbinds&Hder)]. {
        false. applys Hder2. prove_bag.
    }
    binds_determine.
    jauto_js.
Qed.

(* TODO move *)
Lemma decl_env_record_var_related_empty_lemma : forall BR jmut jv,
    decl_env_record_var_related BR jmut jv L.value_empty ->
    jmut = J.mutability_uninitialized_immutable /\ jv = J.value_prim J.prim_undef.
Proof.
    introv Hvrel.
    destruct Hvrel as [(Hmut&Hvrel)|Hvrel].
    + inverts Hvrel.
    + destruct_hyp Hvrel. jauto.
Qed.

(* TODO move *)
Lemma decl_env_record_var_related_not_empty_lemma : forall BR jmut jv v,
    v <> L.value_empty ->
    decl_env_record_var_related BR jmut jv v ->
    value_related BR jv v /\ jmut <> J.mutability_uninitialized_immutable.
Proof.
    introv Hnempty Hvrel.
    destruct Hvrel as [Hvrel|Hvrel]; destruct_hyp Hvrel; tryfalse.
    auto.
Qed.

(* TODO begin big block of moving! *)
(* TODO move *)
Definition mutability_of_bools b1 b2 :=
    if b1 then J.mutability_of_bool b2 else J.mutability_immutable.

(* TODO move *)
(*
Lemma js_env_record_write_decl_env_lemma : forall jst jeptr s jmut jv jder,
    binds jst jeptr (J.env_record_decl jder) ->
    J.env_record_write_decl_env jst jeptr s jmut jv = 
        jst \(jeptr := J.env_record_decl (J.decl_env_record_write jder s jmut jv)).
Proof.
    introv Hbinds.
    unfolds J.env_record_write_decl_env.
    rew_heap_to_libbag.
    simpl in Hbinds. unfolds J.env_record_binds. rew_heap_to_libbag in Hbinds.
    erewrite read_binds_inv by eauto.
    reflexivity.
Qed.
*)

Lemma decl_env_record_related_write_preserved : forall BR jder obj s jv v b1 b2,
    b1 || !b2 ->
    value_related BR jv v ->
    decl_env_record_related BR jder obj ->
    decl_env_record_related BR (J.decl_env_record_write jder s (mutability_of_bools b1 b2) jv)
        (L.set_object_property obj s (L.attributes_data_of (L.attributes_data_intro v b1 true b2))).
Proof.
    introv Hboolcond Hvrel Herel.
    unfolds J.decl_env_record_write.
    destruct obj.
    simpls.
    rew_heap_to_libbag.
    destruct Herel.
    constructor; try eassumption.
    unfolds.
    intro s'.
    destruct (classic (s = s')). { (* equal *)
        substs.
        right.
        do 3 eexists. splits; [rew_binds_eq; iauto | idtac | idtac]. { 
            simpls.
            rewrite binds_update_same_eq.
            destruct b1; destruct b2; simpl; tryfalse; try reflexivity. 
        } {
            unfolds. left. split; [idtac | eassumption].
            { intro; destruct b1; destruct b2; tryfalse. }
        }
    } { (* disequal *)
        lets Hx : decl_env_record_related_vars s'.
        destruct_hyp Hx.
        left. split. rew_index_eq. iauto.
        simpls. rew_index_eq. iauto.
        right. simpls. do 3 eexists. rew_heap_to_libbag in *. rew_binds_eq. iauto.
    }
Qed.

Lemma add_accessor_field_lemma : forall k c st st' r s v1 v2 b1 b2 ptr obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privAddAccessorField 
        [L.value_object ptr; L.value_string s; v1; v2; L.value_bool b1; L.value_bool b2])
        (L.out_ter st' r) ->
    binds st ptr obj ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_accessor_of 
        (L.attributes_accessor_intro v1 v2 b1 b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hlred Hbinds.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide. {
        repeat ljs_autoforward. 
        inv_ljs.
    }
    repeat ljs_autoforward.
    destruct obj.
    inv_ljs. {
        binds_determine.
        false. prove_bag.
    }
    simpls.
    do 3 (repeat ljs_autoforward; inv_ljs; [idtac | binds_inv; false; prove_bag 7]). 
    repeat ljs_autoforward. 
    simpls.
    repeat binds_inv.
    simpls.
    rew_bag_simpl.
    eauto_js.
Qed.

Lemma add_data_field_lemma : forall k c st st' r s v b0 b1 b2 ptr obj,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privAddDataField 
        [L.value_object ptr; L.value_string s; v; L.value_bool b0; L.value_bool b1; L.value_bool b2])
        (L.out_ter st' r) ->
    binds st ptr obj ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of (L.attributes_data_intro v b0 b1 b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s.
Proof.
    introv Hlred Hbinds.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide. {
        repeat ljs_autoforward. 
        inv_ljs.
    }
    repeat ljs_autoforward.
    destruct obj.
    inv_ljs. {
        binds_determine.
        false. prove_bag.
    }
    simpls.
    do 3 (repeat ljs_autoforward; inv_ljs; [idtac | binds_inv; false; prove_bag 7]). 
    repeat ljs_autoforward. 
    simpls.
    repeat binds_inv.
    simpls.
    rew_bag_simpl.
    eauto_js.
Qed.

Lemma decl_env_add_binding_lemma : forall BR k jst jc c st st' r jder jeptr ptr obj b1 b2 jv v s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool b1; L.value_bool b2]) (L.out_ter st' r) -> 
    b1 || !b2 ->
    binds st ptr obj ->
    binds jst jeptr (J.env_record_decl jder) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    decl_env_record_related BR jder obj ->
    value_related BR jv v ->
    fact_js_env jeptr ptr \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of 
        (L.attributes_data_intro v b1 true b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s /\ ~index jder s /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr jder s (mutability_of_bools b1 b2) jv) st'.
Proof.
    introv Hlred Hboolcond Hbinds Hjbinds Hcinv Hinv Herel Hvrel Hfact.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    forwards_th Hx : add_data_field_lemma. eassumption.
    destruct_hyp Hx.
    splits; try eauto_js.
    {
    lets Hx : decl_env_record_related_vars Herel s. 
    destruct_hyp Hx; prove_bag.
    }
    {
    destruct obj.
    eapply state_invariant_modify_env_record_preserved; try eassumption.
    eapply env_record_related_decl.
    lets Hx : decl_env_record_related_write_preserved Hboolcond Hvrel Herel. 
    eapply Hx. 
    reflexivity.
    }
Qed.

Lemma decl_env_add_mutable_binding_lemma : forall BR k jst jc c st st' r jder jeptr ptr obj b2 jv v s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool true; L.value_bool b2]) (L.out_ter st' r) -> 
    binds st ptr obj ->
    binds jst jeptr (J.env_record_decl jder) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    decl_env_record_related BR jder obj ->
    value_related BR jv v ->
    fact_js_env jeptr ptr \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of 
        (L.attributes_data_intro v true true b2))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s /\ ~index jder s /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) jv) st'.
Proof.
    intros. eapply decl_env_add_binding_lemma; eauto.
Qed.

Lemma create_mutable_binding_some_lemma : forall jst jc jeptr s b2 jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s (Some b2)) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) 
        (J.value_prim J.prim_undef))).
Proof.
    introv Hbinds Hnind. eauto_js.
Qed. 

Lemma create_mutable_binding_none_lemma : forall jst jc jeptr s jder,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_mutable_binding jeptr s None) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool false) 
        (J.value_prim J.prim_undef))).
Proof.
    introv Hbinds Hnind. eauto_js.
Qed. 

Lemma js_mutability_of_bool_is_mutable : forall b,
    J.mutability_is_mutable (J.mutability_of_bool b).
Proof. 
    introv. destruct b; unfolds; eauto.
Qed.

Hint Resolve js_mutability_of_bool_is_mutable : js_ljs.

Lemma js_mutability_of_bool_is_mutable_if_rewrite : forall T b (x1 : T) x2,
    (If J.mutability_is_mutable (J.mutability_of_bool b) then x1 else x2) = x1.
Proof.
    introv. cases_if. reflexivity. false. eauto_js.
Qed.

Hint Rewrite js_mutability_of_bool_is_mutable_if_rewrite : js_ljs.

Hint Extern 80 => progress rew_heap_to_libbag : js_ljs.

Lemma create_set_mutable_binding_some_lemma : forall jst jc jeptr s b2 jder jv b,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_set_mutable_binding jeptr s (Some b2) jv b) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool b2) jv)).
Proof.
    introv Hbinds Hnind.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    unfolds J.env_record_write_decl_env.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding. eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl. eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x.
    unfolds J.env_record_write_decl_env.
    rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed. 

Hint Resolve create_set_mutable_binding_some_lemma : js_ljs.

Lemma create_set_mutable_binding_none_lemma : forall jst jc jeptr s jder jv b,
    binds jst jeptr (J.env_record_decl jder) ->
    ~index jder s ->
    J.red_expr jst jc (J.spec_env_record_create_set_mutable_binding jeptr s None jv b) 
        (J.out_void (J.env_record_write_decl_env jst jeptr jder s (J.mutability_of_bool false) jv)).
Proof.
    introv Hbinds Hnind.
    eapply J.red_spec_env_record_create_set_mutable_binding.
    eauto_js.
    unfolds J.env_record_write_decl_env.
    eapply J.red_spec_env_record_create_set_mutable_binding_1.
    eapply J.red_spec_env_record_set_mutable_binding.
    rew_heap_to_libbag. eauto_js.
    eapply J.red_spec_env_record_set_mutable_binding_1_decl.
    rew_heap_to_libbag. eauto_js. eauto_js.
    autorewrite with js_ljs. sets_eq_let x.
    unfolds J.env_record_write_decl_env.
    repeat rew_heap_to_libbag in EQx.
    rew_bag_simpl in EQx.
    substs. eauto_js.
Qed.

Hint Resolve create_set_mutable_binding_none_lemma : js_ljs.
(* TODO end big block of moving! *)

(* *** Getting and setting of object fields *)

(* TODO move to common *)
Ltac apply_ih_call := match goal with
    | H : ih_call ?k', 
      HS : state_invariant ?BR ?jst ?st,
      HC' : context_invariant ?BR' ?jc ?c', 
      HR : L.red_exprh ?k ?c ?st (L.expr_app_2 LjsInitEnv.privAppExpr _) _ |- _ =>
        let Hle := fresh "Hle" in
        let HC := fresh "HC" in
        let Hsec := fresh "Hsec" in
        let Hsub := fresh "H" in
        asserts Hle : (k < k')%nat; [math | idtac];
        asserts Hsub : (BR' \c BR); [prove_bag | idtac];
        asserts HC : (context_invariant BR jc c); 
            [applys context_invariant_bisim_incl_preserved Hsub; ljs_context_invariant | idtac]; 
        lets Hih : H Hle HC HS HR; 
        [eauto_js
        |prove_bag|prove_bag
        |try repeat first [eapply Forall2_nil | eapply Forall2_cons; [eauto_js | idtac]]
        |clear Hle; clear Hsub; clear HS; clear HR; clear HC]
   (*     lets Hsec : L.red_exprh_state_security_ok HR;  *)
    end.

Lemma get_default_lemma : forall BR k jst jc c st st' r ptr jptr v jv s,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetDefault [L.value_object ptr; v; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_get_1 J.builtin_get_default jv jptr s) (fun _ => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : get_property_lemma. eassumption.
    destruct_hyp Hx; try ljs_handle_abort. { (* field not found *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    } { (* data field *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        jauto_js.
    } { (* accessor field *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        cases_decide as Heq; rewrite stx_eq_undefined_eq_lemma in Heq. { (* getter undefined *)
            subst_hyp Heq.
            inverts Hx4. (* TODO *) (* inverting value_related *)
            repeat ljs_autoforward.
            jauto_js.
        } { (* getter defined *)
            inverts Hx7; tryfalse. (* TODO *) (* inverting object_or_undefined *)
            inverts Hx4. (* inverting value_related *)
            repeat ljs_autoforward.
            forwards_th Hy : zero_arg_obj_lemma.
            destruct_hyp Hy.
            repeat ljs_autoforward.
            apply_ih_call.
            destr_concl; try ljs_handle_abort.
            jauto_js.
        }
    }
Qed.
(*
Lemma get_1_lemma : forall BR k jst jc c st st' r ptr jptr v jv s x,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGet [L.value_object ptr; v; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    value_related BR jv v ->
    J.object_method J.object_get_ jst jptr x ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_get_1 x jv jptr s) (fun _ => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel Hm.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* exotic *)
        skip. (* TODO *)
    } { (* default *)
        repeat ljs_autoforward.
        forwards : object_method_get_default_lemma; try eassumption.
        forwards_th : get_default_lemma; try eassumption.
    }
    forwards Hmm : object_method_get_lemma; try eassumption. (* TODO *)
    asserts Heq : (x = J.builtin_get_default). skip. (* TODO exotic objects *) subst_hyp Heq.
    forwards_th : get_default_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js.
Qed.
*)
Lemma get_lemma : forall BR k jst jc c st st' r ptr jptr s,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGet1 [L.value_object ptr; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_object_get jptr s) (fun _ => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* exotic *)
        skip. (* TODO *)
    } { (* default *)
        repeat ljs_autoforward.
        forwards : object_method_get_default_lemma; try eassumption.
        forwards_th : get_default_lemma; try eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js.
    }
Qed.

Lemma get_prim_lemma : forall BR k jst jc c st st' r v jv s,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privGetPrim [v; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_prim_value_get jv s) (fun _ => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hf.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_object_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide as Hidx. { (* exotic *)
        skip. (* TODO *)
    } { (* default *)
        repeat ljs_autoforward.
        forwards : object_method_get_default_lemma; try eassumption.
        forwards_th : get_default_lemma; try eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js.
    }
Qed.

(* TODO move *)
Lemma object_method_can_put_lemma : forall BR jst st jptr ptr,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_can_put_ jst jptr J.builtin_can_put_default.
Proof.
Admitted. (* TODO: ignoring exotic objects for now *)

(* TODO move to utils *)
Parameter string_of_nat_0_lemma : string_of_nat 0 = "0".

(* TODO move *)
Lemma one_arg_obj_lemma : forall BR k jst jc c st st' r v1,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privoneArgObj [v1]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' ptr,
    state_invariant BR' jst st' /\
    BR \c BR' /\
    st \c st' /\
    fact_iarray ptr [v1] \in BR' /\
    r = L.res_value (L.value_object ptr).
Proof.
    introv Hlred Hcinv Hinv.
    ljs_invert_apply.
    repeat ljs_autoforward.
    evar (obj : L.object).
    cuts Hiobj : (iarray_object obj [v]); subst obj. {
        exists (\{fact_iarray (fresh st) [v]} \u BR) (fresh st).
        jauto_js.
    }
    constructor.
    + introv Hnth. inverts Hnth as Hnth; try inverts Hnth. simpl. rewrite string_of_nat_0_lemma. prove_bag.
    + introv Hindex. simpl in Hindex. rew_index_eq in Hindex. destruct_hyp Hindex; tryfalse.
      exists 0 v. rewrite string_of_nat_0_lemma. split. reflexivity. eapply Nth_here.
Qed.

(* TODO move *)
Lemma value_related_primitive_lemma : forall BR jv v,
    L.is_primitive v ->
    value_related BR jv v ->
    exists jpv, jv = J.value_prim jpv.
Proof.
    introv Hprim Hvrel.
    inverts Hprim; inverts Hvrel; jauto.
Qed.

(* TODO move *)
Lemma value_related_not_primitive_lemma : forall BR jv v,
    ~L.is_primitive v ->
    value_related BR jv v ->
    exists jptr, jv = J.value_object jptr.
Proof.
    introv Hprim Hvrel.
    inverts Hvrel; try solve [false; apply Hprim; eauto_js].
    jauto.
Qed.

Lemma put_default_lemma : forall BR k jst jc c st st' r ptr jptr v jv v1 jv1 s b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privPut 
        [L.value_object ptr; v; L.value_string s; v1; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    value_related BR jv v ->
    value_related BR jv1 v1 ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_object_put_1 J.builtin_put_default jv jptr s jv1 b) 
        (fun jrv => jrv = J.resvalue_empty).
Admitted. (* this thing eats lots of memory
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel1 Hvrel2.
    ljs_invert_apply.
    forwards Hcp : object_method_can_put_lemma; try eassumption.
    forwards Hgp : object_method_get_property_lemma; try eassumption.
    repeat ljs_autoforward.
    forwards_th Hx : get_own_property_lemma. eassumption.
    destruct_hyp Hx; try ljs_handle_abort. { (* field not found *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        cases_decide as Hpnull; rewrite stx_eq_null_eq_lemma in Hpnull. { (* proto is null *)
            forwards Hjproto : object_proto_null_lemma; try prove_bag.
            repeat ljs_autoforward.
            forwards Hjext : object_extensible_lemma; try prove_bag.
            unfold L.object_extensible in Hjext. 
            inv_ljs. { (* extensible *)
                rewrite <- H11 in Hjext. (* TODO *)
                repeat ljs_autoforward.
                cases_decide as Hprim. { (* is primitive *)
                    lets (jpv&EQjpv) : value_related_primitive_lemma Hprim Hvrel1.
                    subst_hyp EQjpv.
                    repeat ljs_autoforward.
                    forwards_th : type_error_or_void_lemma. eauto_js.
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    resvalue_related_only_invert.
                    jauto_js 15.
                } { (* not primitive *)
                    lets (jptr_this&EQjptr) : value_related_not_primitive_lemma Hprim Hvrel1.
                    subst_hyp EQjptr.
                    repeat ljs_autoforward.
                    forwards_th Hx : make_data_descriptor_ljs_lemma.
                    unfolds in Hx. destruct_hyp Hx.
                    repeat ljs_autoforward.
                    forwards_th : define_own_property_lemma; try prove_bag. skip. skip. (* TODO *)
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    repeat ljs_autoforward.
                    jauto_js 15.
                }
            } { (* not extensible *)
                rewrite <- H11 in Hjext. (* TODO *)
                repeat ljs_autoforward.
                forwards_th : type_error_or_void_lemma. eauto_js.
                destr_concl; try ljs_handle_abort.
                res_related_invert.
                resvalue_related_only_invert.
                jauto_js 12.
            }
        } { (* proto not null *)
            forwards Hjproto : object_proto_not_null_lemma; try prove_bag.
            destruct_hyp Hjproto.
            repeat ljs_autoforward.
            unfolds L.object_proto. rewrite Hjproto0 in *. (* TODO *)
            forwards_th Hy : get_property_lemma. prove_bag.
            destruct_hyp Hy; try ljs_handle_abort. { (* field not found in prototype *)
                repeat ljs_autoforward.
                ljs_invert_apply.
                repeat ljs_autoforward.
                forwards Hjext : object_extensible_lemma; try eapply H10; try prove_bag. (* TODO *)
                unfold L.object_extensible in Hjext. 
                inv_ljs. { (* extensible *)
                    rewrite <- H21 in Hjext. (* TODO *)
                    repeat ljs_autoforward.
                    cases_decide as Hprim. { (* is primitive *)
                        lets (jpv&EQjpv) : value_related_primitive_lemma Hprim Hvrel1.
                        subst_hyp EQjpv.
                        repeat ljs_autoforward.
                        forwards_th : type_error_or_void_lemma. eauto_js.
                        destr_concl; try ljs_handle_abort.
                        res_related_invert.
                        resvalue_related_only_invert.
                        jauto_js 20.
                    } { (* not primitive *)
                        lets (jptr_this&EQjptr) : value_related_not_primitive_lemma Hprim Hvrel1.
                        subst_hyp EQjptr.
                        repeat ljs_autoforward.
                        forwards_th Hx : make_data_descriptor_ljs_lemma.
                        unfolds in Hx. destruct_hyp Hx.
                        repeat ljs_autoforward.
                        forwards_th : define_own_property_lemma; try prove_bag. skip. skip. (* TODO *)
                        destr_concl; try ljs_handle_abort.
                        res_related_invert.
                        repeat ljs_autoforward.
                        jauto_js 20.
                    }
                } { (* not extensible *)
                    rewrite <- H21 in Hjext. (* TODO *)
                    repeat ljs_autoforward.
                    forwards_th : type_error_or_void_lemma. eauto_js.
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    resvalue_related_only_invert.
                    jauto_js 12.
                }
            } { (* data field in prototype *) 
                ljs_invert_apply.
                repeat ljs_autoforward.
                forwards Hjext : object_extensible_lemma; try eapply H10; try prove_bag. (* TODO *)
                unfold L.object_extensible in Hjext. 
                inv_ljs. { (* extensible *)
                    rewrite <- H21 in Hjext. (* TODO *)
                    repeat ljs_autoforward.
                    inv_ljs. { (* writable *)
                        repeat ljs_autoforward.
                        cases_decide as Hprim. { (* is primitive *)
                            lets (jpv&EQjpv) : value_related_primitive_lemma Hprim Hvrel1.
                            subst_hyp EQjpv.
                            repeat ljs_autoforward.
                            forwards_th : type_error_or_void_lemma. eauto_js.
                            destr_concl; try ljs_handle_abort.
                            res_related_invert.
                            resvalue_related_only_invert.
                            jauto_js 20.
                        } { (* not primitive *)
                            lets (jptr_this&EQjptr) : value_related_not_primitive_lemma Hprim Hvrel1.
                            subst_hyp EQjptr.
                            repeat ljs_autoforward.
                            forwards_th Hx : make_data_descriptor_ljs_lemma.
                            unfolds in Hx. destruct_hyp Hx.
                            repeat ljs_autoforward.
                            forwards_th : define_own_property_lemma; try prove_bag. skip. skip. (* TODO *)
                            destr_concl; try ljs_handle_abort.
                            res_related_invert.
                            repeat ljs_autoforward.
                            jauto_js 20.
                        }
                    } { (* not writable *)
                        repeat ljs_autoforward.
                        forwards_th : type_error_or_void_lemma. eauto_js.
                        destr_concl; try ljs_handle_abort.
                        res_related_invert.
                        resvalue_related_only_invert.
                        jauto_js 20.
                    }
                } { (* not extensible *)
                    rewrite <- H21 in Hjext. (* TODO *)
                    repeat ljs_autoforward.
                    forwards_th : type_error_or_void_lemma. eauto_js.
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    resvalue_related_only_invert.
                    jauto_js 12.
                }
            } { (* accessor field in prototype *)
                ljs_invert_apply.
                repeat ljs_autoforward.
                cases_decide as Heq; rewrite stx_eq_undefined_eq_lemma in Heq. { (* setter undefined *)
                    subst_hyp Heq.
                    inverts Hy6. (* TODO *) (* inverting value_related *)
                    repeat ljs_autoforward.
                    forwards_th : type_error_or_void_lemma. eauto_js.
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    resvalue_related_only_invert.
                    jauto_js 12.
                } { (* setter defined *)
                    inverts Hy9; tryfalse. (* TODO *) (* inverting object_or_undefined *)
                    inverts Hy6. (* TODO *) (* inverting value_related *)
                    repeat ljs_autoforward.
                    forwards_th Hy : one_arg_obj_lemma.
                    destruct_hyp Hy.
                    repeat ljs_autoforward.
                    apply_ih_call.
                    destr_concl; try ljs_handle_abort.
                    res_related_invert.
                    resvalue_related_only_invert.
                    repeat ljs_autoforward.
                    jauto_js 30.
                }
            }
        }
    } { (* data field *) 
        ljs_invert_apply.
        repeat ljs_autoforward.
        inv_ljs. { (* writable *)
            repeat ljs_autoforward.
            cases_decide as Hprim. { (* is primitive *)
                lets (jpv&EQjpv) : value_related_primitive_lemma Hprim Hvrel1.
                subst_hyp EQjpv.
                repeat ljs_autoforward.
                forwards_th : type_error_or_void_lemma. eauto_js.
                destr_concl; try ljs_handle_abort.
                res_related_invert.
                resvalue_related_only_invert.
                jauto_js 20.
            } { (* not primitive *)
                lets (jptr_this&EQjptr) : value_related_not_primitive_lemma Hprim Hvrel1.
                subst_hyp EQjptr.
                repeat ljs_autoforward.
                forwards_th Hx : make_value_only_descriptor_ljs_lemma.
                unfolds in Hx. destruct_hyp Hx.
                repeat ljs_autoforward.
                forwards_th : define_own_property_lemma; try prove_bag. skip. skip. (* TODO *)
                destr_concl; try ljs_handle_abort.
                res_related_invert.
                repeat ljs_autoforward.
                jauto_js 20.
            }
        } { (* not writable *)
            repeat ljs_autoforward.
            ljs_invert_apply.
            repeat ljs_autoforward.
            forwards_th : type_error_or_void_lemma. eauto_js.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 12.
        }
    } { (* accessor field *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        cases_decide as Heq; rewrite stx_eq_undefined_eq_lemma in Heq. { (* getter undefined *)
            subst_hyp Heq.
            inverts Hx6. (* TODO *) (* inverting value_related *)
            repeat ljs_autoforward.
            ljs_invert_apply.
            repeat ljs_autoforward.
            forwards_th : type_error_or_void_lemma. eauto_js.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 12.
        } { (* setter defined *)
            inverts Hx9; tryfalse. (* TODO *) (* inverting object_or_undefined *)
            inverts Hx6. (* inverting value_related *)
            repeat ljs_autoforward.
            forwards_th Hy : one_arg_obj_lemma.
            destruct_hyp Hy.
            repeat ljs_autoforward.
            apply_ih_call.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            repeat ljs_autoforward.
            jauto_js 30.
        }
    }
Qed.
*)

Lemma put_1_lemma : forall BR k jst jc c st st' r ptr jptr v jv s x v1 jv1 b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privPut 
        [L.value_object ptr; v; L.value_string s; v1; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    value_related BR jv v ->
    value_related BR jv1 v1 ->
    J.object_method J.object_put_ jst jptr x ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_object_put_1 x jv jptr s jv1 b) 
       (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel Hvrels Hm.
    forwards Hmm : object_method_put_lemma; try eassumption. (* TODO *)
    asserts Heq : (x = J.builtin_put_default). skip. (* TODO exotic objects *) subst_hyp Heq.
    forwards_th : put_default_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js.
Qed.

Lemma put_lemma : forall BR k jst jc c st st' r ptr jptr s v1 jv1 b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privPut1 [L.value_object ptr; L.value_string s; v1; L.value_bool b])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    value_related BR jv1 v1 ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_object_put jptr s jv1 b) 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel.
    ljs_invert_apply.
    forwards Hmm : object_method_put_lemma; try eassumption. (* TODO *)
    repeat ljs_autoforward.
    forwards_th : put_1_lemma; try eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js.
Qed.

Lemma put_prim_lemma : forall BR k jst jc c st st' r v jv s v1 jv1 b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privPutPrim [v; L.value_string s; v1; L.value_bool b])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    value_related BR jv1 v1 ->
    concl_ext_expr_resvalue BR jst jc c st st' r (J.spec_prim_value_put jv s jv1 b) 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrel Hvrel1.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : red_spec_to_object_ok.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    forwards Hmm : object_method_put_lemma; try eassumption. (* TODO *)
    repeat ljs_autoforward.
    forwards_th : put_1_lemma; try eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js.
Qed.

(* *** Methods of environment records *)

Lemma get_binding_value_lemma : forall BR k jst jc c st st' r ptr s b jeptr,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvGetBindingValue 
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_env_record_get_binding_value jeptr s b) (fun _ => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hd; rewrite stx_eq_empty_eq_lemma in Hd. { (* uninitialized immutable *)
            simpl in Hd. subst_hyp Hd.
            forwards (Heq1&Heq2) : decl_env_record_var_related_empty_lemma; try eassumption.
            subst_hyp Heq1. subst_hyp Heq2.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th : reference_error_lemma. eauto_js.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* not strict *)
                repeat ljs_autoforward.
                jauto_js 10.
            }
        } {
            repeat ljs_autoforward.
            simpl.
            forwards (Hvrel&Hjmut) : decl_env_record_var_related_not_empty_lemma; try eassumption.
            jauto_js 15.
        }
    } { (* object records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
        repeat ljs_autoforward.
        forwards_th : has_property_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        inv_ljs. { (* field found *)
            repeat ljs_autoforward.
            forwards_th : get_lemma. prove_bag.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            jauto_js 10.
        } { (* field not found *)
            repeat ljs_autoforward.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th : reference_error_lemma. eauto_js.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* not strict *)
                repeat ljs_autoforward.
                jauto_js 10.
            }
        }
    }
Qed.

(* TODO should not be necessary *)
Hint Extern 3 (J.red_expr _ _ (J.expr_assign_1 _ _ _) _) => eapply J.red_expr_assign_1_simple : js_ljs.

Lemma mutability_not_immutable_lemma : forall jmut,
    jmut <> J.mutability_uninitialized_immutable ->
    jmut <> J.mutability_immutable -> 
    mutability_writable jmut = true.
Proof.
    introv Hx1 Hx2.
    destruct jmut; tryfalse; try reflexivity.
Qed.

Lemma decl_env_record_vars_related_write_lemma : forall BR jder props s jmut jv v,
    decl_env_record_vars_related BR jder props ->
    decl_env_record_var_related BR jmut jv v ->
    decl_env_record_vars_related BR (jder\(s:=(jmut, jv)))
        (props\(s:=L.attributes_data_of 
            (L.attributes_data_intro v (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Hvrels Hvrel.
    intro s'.
    destruct (classic (s = s')). {
        substs. 
        right.
        jauto_js.
    } {
        specializes Hvrels s'.
        destruct_hyp Hvrels. {
            left. split; prove_bag.
        } {
            right. repeat eexists; prove_bag.
        }
    }
Qed.

Hint Extern 3 (decl_env_record_vars_related _ ?jder _) => 
    not (is_evar jder); eapply decl_env_record_vars_related_write_lemma : js_ljs.

Lemma decl_env_record_related_write_lemma : forall BR jder s obj jmut jv v,
    decl_env_record_related BR jder obj ->
    decl_env_record_var_related BR jmut jv v ->
    decl_env_record_related BR 
        (J.decl_env_record_write jder s jmut jv)
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Herel Hvrel.
    destruct obj. destruct object_attrs.
    destruct Herel.
    unfolds L.object_proto. unfolds L.object_class. unfolds L.object_extensible.
    simpls.
    constructor; eauto.
    apply decl_env_record_vars_related_write_lemma; assumption.
Qed.

Hint Extern 3 (decl_env_record_related _ ?jer _) => 
    not (is_evar jer); eapply decl_env_record_related_write_lemma : js_ljs.

Lemma object_internal_write_hint : forall obj s attrs,
    L.object_internal obj = L.object_internal (L.set_object_property obj s attrs).
Proof.
    destruct obj. reflexivity.
Qed.

Lemma object_internal_read_option_write_hint : forall obj obj' s,
    L.object_internal obj = L.object_internal obj' ->
    L.object_internal obj\(s?) = L.object_internal obj'\(s?).
Proof.
    introv Heq. rewrite Heq. reflexivity.
Qed.

Hint Resolve object_internal_read_option_write_hint object_internal_write_hint : js_ljs.

Hint Extern 1 (decl_env_record_var_related _ _ _ _) => unfolds : js_ljs.

(*
Lemma env_record_related_decl_write_lemma : forall BR jder s obj jmut jv v,
    env_record_related BR (J.env_record_decl jder) obj ->
    decl_env_record_var_related BR jmut jv v ->
    env_record_related BR 
        (J.env_record_decl (J.decl_env_record_write jder s jmut jv)) 
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Herel Hvrel.
    inverts Herel as Herel.
    constructor. apply decl_env_record_related_write_lemma; assumption.
Qed.

Hint Extern 3 (env_record_related _ ?jer _) => 
    not (is_evar jer); eapply env_record_related_decl_write_lemma : js_ljs.
*)

(*
Lemma env_record_related_decl_write : forall BR jder s obj jmut jv v,
    value_related BR jv v ->
    env_record_related BR (J.env_record_decl jder) obj ->
    jmut <> J.mutability_uninitialized_immutable ->
    env_record_related BR 
        (J.env_record_decl (J.decl_env_record_write jder s jmut jv)) 
        (L.set_object_property obj s 
            (L.attributes_data_of (L.attributes_data_intro v (* TODO factorize this to the decl_env_record_rel *)
                (mutability_writable jmut) true (mutability_configurable jmut)))).
Proof.
    introv Hvrel Herel Hjmut. 
    destruct obj. destruct object_attrs.
    inverts Herel as Herel. inverts Herel. 
    unfolds L.object_proto. unfolds L.object_class. unfolds L.object_extensible.
    simpls.
    constructor. constructor; eauto.
    simpl.
    intro s'.
    destruct (classic (s = s')) as [Hs|Hs]. {
        subst_hyp Hs.
        right. unfolds decl_env_record_var_related.
        jauto_js.
    } {
        lets Hx : decl_env_record_related_vars s'.
        destruct_hyp Hx. {
            left. 
            asserts Hs' : (s' <> s). solve [eauto].
            unfolds J.decl_env_record_write. repeat rew_heap_to_libbag. 
            split; intro Hi; eapply index_update_diff_inv in Hi; eauto.
        } {
            right. 
            unfolds J.decl_env_record_write. repeat rew_heap_to_libbag. 
            prove_bag 20.
        }
    }
Qed.

Hint Extern 3 (env_record_related _ ?jer _) => not (is_evar jer); eapply env_record_related_decl_write : js_ljs.
*)

Lemma mutability_is_mutable_uninitialized_immutable :
    ~JsPreliminary.mutability_is_mutable J.mutability_uninitialized_immutable.
Proof.
    intro H. unfolds in H. destruct_hyp H. tryfalse.
Qed.

Hint Resolve mutability_is_mutable_uninitialized_immutable : js_ljs.

Lemma mutability_is_mutable_immutable :
    ~JsPreliminary.mutability_is_mutable J.mutability_immutable.
Proof.
    intro H. unfolds in H. destruct_hyp H. tryfalse.
Qed.

Hint Resolve mutability_is_mutable_immutable : js_ljs.

Lemma set_mutable_binding_lemma : forall BR k jst jc c st st' r v ptr s b jeptr jv,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvSetMutableBinding 
        [L.value_object ptr; L.value_string s; v; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_set_mutable_binding jeptr s jv b) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hd; rewrite stx_eq_empty_eq_lemma in Hd. { (* uninitialized immutable *)
            lets Hmutmut : mutability_is_mutable_uninitialized_immutable.
            simpl in Hd. subst_hyp Hd.
            forwards (Heq1&Heq2) : decl_env_record_var_related_empty_lemma; try eassumption.
            subst_hyp Heq1. subst_hyp Heq2.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th : type_error_lemma. eauto_js.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* not strict *)
                repeat ljs_autoforward.
                jauto_js 10.
            }
        }
        simpl in Hd.
        forwards (Hvrel'&Hjmut) : decl_env_record_var_related_not_empty_lemma; try eassumption.
        destruct (classic (jmut = J.mutability_immutable)) as [Heqmut|Heqmut]. { (* immutable binding *)
            lets Hmutmut : mutability_is_mutable_immutable.
            subst_hyp Heqmut.
            destruct b. { (* strict *)
                repeat ljs_autoforward.
                forwards_th Hx : type_error_lemma. eauto_js.
                destr_concl; tryfalse.
                ljs_handle_abort.
            } { (* nonstrict *)
                repeat ljs_autoforward.
                jauto_js 10. 
            }
        } { (* mutable binding *)
            asserts Hmutmut : (J.mutability_is_mutable jmut). { unfolds. eauto. }
            repeat ljs_autoforward.
            rewrite mutability_not_immutable_lemma in H8 by eassumption. (* TODO *)
            repeat ljs_autoforward.
            inv_ljs; repeat binds_determine; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            jauto_js 10. 
        }
    } { (* object records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
        repeat ljs_autoforward.
        forwards_th : put_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    }
Qed.

Lemma has_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvHasBinding
        [L.value_object ptr; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_env_record_has_binding jeptr s) (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Hidx. {
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            jauto_js 10.
        } {
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            asserts Hjidx : (~J.decl_env_record_indom jder s0). { assumption. }
            jauto_js 10.
        }
    } { (* object records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
        repeat ljs_autoforward.
        forwards_th : has_property_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        jauto_js.
    }
Qed.

(*
Definition concl_ljs_new_descriptor st st' r desc :=
    exists ptr obj,
    property_descriptor desc obj /\
    r = L.res_value (L.value_object ptr) /\
    st \c st' /\
    binds st' ptr obj /\
    ~index st ptr.*)

Lemma create_mutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr b ob,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    b = unsome_default false ob ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s ob) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hb.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        forwards_th Hx : decl_env_add_mutable_binding_lemma; try prove_bag.
        destruct_hyp Hx.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* object records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
        repeat ljs_autoforward.
        forwards_th Hx : make_data_descriptor_lemma.
        unfold concl_ljs_new_descriptor in Hx. destruct_hyp Hx.
        repeat ljs_autoforward.
        forwards_th : define_own_property_lemma; try prove_bag.
        skip.
(* WTF assert in the rules?!?
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        jauto_js 20.
*)
    }
Qed.

Lemma create_mutable_binding_lemma_some : forall BR k jst jc c st st' r ptr s jeptr b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s (Some b)) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    eapply create_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_mutable_binding_lemma_none : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateMutableBinding
        [L.value_object ptr; L.value_string s; L.value_false]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_mutable_binding jeptr s None) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    eapply create_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_set_mutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr b b' ob v jv,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool b; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    b = unsome_default false ob ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s ob jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel Hb.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th : create_mutable_binding_lemma; try eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th : set_mutable_binding_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    jauto_js 10.
Qed.

Lemma create_set_mutable_binding_lemma_some : forall BR k jst jc c st st' r ptr s jeptr b b' v jv,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool b; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s (Some b) jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel.
    eapply create_set_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

Lemma create_set_mutable_binding_lemma_none : forall BR k jst jc c st st' r ptr s jeptr b' v jv,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateSetMutableBinding
        [L.value_object ptr; L.value_string s; v; L.value_bool false; L.value_bool b']) 
            (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_set_mutable_binding jeptr s None jv b') 
        (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hf Hvrel.
    eapply create_set_mutable_binding_lemma; try eassumption. reflexivity.
Qed.

(* TODO move *)
Lemma decl_env_record_related_write_immutable_preserved : forall BR jder obj s,
    decl_env_record_related BR jder obj ->
    decl_env_record_related BR 
        (J.decl_env_record_write jder s J.mutability_uninitialized_immutable (J.value_prim J.prim_undef))
        (L.set_object_property obj s (L.attributes_data_of (L.attributes_data_intro L.value_empty true true false))).
Proof.
    introv Herel.
    unfolds J.decl_env_record_write.
    destruct obj.
    simpls.
    rew_heap_to_libbag.
    destruct Herel.
    constructor; try eassumption.
    unfolds.
    intro s'.
    destruct (classic (s = s')). { (* equal *)
        substs.
        right.
        do 3 eexists. splits; [rew_binds_eq; iauto | idtac | idtac]. {
            simpls.
            rewrite binds_update_same_eq. reflexivity.
        } {
            unfolds. right. eauto.
        }
    } { (* disequal *)
        lets Hx : decl_env_record_related_vars s'.
        destruct_hyp Hx.
        left. split. rew_index_eq. iauto.
        simpls. rew_index_eq. iauto.
        right. simpls. do 3 eexists. rew_heap_to_libbag in *. rew_binds_eq. iauto.
    }
Qed.

(* TODO move *)
Lemma decl_env_add_immutable_binding_lemma : forall BR k jst jc c st st' r jder jeptr ptr obj s,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privDeclEnvAddBinding
        [L.value_object ptr; L.value_string s; L.value_empty; L.value_true; L.value_false]) (L.out_ter st' r) ->
    binds st ptr obj ->
    binds jst jeptr (J.env_record_decl jder) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    decl_env_record_related BR jder obj ->
    fact_js_env jeptr ptr \in BR ->
    st' = st \(ptr := L.set_object_property obj s (L.attributes_data_of
        (L.attributes_data_intro L.value_empty true true false))) /\
    r = L.res_value L.value_undefined /\
    ~index (L.object_properties obj) s /\ ~index jder s /\
    state_invariant BR (J.env_record_write_decl_env jst jeptr jder s 
        J.mutability_uninitialized_immutable (J.value_prim J.prim_undef)) st'.
Proof.
    introv Hlred Hbinds Hjbinds Hcinv Hinv Herel Hfact.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : add_data_field_lemma. eassumption.
    destruct_hyp Hx.
    splits; try eauto_js.
    {
    lets Hx : decl_env_record_related_vars Herel s.
    destruct_hyp Hx; prove_bag.
    }
    {
    destruct obj.
    eapply state_invariant_modify_env_record_preserved; try eassumption.
    eapply env_record_related_decl.
    lets Hx : decl_env_record_related_write_immutable_preserved Herel.
    eapply Hx.
    reflexivity.
    }
Qed.

(* TODO should not be needed *)
Hint Extern 1 (J.red_expr _ _ (J.spec_env_record_create_immutable_binding _ _) _) =>
    eapply J.red_spec_env_record_create_immutable_binding : js_ljs.

Lemma create_immutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvCreateImmutableBinding
        [L.value_object ptr; L.value_string s]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_create_immutable_binding jeptr s) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        forwards_th Hx : decl_env_add_immutable_binding_lemma; try prove_bag.
        destruct_hyp Hx.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* object records *)
        inverts keep Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
Qed.

(* TODO should not be needed *)
Hint Extern 1 (J.red_expr _ _ (J.spec_env_record_initialize_immutable_binding _ _ _) _) =>
    eapply J.red_spec_env_record_initialize_immutable_binding : js_ljs.

Lemma initialize_immutable_binding_lemma : forall BR k jst jc c st st' r ptr s jeptr jv v,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvInitializeImmutableBinding 
        [L.value_object ptr; L.value_string s; v]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    fact_js_env jeptr ptr \in BR ->
    value_related BR jv v ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_env_record_initialize_immutable_binding jeptr s jv) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv Hlred Hcinv Hinv Hf Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    repeat ljs_autoforward.
    lets (jer&Hjbinds&Herel) : env_record_related_lookup_lemma ___; try eassumption.
    inverts Herel as Herel. { (* declarative records *)
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
Opaque decide.
        repeat ljs_autoforward.
        lets Hx : decl_env_record_vars_related_binds_lemma ___; try eassumption.
        destruct_hyp Hx.
        cases_decide as Hstxeq; rewrite stx_eq_empty_eq_lemma in Hstxeq; simpl in Hstxeq. { (* imm *)
            subst_eq Hstxeq.
            forwards Hx : decl_env_record_var_related_empty_lemma. eassumption.
            destruct_hyp Hx.
            repeat ljs_autoforward.
            destruct obj.
            inv_ljs; repeat binds_determine; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            inv_ljs; repeat binds_inv; try solve [false; prove_bag]. (* TODO *)
            repeat ljs_autoforward.
            simpl in H3. (* TODO *)
            binds_inv.
            simpl.
            rew_bag_simpl.
            jauto_js 10.
        } {
            repeat ljs_autoforward. inv_ljs.
        }
    } {
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
Qed.

(* ** Function calls *)

Lemma object_method_call_some_lemma : forall BR jst st jptr ptr obj clo,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    L.object_code obj = L.value_closure clo ->
    exists jcall,
    J.object_method J.object_call_ jst jptr (Some jcall) /\
    call_related jcall (L.value_closure clo).
Proof.
    introv Hinv Hbs Hbinds Hclo.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    inverts object_prim_related_call as Hp1 Hp2. {
        symmetry in Hp2. unfolds J.object_method.
        rewrite <- Hclo.
        jauto_js.
    } {
        tryfalse.
    } 
Qed.

Lemma object_method_code_some_lemma : forall BR jst st jptr ptr obj v,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "usercode" v ->
    exists jfb is jle,
    J.object_method J.object_code_ jst jptr (Some jfb) /\
    J.object_method J.object_formal_parameters_ jst jptr (Some is) /\
    J.object_method J.object_scope_ jst jptr (Some jle) /\
    usercode_related BR jfb is jle v.
Proof.
    introv Hinv Hbs Hbinds Hibinds.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_usercode by eassumption.
    inverts object_prim_related_usercode as Hp1 Hp2 Hp3 Hp4.
    symmetry in Hp2. symmetry in Hp3. symmetry in Hp4.
    unfolds J.object_method.
    jauto_js.
Qed.

Lemma object_strict_lemma : forall BR jst st jptr ptr obj v jfb,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (L.object_internal obj) "strict" v ->
    J.object_method J.object_code_ jst jptr (Some jfb) ->
    exists b,
    v = L.value_bool b /\
    J.funcbody_is_strict jfb = b.
Proof.
    introv Hinv Hbs Hbinds Hibinds Hcode.
    destruct Hcode as (jobj'&Hjbinds&Hzzz).
    rew_heap_to_libbag in Hjbinds.
    lets Horel : heaps_bisim_consistent_bisim_obj (state_invariant_heaps_bisim_consistent Hinv) Hbs Hjbinds Hbinds.
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_func_strict by eassumption.
    inverts object_prim_related_func_strict as Hp1 Hp2.
    inverts Hp1.
    rewrite Hzzz in Hp2.
    injects.
    jauto_js.
Qed.

Lemma usercode_context_invariant_restore_lemma : forall BR jeptr ptr jle c jv v b v' v'' v''',
    initBR \c BR ->
    binds c "$context" v' ->
    fact_js_env jeptr ptr \in BR ->
    fact_ctx_parent ptr v' \in BR ->
    value_related BR jv v ->
    usercode_context_invariant BR jle b c ->
    context_invariant BR 
        (J.execution_ctx_intro_same (jeptr::jle) jv b) 
        (c\("args" := v'')\("$this" := v)\("obj" := v''')
           \("$context" := L.value_object ptr)\("$vcontext" := L.value_object ptr)).
Proof.
    introv Hinit Hbinds Hf1 Hf2 Hthisrel Hucinv.
    lets Hlerel : usercode_context_invariant_lexical_env_related Hucinv Hbinds.
    destruct Hucinv.
    constructor. {
        assumption.
    } {
        constructor; introv Hb; 
        repeat rewrite binds_update_diff_eq in Hb by prove_bag;
        repeat rewrite binds_update_same_eq in Hb by prove_bag;
        try subst_hyp Hb; simpl; eauto_js 2.
    } 
    + eauto_js 8.
    + constructor; introv Hmem; inverts Hmem as Hmem; eauto_js.
Qed.

Lemma usercode_context_invariant_restore : forall BR k jle c jv v b v' v'' v''' jst st st' r jc' c',
    L.red_exprh k (c\("args" := v'')\("$this" := v)\("obj" := v''')) st 
        (L.expr_app_2 LjsInitEnv.privnewDeclEnvRec [v']) (L.out_ter st' r) ->
    context_invariant BR jc' c' ->
    state_invariant BR jst st ->
    usercode_context_invariant BR jle b c ->
    binds c "$context" v' ->
    value_related BR jv v ->
    exists obj BR',
    st' = st \(fresh st := obj) /\
    r = L.res_value (L.value_object (fresh st)) /\
    BR' = \{fact_ctx_parent (fresh st) v'} \u \{fact_js_env (fresh jst) (fresh st)} \u BR /\
    env_record_related BR' (J.env_record_decl J.decl_env_record_empty) obj /\
    context_invariant BR'
        (J.execution_ctx_intro_same (fresh jst::jle) jv b) 
        (c\("args" := v'')\("$this" := v)\("obj" := v''')
          \("$context" := L.value_object (fresh st))\("$vcontext" := L.value_object (fresh st))) /\
    state_invariant BR'
        (J.state_next_fresh (jst \(fresh jst := J.env_record_decl J.decl_env_record_empty))) 
        (st \(fresh st := obj)).
Proof.
    introv Hlred Hcinv Hinv Hucinv Hbinds Hvrel.
    asserts Hsub : (BR \c (\{fact_js_env (fresh jst) (fresh st)} \u BR)). jauto_js.
    lets Hlerel : usercode_context_invariant_lexical_env_related Hucinv Hbinds.
    forwards_th Hx : only_state_invariant_new_env_record_decl_lemma. destruct_hyp Hx.
    do 2 eexists; splits; try reflexivity; try eassumption.
    lets Hincl : context_invariant_bisim_includes_init Hcinv.
    eapply usercode_context_invariant_restore_lemma; eauto_js.
Qed.

(* TODO: move to TLC LibLogic *)
Lemma case_classic_l_eq : forall P Q, (P \/ (~ P /\ Q)) = (P \/ Q).
Proof.
    introv. rew_logic. split.
    + iauto.
    + auto using case_classic_l.
Qed.

Lemma case_classic_r_eq : forall P Q, (Q \/ (P /\ ~ Q)) = (P \/ Q).
Proof.
    introv. rew_logic. split.
    + iauto.
    + auto using case_classic_r.
Qed.

(* TODO move *)
Lemma js_prog_intro_eta : forall p, J.prog_intro (J.prog_intro_strictness p) (J.prog_elements p) = p.
Proof.
    introv. destruct p. reflexivity.
Qed.

(* TODO move *)
Lemma array_idx_lemma : forall BR k jst jc c st st' ptr jvs vs s k' r,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privArrayIdx [L.value_object ptr; L.value_string s])
        (L.out_ter st' r) ->
    s = string_of_nat k' ->
    fact_iarray ptr vs \in BR ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    state_invariant BR jst st' /\
    st = st' /\ 
    exists jv v,
    r = L.res_value v /\
    value_related BR jv v /\
    (k' >= length vs /\ jv = J.value_prim J.prim_undef /\ v = L.value_undefined \/ Nth k' jvs jv /\ Nth k' vs v).
Proof.
Admitted. (* TODO *)

Lemma values_related_length_lemma : forall BR jvs vs,
    values_related BR jvs vs ->
    length jvs = length vs.
Proof.
    introv Hvrel.
    inductions Hvrel. { reflexivity. } {
        rew_length. rewrite IHHvrel. reflexivity.
    }
Qed.

(* TODO move *)
Lemma red_spec_creating_function_object_ok : forall BR k jst jc c' c st st' r is s jp jle,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privMakeFunctionObject 
            [L.value_closure (funcbody_closure (to_list c) is jp); L.value_number (length is); L.value_string s; 
             L.value_bool (J.prog_intro_strictness jp)])
        (L.out_ter st' r) ->
    context_invariant BR jc c' ->
    state_invariant BR jst st ->
    (forall v, binds c "$context" v -> lexical_env_related BR jle v) ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_creating_function_object is (J.funcbody_intro jp s) jle (J.prog_intro_strictness jp)) 
        (fun jv => exists jptr, jv = J.value_object jptr).
Proof.
    introv Hlred Hcinv Hinv Himpl.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : add_data_field_lemma. prove_bag.
    destruct_hyp Hx.
    repeat ljs_autoforward.
    sets_eq b : (J.prog_intro_strictness jp).
(*
    destruct b. { (* strict *)
        repeat ljs_autoforward.
        skip. (* TODO *)
    } { (* not strict *)
        repeat ljs_autoforward.
        skip. (* TODO *)
    }
*)
Admitted. (* TODO *)

(* TODO move to ejs *)
Lemma exprjs_prog_strictness_eq : forall jp, E.prog_strictness (E.js_prog_to_ejs jp) = J.prog_intro_strictness jp.
Proof.
    introv. destruct jp. reflexivity.
Qed.

(* TODO move *)
Ltac determine_fact_js_obj :=
    match goal with
    | Hfact1 : fact_js_obj ?jptr ?ptr1 \in ?BR1, Hfact2 : fact_js_obj ?jptr ?ptr2 \in ?BR2,
      Hinv : state_invariant ?BR _ _ |- _ =>
        let Hsub1 := fresh in let Hsub2 := fresh in let Heq := fresh "Heq" in 
        asserts Hsub1 : (BR1 \c BR); [prove_bag | idtac];
        asserts Hsub2 : (BR2 \c BR); [prove_bag | idtac];
        lets Heq : heaps_bisim_consistent_lfun_obj (state_invariant_heaps_bisim_consistent Hinv) 
            (incl_in Hsub1 Hfact1) (incl_in Hsub2 Hfact2);
        clear Hsub1; clear Hsub2; try (subst_hyp Heq; clear Hfact2)
    end.

Ltac determine_fact_js_env :=
    match goal with
    | Hfact1 : fact_js_env ?jptr ?ptr1 \in ?BR1, Hfact2 : fact_js_env ?jptr ?ptr2 \in ?BR2,
      Hinv : state_invariant ?BR _ _ |- _ =>
        let Hsub1 := fresh in let Hsub2 := fresh in let Heq := fresh "Heq" in 
        asserts Hsub1 : (BR1 \c BR); [prove_bag | idtac];
        asserts Hsub2 : (BR2 \c BR); [prove_bag | idtac];
        lets Heq : heaps_bisim_consistent_lfun_env (state_invariant_heaps_bisim_consistent Hinv) 
            (incl_in Hsub1 Hfact1) (incl_in Hsub2 Hfact2);
        clear Hsub1; clear Hsub2; try (subst_hyp Heq; clear Hfact2)
    end.

Lemma create_arguments_object_ok : forall BR k jst jc c st st' r jptr ptr ptr1 ptr2(*ptr3*)is jvs vs jeptr jlenv v b,
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privmkArgsObj
        [L.value_object ptr2; L.value_null(*object ptr3*); L.value_object ptr1; L.value_object ptr; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    lexical_env_related BR jlenv v ->
    fact_js_obj jptr ptr \in BR ->
    fact_iarray ptr1 vs \in BR ->
(*     fact_iarray ptr3 (map L.value_string is) \in BR -> TODO non-strict args obj *)
    fact_js_env jeptr ptr2 \in BR ->
    fact_ctx_parent ptr2 v \in BR ->
    concl_ext_expr_value BR jst jc c st st' r
        (J.spec_create_arguments_object jptr is jvs (jeptr::jlenv) b) 
        (fun jv => exists ptr0, jv = J.value_object ptr0).
Proof.
Admitted. (* TODO *)

(* TODO move *)
Hint Constructors J.red_prog : js_ljs.

Hint Extern 1 (J.red_prog _ _ (J.prog_1 _ _) _) => eapply J.red_prog_1_stat : js_ljs. 
Hint Extern 50 => progress unfolds J.res_overwrite_value_if_empty : js_ljs.

Lemma prog_els_last_lemma : forall el els,
    E.expr_seqs (List.map E.js_element_to_ejs (els & el)) = 
        E.expr_seq (E.expr_seqs (List.map E.js_element_to_ejs els)) (E.js_element_to_ejs el).
Proof.
    introv.
    unfolds E.expr_seqs.
    rewrite_all list_map_tlc.
    rew_list.
    reflexivity.
Qed.

Lemma prog_ok_lemma : forall els BR k jst jc c st st' r b,
    ih_stat k ->
    L.red_exprh k c st (L.expr_basic (E.ejs_to_ljs (E.expr_seqs (List.map E.js_element_to_ejs els))))
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' jst' jr,
    J.red_prog jst jc (J.prog_basic (J.prog_intro b els)) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.
Proof.
    induction els as [|el els] using list_rev_ind;
    introv IHt Hlred Hcinv Hinv. { (* no more elements *)
        repeat ljs_autoforward.
        jauto_js.
    } (* one element more *)
    rewrite prog_els_last_lemma in Hlred.
    repeat ljs_autoforward.
    specializes IHels (ih_stat_S IHt).
    specializes_th IHels.
    destruct_hyp IHels. res_related_abort; try ljs_handle_abort. (* TODO destr_concl_auto *)
    repeat ljs_autoforward.
    destruct el. { (* statement *)
        repeat ljs_autoforward.
        destr_concl.
        res_related_invert; repeat ljs_autoforward; try resvalue_related_only_invert; jauto_js. 
    } { (* funcdecl *)
        destruct f. (* TODO remove *)
        repeat ljs_autoforward.
        jauto_js.
    }
Qed.

Lemma prog_ok_call_lemma : forall BR k jst jc c st st' r jp,
    ih_stat k ->
    L.red_exprh k c st 
        (L.expr_basic (E.ejs_to_ljs (E.expr_seqs (List.map E.js_element_to_ejs (J.prog_elements jp)))))
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    exists BR' jst' jr,
    J.red_prog jst jc (J.prog_basic jp) (J.out_ter jst' jr) /\ 
    state_invariant BR' jst' st' /\
    BR \c BR' /\
    res_related BR' jst' st' jr r.
Proof.
    intros. destruct jp. eapply prog_ok_lemma; eassumption.
Qed.

Definition post_to_primitive jv jv' := 
    exists jp', jv' = J.value_prim jp' /\ forall jp, jv = J.value_prim jp -> jp = jp'.

Lemma post_to_primitive_lemma1 : forall jv1 jv2, post_to_primitive jv1 jv2 -> exists jpr, jv2 = J.value_prim jpr.
Proof.
    introv Hpp. unfold post_to_primitive in Hpp. destruct_hyp Hpp. eauto.
Qed.

Lemma post_to_primitive_lemma2 : forall jpr jv, 
    post_to_primitive (J.value_prim jpr) jv -> jv = J.value_prim jpr.
Proof.
    introv Hpp. unfold post_to_primitive in Hpp. destruct_hyp Hpp. 
    eapply func_eq_1. symmetry. eauto.
Qed.

Ltac js_post_to_primitive :=
    match goal with
    | H : post_to_primitive (J.value_prim ?jpr) ?jv |- _ =>
        match jv with
        | J.value_prim jpr => fail 1
        | _ => let H1 := fresh in lets H1 : post_to_primitive_lemma2 H; destruct_hyp H1
        end
    | H : post_to_primitive ?jv1 ?jv2 |- _ =>
        match jv2 with
        | J.value_prim _ => fail 1
        | _ => let H1 := fresh in lets H1 : post_to_primitive_lemma1 H; destruct_hyp H1
        end
    end.

Lemma red_spec_to_primitive_ok : forall BR k jst jc c st st' jv v jprefo r s,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitiveHint [v; L.value_string s])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    option_preftype_name jprefo s ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_to_primitive jv jprefo) (post_to_primitive jv).
Proof.
    (* TODO *)
Admitted.

Lemma red_spec_to_primitive_ok_default : forall BR k jst jc c st st' jv v r,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitive [v])
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    value_related BR jv v ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_to_primitive jv None) (post_to_primitive jv).
Proof.
    introv Hlred Hcinv Hinv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th Hx : red_spec_to_primitive_ok. eapply option_preftype_name_none.
    assumption.
Qed.

(** *** spec_expr_get_value_conv spec_to_boolean 
    It corresponds to [to_bool] in the desugaring. *)

Lemma red_spec_to_boolean_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToBoolean J.spec_to_boolean 
        (fun jv => exists b, jv = J.value_prim (J.prim_bool b)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.

    ljs_apply.

    repeat ljs_autoforward. 

    inverts Hvrel; try injects; jauto_js.
Qed.

(* TODO move *)
Lemma to_primitive_primitive_noop_lemma : forall k c st st' r v s,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privToPrimitiveHint [v; L.value_string s])
        (L.out_ter st' r) ->
    L.is_primitive v ->
    st = st' /\ r = L.res_value v.
Proof.
    introv Hlred Hprim.
    inverts red_exprh Hlred.
    ljs_apply.
    repeat ljs_autoforward.
    cases_decide as Hisobj. {
        inverts Hisobj; inverts Hprim.
    }
    repeat ljs_autoforward.
    eauto.
Qed.

Lemma convert_prim_to_number_lemma : forall BR jpv v,
    value_related BR (J.value_prim jpv) v ->
    L.value_to_num_cast v = J.convert_prim_to_number jpv.
Proof.
    introv Hvrel.
    inverts Hvrel; reflexivity.
Qed.

Lemma red_spec_to_number_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToNumber J.spec_to_number
        (fun jv => exists n, jv = J.value_prim (J.prim_number n)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct (classic (L.is_primitive v0)) as [Hprim|Hprim]. {
        forwards_th Hx : to_primitive_primitive_noop_lemma. { eassumption. }
        destruct_hyp Hx.
        repeat ljs_autoforward.
        forwards Hx : value_related_primitive_lemma Hprim Hvrel.
        destruct_hyp Hx.
        erewrite convert_prim_to_number_lemma by eassumption.
        jauto_js.
    } 
    forwards_th Hx : red_spec_to_primitive_ok. {
        eapply option_preftype_name_some. eapply preftype_name_number.
    }
    inverts Hvrel; try solve [false; eauto_js].
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    js_post_to_primitive.
    resvalue_related_only_invert.
    erewrite convert_prim_to_number_lemma by eassumption.
    jauto_js.
Qed.

Lemma convert_prim_to_string_lemma : forall BR jpv v,
    value_related BR (J.value_prim jpv) v ->
    L.value_to_str_cast v = J.convert_prim_to_string jpv.
Proof.
    introv Hvrel.
    inverts Hvrel; reflexivity.
Qed.

Lemma red_spec_to_string_unary_ok : forall k,
    th_ext_expr_unary k LjsInitEnv.privToString J.spec_to_string
        (fun jv => exists n, jv = J.value_prim (J.prim_string n)).
Proof.
    introv Hcinv Hinv Hvrel Hlred.
    inverts red_exprh Hlred; tryfalse.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    destruct (classic (L.is_primitive v0)) as [Hprim|Hprim]. {
        forwards_th Hx : to_primitive_primitive_noop_lemma. { eassumption. }
        destruct_hyp Hx.
        repeat ljs_autoforward.
        forwards Hx : value_related_primitive_lemma Hprim Hvrel.
        destruct_hyp Hx.
        erewrite convert_prim_to_string_lemma by eassumption.
        jauto_js.
    } 
    forwards_th Hx : red_spec_to_primitive_ok. {
        eapply option_preftype_name_some. eapply preftype_name_string.
    }
    inverts Hvrel; try solve [false; eauto_js].
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    match goal with H : post_to_primitive _ _ |- _ => unfold post_to_primitive in H; destruct_hyp H end. (* TODO *)
    resvalue_related_only_invert.
    erewrite convert_prim_to_string_lemma by eassumption.
    jauto_js.
Qed.

Lemma red_spec_to_boolean_ok : forall k je, 
    ih_expr k ->
    th_spec k (E.to_bool (js_expr_to_ljs je))
              (J.spec_expr_get_value_conv J.spec_to_boolean je) 
              (fun _ _ _ _ _ r jv => exists b, jv = J.value_prim (J.prim_bool b) /\ 
                  r = L.res_value (L.value_bool b)).
Proof.
    introv IHe Hcinv Hinv Hlred.
    repeat ljs_autoforward.

    destr_concl; try ljs_handle_abort.

    repeat inv_internal_fwd_ljs.
    forwards_th : red_spec_to_boolean_unary_ok.

    destr_concl.
    res_related_invert.
    resvalue_related_invert. 
    jauto_js 6.
    jauto_js 6.
Qed.

Lemma construct_related_lemma : forall BR jst st jptr ptr obj v,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    binds (LjsSyntax.object_internal obj) "construct" v ->
    exists jcon,
    construct_related jcon v.
Proof.
    introv Hinv Hbs Hbinds Hcbinds.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    erewrite read_option_binds_inv in object_prim_related_construct by eassumption.
    inverts object_prim_related_construct.
    jauto.
Qed.

Lemma object_method_construct_lemma : forall BR jst st jptr ptr obj jcon,
    state_invariant BR jst st ->
    fact_js_obj jptr ptr \in BR ->
    binds st ptr obj ->
    option_construct_related jcon (L.object_internal obj\("construct"?)) ->
    J.object_method J.object_construct_ jst jptr jcon.
Proof.
    introv Hinv Hbs Hbinds Hocrel.
    lets Hx : state_invariant_bisim_obj_lemma Hinv Hbs Hbinds.
    destruct Hx as (?jobj&Hjbinds&Horel).
    destruct Horel.
    destruct object_related_prim.
    inverts Hocrel as Ho1 Ho2. {
        rewrite <- Ho2 in object_prim_related_construct.
        inverts object_prim_related_construct as Hp1 Hp2.
        asserts Heq : (a = a0). { (* TODO determinism lemma *)
            inverts Ho1 as Ho3; inverts Hp1 as Hp3; try reflexivity;
            try inverts Ho3; try inverts Hp3; reflexivity.
        }
        subst_hyp Heq.
        unfolds. jauto.
    }
    rewrite <- Ho1 in object_prim_related_construct.
    inverts object_prim_related_construct.
    unfolds. jauto.
Qed.

Lemma red_spec_construct_prealloc_ok : forall k jpre, th_construct_prealloc k jpre.
Proof.
    introv Hcinv Hinv Hvrels Halo Hcpre Hlred.
    inverts Hcpre.
Admitted.

Lemma red_spec_construct_ok : forall BR k jst jc c st st' ptr ptr1 vs r jptr jvs,
    ih_call k ->
    L.red_exprh k c st 
        (L.expr_app_2 LjsInitEnv.privrunConstruct [L.value_object ptr; L.value_object ptr1]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    concl_ext_expr_value BR jst jc c st st' r (J.spec_construct jptr jvs) (fun jv => True).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrels Halo Hbs.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards Hx : construct_related_lemma Hinv Hbs; try eassumption. 
    destruct Hx as (jcon&Hcrel).
    forwards Hmeth : object_method_construct_lemma; try eassumption. eauto_js 7.
    inverts Hcrel. { (* prealloc *)
        lets Hx : red_spec_construct_prealloc_ok ___.
        specializes_th Hx; try eassumption.
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* default *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        forwards_th : get_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        skip. (* TODO *)
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.

(* TODO lots of cleaning up needed! *)

Lemma ref_base_type_obj_not_unresolvable jref :
    ref_base_type_obj (J.ref_base jref) -> ~J.ref_is_unresolvable jref.
Proof.
    introv Hrbt Hjru. destruct jref. inverts Hrbt as Hoc. simpls. substs. 
    inverts Hoc. unfolds J.ref_is_unresolvable. unfolds J.ref_kind_of. 
    destruct jv; simpls; tryfalse. destruct p; tryfalse.
Qed.

Lemma js_not_identifier_not_unresolvable : forall je jref,
    js_reference_type je (J.ref_base jref) -> (forall s, je <> J.expr_identifier s) -> ~J.ref_is_unresolvable jref.
Proof.
    introv Hrt Hne.
    eapply ref_base_type_obj_not_unresolvable.
    inverts Hrt; try eassumption. 
    specializes Hne s. false.
Qed.

Lemma red_spec_lexical_env_get_identifier_ref_lemma : forall k BR jst jc c st st' r v s b v1 jlenv,
    L.red_exprh k c st
        (L.expr_app_2 LjsInitEnv.privEnvGetId [v; L.value_string s; v1]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    lexical_env_related BR jlenv v -> 
    exists BR' jst' jsr,
    J.red_spec jst jc (J.spec_lexical_env_get_identifier_ref jlenv s b) jsr /\
    js_specret_state jsr jst' /\
    ((exists k' c' v' jrbt st'',
      jsr = J.specret_val jst' (J.ref_intro jrbt s b) /\
      L.red_exprh k' c' st'' (L.expr_app_2 v1 [v']) (L.out_ter st' r) /\ 
      state_invariant BR' jst' st'' /\
      ref_base_type_related BR' jrbt v' /\
      ref_base_type_var jrbt /\
      k' < k /\
      BR \c BR') \/ 
     (exists jr,
      jsr = J.specret_out (J.out_ter jst' jr) /\
      J.abort (J.out_ter jst' jr) /\ J.res_type jr = J.restype_throw /\ 
      state_invariant BR' jst' st' /\
      res_related BR' jst' st' jr r /\ BR \c BR')).
Proof.
    intro k.
    induction_wf IH : lt_wf k.
    introv Hlred Hcinv Hinv Hlrel.
    ljs_invert_apply.
    inverts Hlrel as Hlrel1 Hlrel2 Hlrel3. {
        repeat ljs_autoforward.
        jauto_js. 
    }
    repeat ljs_autoforward.
    forwards (jer&Hjbinds&Herel) : env_record_related_lookup_lemma Hinv Hlrel1. eassumption.
    inverts Herel as Herel. {
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Hidx; repeat ljs_autoforward. { (* var found *)
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            jauto_js 8.
        } { (* not found *)
            erewrite <- decl_env_record_vars_related_index_lemma in Hidx by eassumption.
            rewrite <- decl_env_record_indom_to_libbag in Hidx. (* TODO can be removed somehow? *)
            lets Hp : state_invariant_ctx_parent_ok Hinv Hlrel2.
            destruct_hyp Hp. repeat binds_determine.
            specializes IH ___; try eassumption. math.
            destruct_hyp IH; try ljs_handle_abort.
            jauto_js 20.
        }
    } {
        inverts Herel.
        unfolds L.object_class.
        cases_decide as Heq; rewrite stx_eq_string_eq_lemma in Heq; tryfalse.
        repeat ljs_autoforward.
        cases_decide as Heq1; rewrite stx_eq_string_eq_lemma in Heq1; tryfalse.
        repeat ljs_autoforward.
        forwards_th : has_property_lemma. eassumption.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_invert.
        inv_ljs. { (* var found *)
            repeat ljs_autoforward.
            jauto_js 8.
        } { (* not found *)
            repeat ljs_autoforward.
            lets Hp : state_invariant_ctx_parent_ok ___. eassumption.
            unfolds in Hp. specializes Hp ___. eauto_js.
            destruct_hyp Hp. repeat binds_determine.
            specializes IH ___; try eassumption. math. eauto_js. eauto_js.
            destruct_hyp IH; try ljs_handle_abort. jauto_js 8.
        }
    }
Qed.

(* TODO more things to sort *)

Lemma reference_match_lemma : forall (A : Type) (P : A -> Prop) ee f1 f2 f3,
    P (E.reference_match ee f1 f2 f3) ->
    (exists ee1 ee2, ee = E.expr_get_field ee1 ee2 /\ P (f1 ee1 ee2)) \/
    (exists s, ee = E.expr_var_id s /\ P (f2 s)) \/
    (~ejs_reference_producing ee /\ P (f3 ee)).
Proof.
    destruct ee; eauto.
Qed.

Definition exprjs_red_p k c st o e := L.red_exprh k c st (L.expr_basic e) o.

Lemma reference_match_red_exprh_lemma : forall k c st o ee f1 f2 f3,
    L.red_exprh k c st (L.expr_basic (E.reference_match ee f1 f2 f3)) o ->
    (exists ee1 ee2, ee = E.expr_get_field ee1 ee2 /\ L.red_exprh k c st (L.expr_basic (f1 ee1 ee2)) o) \/
    (exists s, ee = E.expr_var_id s /\ L.red_exprh k c st (L.expr_basic (f2 s)) o) \/
    (~ejs_reference_producing ee /\ L.red_exprh k c st (L.expr_basic (f3 ee)) o).
Proof.
    introv Hlred.
    applys reference_match_lemma (exprjs_red_p k c st o) Hlred.
Qed.

Inductive js_field_access : J.expr -> E.expr -> E.expr -> Prop :=
| js_field_access_access : forall je1 je2,
    js_field_access (J.expr_access je1 je2) (E.js_expr_to_ejs je1) (E.js_expr_to_ejs je2)
| js_field_access_member : forall je1 s,
    js_field_access (J.expr_member je1 s) (E.js_expr_to_ejs je1) (E.expr_string s).

Lemma js_field_access_reference_producing : forall je ee1 ee2,
    js_field_access je ee1 ee2 -> js_reference_producing je.
Proof.
    introv jsfe. inverts jsfe; eauto_js.
Qed.

Hint Constructors js_field_access : js_ljs.
Hint Resolve js_field_access_reference_producing : js_ljs.

Lemma reference_match_red_exprh_js_lemma : forall k c st o je f1 f2 f3,
    L.red_exprh k c st (L.expr_basic (E.reference_match (E.js_expr_to_ejs je) f1 f2 f3)) o ->
    (exists ee1 ee2, js_reference_producing je /\ js_field_access je ee1 ee2 /\ 
        L.red_exprh k c st (L.expr_basic (f1 ee1 ee2)) o) \/
    (exists s, js_reference_producing je /\ je = J.expr_identifier s /\ 
        L.red_exprh k c st (L.expr_basic (f2 s)) o) \/
    (~js_reference_producing je /\ L.red_exprh k c st (L.expr_basic (f3 (E.js_expr_to_ejs je))) o).
Proof.
    introv Hlred.
    lets Hx : reference_match_red_exprh_lemma Hlred.
    destruct je; try destruct l; try destruct b; try destruct f; destruct_hyp Hx; tryfalse;
    try match goal with H : ~ejs_reference_producing _ |- _ => false; apply H; solve [eauto_js 10] end;
    eauto_js 9. 
Qed.

Ltac reference_match_cases Hlred Hx Heq Hrp :=
    lets Hx : (reference_match_red_exprh_js_lemma _ _ _ _ Hlred);
    clear Hlred;
    destruct Hx as [(?ee&?ee&Hrp&Heq&Hlred)|[(?s&Hrp&Heq&Hlred)|(Hrp&Hx)]]; try subst_hyp Heq.

(* TODO move *)
Lemma js_red_expr_getvalue_not_ref_lemma : forall jst jc je jo jo',
    ~js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_out jo') ->
    jo = jo'.
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto.
Qed.

Lemma js_red_expr_getvalue_not_ref_lemma2 : forall jst jst' jc je jo jv,
    ~js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_val jst' jv) ->
    jo = J.out_ter jst' (J.res_normal (J.resvalue_value jv)).
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto.
Qed.

Lemma js_red_expr_getvalue_ref_lemma : forall jst jc je jo jo',
    js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_out jo') ->
    jo = jo' \/ exists jst' jref, jo = J.out_ter jst' (J.res_ref jref) /\
        J.red_spec jst' jc (J.spec_get_value (J.resvalue_ref jref)) (@J.specret_out J.value jo').
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    auto. eauto_js.
Qed.

Lemma js_red_expr_getvalue_ref_lemma2 : forall jst jst' jc je jo jv,
    js_reference_producing je ->
    js_red_expr_getvalue jst jc je jo (J.specret_val jst' jv) ->
    exists jref jst'', jo = J.out_ter jst'' (J.res_ref jref) /\
        J.red_spec jst'' jc (J.spec_get_value (J.resvalue_ref jref)) (J.specret_val jst' jv).
Proof.
    introv Hnrp Hgv.
    destruct Hgv.
    inverts js_red_expr_getvalue_red_spec; tryfalse.
    jauto_js.
Qed.

Ltac js_red_expr_getvalue_fwd :=
    match goal with
    | Hnrp : ~js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_out _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_not_ref_lemma Hnrp Hgv;
        subst_hyp H
    | Hnrp : ~js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_val _ _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_not_ref_lemma2 Hnrp Hgv;
        subst_hyp H
    | Hnrp : js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_out _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_ref_lemma Hnrp Hgv;
        destruct_hyp H
    | Hnrp : js_reference_producing ?je, Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo (J.specret_val _ _) |- _ =>
        let H := fresh in
        lets H : js_red_expr_getvalue_ref_lemma2 Hnrp Hgv;
        destruct_hyp H
    end.

(* Hint Resolve js_red_expr_getvalue_red_expr : js_ljs. *)
Ltac js_red_expr_getvalue_hint :=
    match goal with
    | Hgv : js_red_expr_getvalue ?jst ?jc ?je ?jo _
        |- J.red_expr ?jst ?jc (J.expr_basic ?je) _ =>
        applys js_red_expr_getvalue_red_expr Hgv
    end.

Hint Extern 5 (J.red_expr ?jst ?jc (J.expr_basic _) _) => js_red_expr_getvalue_hint : js_ljs.

Lemma js_field_access_not_unresolvable_lemma : forall jc jst jst' je ee1 ee2 jref jsr,
    js_field_access je ee1 ee2 ->
    js_red_expr_getvalue jst jc je (J.out_ter jst' (J.res_normal (J.resvalue_ref jref))) jsr ->
    ~J.ref_is_unresolvable jref.
Proof.
    introv Hjfa Hgv.
    inverts Hgv as Hxx Hgva.
    inverts Hgva as Ha Hb Hc. {
        inverts Ha as Hx. false. eauto_js.
    }
    applys js_not_identifier_not_unresolvable Hb.
    destruct Hjfa; eauto.
Qed.

Hint Resolve js_field_access_not_unresolvable_lemma : js_ljs.

Ltac ref_base_type_var_invert :=
    match goal with
    | H1 : ref_base_type_var ?jrbt, H2 : ref_base_type_related _ ?jrbt _ |- _ =>
        inverts H1; inverts H2;
        try match goal with
        | H3 : js_object_coercible (J.value_prim J.prim_undef) |- _ => solve [inverts H3; tryfalse]
        | _ => idtac
        end
    end.

(* ** Reference handling *)

(* TODO why get_value is an ext_spec, and put_value is ext_expr? *)
Lemma env_get_value_lemma : forall BR k jst jc c st st' r v s b jrbt,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvGetValue 
        [v; L.value_string s; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    ref_base_type_related BR jrbt v ->
    ref_base_type_var jrbt ->
    concl_spec BR jst jc c st st' r 
        (J.spec_get_value (J.resvalue_ref (J.ref_intro jrbt s b))) 
        (fun BR' _ jv => 
            v <> L.value_null /\
            exists v', r = L.res_value v' /\ value_related BR' jv v' ).
Proof.
    introv IHc Hlred Hcinv Hinv Hrbt Hrbtv.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply.
    ref_base_type_var_invert. {
        repeat ljs_autoforward.
        forwards_th Hx : unbound_id_lemma.
        destr_concl; tryfalse; try ljs_handle_abort.
    }
    repeat ljs_autoforward.
    forwards_th : get_binding_value_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    jauto_js 15.
Qed.

Lemma env_put_value_lemma : forall BR k jst jc c st st' r v v' s b jrbt jv,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvPutValue 
        [v; L.value_string s; v'; L.value_bool b]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    ref_base_type_related BR jrbt v ->
    ref_base_type_var jrbt ->
    value_related BR jv v' ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_put_value (J.resvalue_ref (J.ref_intro jrbt s b)) jv) 
            (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hrbt Hrbtv Hvrel.
    inverts red_exprh Hlred.
    ljs_apply.
    ljs_context_invariant_after_apply. 
    ref_base_type_var_invert. {
        repeat ljs_autoforward.
        destruct b. { (* strict *)
            repeat ljs_autoforward.
            forwards_th Hx : unbound_id_lemma. 
            destr_concl; tryfalse.
            ljs_handle_abort.
        } { (* nonstrict *)
            repeat ljs_autoforward.
            forwards : context_invariant_prealloc_lemma Hcinv prealloc_related_global.
            forwards_th : put_lemma. prove_bag.
            destr_concl; try ljs_handle_abort.
            res_related_invert.
            resvalue_related_only_invert.
            repeat ljs_autoforward.
            jauto_js.
        }
    }
    repeat ljs_autoforward.
    forwards_th : set_mutable_binding_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    jauto_js 15.
Qed.
