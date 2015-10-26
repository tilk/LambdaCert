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
