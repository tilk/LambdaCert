Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Export LjsPrettyRulesIndexedInvert.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

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
Implicit Type jder : J.decl_env_record.
Implicit Type jprops : J.object_properties_type.

Fixpoint suffixes T (l : list T) :=
    match l with
    | nil => nil
    | h::t => l::suffixes t
    end.

Definition head_not_in_tail T (l : list T) := 
    match l with
    | [] => True
    | h::t => ~Mem h t
    end.

Definition all_different T (l : list T) := Forall (@head_not_in_tail T) (suffixes l).

Lemma Mem_map_lemma : forall A B a (l : list A) (f : A -> B),
    Mem a l -> Mem (f a) (map f l).
Proof.
    hint Mem_here, Mem_next.
    introv Hmem. induction Hmem; rew_map; iauto.
Qed.

Lemma all_different_mem_assoc : forall A B (a:A) (b:B) l,
    all_different (map fst l) ->
    Mem (a, b) l ->
    Assoc a b l.
Proof.
    introv Had Hmem.
    induction l as [|(a'&b') l].
    + inverts Hmem.
    + inverts Hmem as Hmem.
      - eapply Assoc_here.
      - rew_map in Had. inverts Had as Hhn Had. simpl in Hhn.
        specializes IHl Had Hmem.
        asserts Hamem : (Mem (fst (a,b)) (map fst l)). { applys~ Mem_map_lemma. } simpl in Hamem.
        destruct (classic (a = a')) as [HEq|HEq]. 
        * subst a. tryfalse.
        * applys~ Assoc_next.
Qed.

Fixpoint nats k :=
    match k with
    | S k' => k'::nats k'
    | 0 => nil
    end.

Definition nats_asc k := rev (nats k).

Lemma store_items_is_nats_list : exists k, map fst LjsInitEnv.store_items = nats_asc k.
Proof.
    sets_eq l : (map fst LjsInitEnv.store_items).
    unfolds LjsInitEnv.store_items.
    rewrite <- list_map_tlc in EQl.
    simpl in EQl.
    exists (S (List.last l 0)).
    substs. reflexivity.
Qed.

Lemma nats_less : forall k k', Mem k (nats k') -> (k < k')%nat.
Proof.
    introv H. inductions H; destruct k'; tryfalse; injects.
    + math.
    + specializes IHMem ___. reflexivity. math. 
Qed.

Lemma all_different_nats : forall k, all_different (nats k).
Proof.
    induction k.
    + eapply Forall_nil.
    + simpl. eapply Forall_cons.
      - applys contrapose_intro nats_less. math.
      - assumption.
Qed.

Lemma Mem_last_eq : forall A (x y:A) l,
    Mem x (l&y) = ((x = y) \/ (Mem x l)).
Proof.
    introv. rewrite Mem_app_or_eq.
    asserts_rewrite (Mem x [y] = (x=y)). {
        rewrite Mem_cons_eq. rewrite Mem_nil_eq. extens. iff*.
    }
    extens. iff*.
Qed.

Lemma Mem_last_cons : forall A (x y:A) l, Mem x (l&y) = Mem x (y::l).
Proof.
    introv. rewrite Mem_last_eq. rewrite Mem_cons_eq. reflexivity.
Qed.

Lemma head_not_in_tail_last : forall T x y (l : list T),
    x <> y -> head_not_in_tail (x :: l) -> head_not_in_tail (x :: l & y).
Proof.
    introv Hdiff. eapply contrapose_intro. rewrite Mem_last_cons. intro H.
    inverts* H.
Qed.

Lemma all_different_last : forall T x (l : list T), 
    all_different l -> head_not_in_tail (x :: l) -> all_different (l & x).
Proof.
    introv Had Hht.
    induction l.
    + applys~ Forall_cons.
    + inverts Had as Hnt Had. 
      specializes IHl Had __. applys contrapose_intro Mem_next Hht.
      rew_list. applys~ Forall_cons.
      applys~ head_not_in_tail_last. applys contrapose_intro Hht. intro. substs. apply Mem_here.
Qed.

Lemma all_different_rev : forall T (l : list T), all_different l -> all_different (rev l).
Proof.
    introv Had.
    induction l as [|x l]; rew_rev.
    + assumption.
    + inverts Had as Hnt Had. specializes IHl Had.
      applys~ all_different_last. applys contrapose_intro Hnt.
      intro H. apply Mem_rev in H. rew_rev in H. assumption.
Qed. 

Lemma all_different_nats_asc : forall k, all_different (nats_asc k).
Proof.
    introv. unfolds nats_asc. applys all_different_rev. applys all_different_nats.
Qed.

Lemma all_different_store_items :
    all_different (map fst LjsInitEnv.store_items).
Proof.
    lets H : store_items_is_nats_list.
    destruct H as (?&H). rewrite H.
    apply all_different_nats_asc.
Qed.

Lemma init_store_mem_binds : forall k obj,
    Mem (k, obj) LjsInitEnv.store_items ->
    binds LjsInitEnv.init_store k obj.
Proof.
    introv Hmem.
    eapply from_list_binds_inv.
    applys~ all_different_mem_assoc. apply all_different_store_items.
Qed.


Definition ljs_prealloc_call_object code n := {|
    L.object_attrs := {|
        L.oattrs_proto := LjsInitEnv.privFunctionProto;
        L.oattrs_class := "Function";
        L.oattrs_extensible := true;
        L.oattrs_code := code |};
    L.object_properties := from_list [("length", L.attributes_data_of (L.attributes_data_intro (L.value_number n) false false false))];
    L.object_internal := from_list []
|}.

(* TODO *)
Lemma object_create_prealloc_call_lemma : forall jpre code n,
    call_related (JsSyntax.call_prealloc jpre) code ->
    object_related initBR 
        (JsInit.object_create_prealloc_call jpre (J.value_prim (J.prim_number n)) J.Heap.empty) 
        (ljs_prealloc_call_object code n).
Proof.
    introv Hcode.
    constructor.
    + constructor; try solve [constructor || reflexivity || 
         (simpl; rewrite from_list_empty; erewrite read_option_not_index_inv by prove_bag; constructor)].
      - constructor. eapply prealloc_initBR_lemma. eauto_js.
      - constructor. assumption.
    + unfolds. intro.
      destruct (classic (s = "length")) as [Heq|Heq].
Opaque index. 
      - substs. right. simpl. do 2 eexists. rewrite from_list_update. rewrite from_list_empty. 
        rew_heap_to_libbag. rew_binds_eq. eauto_js 10.
      - left. simpl. rewrite from_list_update. rewrite from_list_empty.
        rew_heap_to_libbag. rew_index_eq.  eauto_js 10.
Qed.

Definition ljs_prealloc_constructor_object code1 code2 attrs := {|
    L.object_attrs := {|
        L.oattrs_proto := LjsInitEnv.privFunctionProto;
        L.oattrs_class := "Function";
        L.oattrs_extensible := true;
        L.oattrs_code := code2 |};
    L.object_properties := attrs;
    L.object_internal := from_list [("construct", code1); ("hasinstance", LjsInitEnv.privHasInstanceDefault)]
|}.

Lemma object_create_prealloc_constructor_lemma : forall jattrs attrs jpre code1 code2 n,
    object_properties_related initBR 
        (jattrs \("length" := J.attributes_data_of (JsInit.attrib_constant (J.value_prim (J.prim_number n))))) 
        attrs ->
    call_related (JsSyntax.call_prealloc jpre) code2 ->
    construct_related (JsSyntax.construct_prealloc jpre) code1 ->
    object_related initBR
        (JsInit.object_create_prealloc_constructor jpre (J.value_prim (J.prim_number n)) jattrs)
        (ljs_prealloc_constructor_object code1 code2 attrs).
Proof.
    introv Hprel Hcrel Hcorel.
    constructor.
    + constructor; try solve [constructor || reflexivity || 
         (simpl; repeat rewrite from_list_update; rewrite from_list_empty; 
          erewrite read_option_not_index_inv by (rew_index_eq; rew_logic; eauto); constructor)].
      - constructor. eapply prealloc_initBR_lemma. eauto_js.
      - constructor. assumption.
      - simpl. repeat rewrite from_list_update. rewrite from_list_empty.
        erewrite read_option_binds_inv by prove_bag. constructor. eassumption.
      - simpl. repeat rewrite from_list_update. rewrite from_list_empty.
        erewrite read_option_binds_inv by prove_bag. constructor. constructor.
    + simpl. assumption.
Qed.

Definition native_error_proto_obj jne :=
    match jne with
    | J.native_error_syntax => LjsInitEnv.ptr_privSyntaxErrorProto
    | J.native_error_eval => LjsInitEnv.ptr_privEvalErrorProto
    | J.native_error_range => LjsInitEnv.ptr_privRangeErrorProto
    | J.native_error_ref => LjsInitEnv.ptr_privReferenceErrorProto
    | J.native_error_type => LjsInitEnv.ptr_privTypeErrorProto
    end.

Definition native_error_proto_val jne := L.value_object (native_error_proto_obj jne).

Definition native_error_obj jne :=
    match jne with
    | J.native_error_syntax => LjsInitEnv.ptr_privSyntaxErrorGlobalFuncObj
    | J.native_error_eval => LjsInitEnv.ptr_privEvalErrorGlobalFuncObj
    | J.native_error_range => LjsInitEnv.ptr_privRangeErrorGlobalFuncObj
    | J.native_error_ref => LjsInitEnv.ptr_privReferenceErrorGlobalFuncObj
    | J.native_error_type => LjsInitEnv.ptr_privTypeErrorGlobalFuncObj
    end.

Definition native_error_val jne := L.value_object (native_error_obj jne).

Definition attr_constant v := L.attributes_data_of (L.attributes_data_intro v false false false).

Definition attr_native v := L.attributes_data_of (L.attributes_data_intro v true false true).

Definition ljs_prealloc_native_error_proto jne := {|
    L.object_attrs := {|
        L.oattrs_proto := LjsInitEnv.privErrorProto;
        L.oattrs_class := "Error";
        L.oattrs_extensible := true;
        L.oattrs_code := L.value_undefined |};
    L.object_properties := from_list [
        ("constructor", attr_native (native_error_val jne));
        ("message", attr_native (L.value_string ""));
        ("name", attr_native (L.value_string (J.string_of_native_error jne)))];
    L.object_internal := from_list []
|}.

Lemma value_related_native_error_lemma : forall jne,
    value_related initBR 
        (J.value_object (J.object_loc_prealloc (J.prealloc_native_error jne)))
        (native_error_val jne).
Proof.
    introv.
    constructor. eapply prealloc_initBR_lemma. destruct jne; constructor.
Qed.

Hint Resolve value_related_native_error_lemma : js_ljs.

Lemma value_related_native_error_proto_lemma : forall jne,
    value_related initBR 
        (J.value_object (J.object_loc_prealloc (J.prealloc_native_error_proto jne)))
        (native_error_proto_val jne).
Proof.
    introv.
    constructor. eapply prealloc_initBR_lemma. destruct jne; constructor.
Qed.

Hint Resolve value_related_native_error_proto_lemma : js_ljs.

Lemma object_create_prealloc_native_error_proto_lemma : forall jne,
    object_related initBR
        (JsInit.object_prealloc_native_error_proto jne)
        (ljs_prealloc_native_error_proto jne).
Proof.
    introv.
    constructor.
    + constructor; try solve [constructor || reflexivity || 
         (simpl; rewrite from_list_empty; erewrite read_option_not_index_inv by prove_bag; constructor)].
      - constructor. eapply prealloc_initBR_lemma. eauto_js.
    + unfolds. intro.
      destruct (classic (s = "constructor" \/ s = "message" \/ s = "name")) as [Heq|Heq].
      - right. simpl. destruct_hyp Heq; do 2 eexists; repeat rewrite from_list_update; rewrite from_list_empty;
        unfolds JsInit.write_native; rew_heap_to_libbag; rew_binds_eq; splits; eauto_js 20.
      - rew_logic in Heq. destruct_hyp Heq.
        left. simpl. repeat rewrite from_list_update. rewrite from_list_empty.
        unfolds JsInit.write_native. rew_heap_to_libbag. rew_index_eq. eauto_js 10.
Qed.

Definition native_error_constructor jne :=
    match jne with
    | J.native_error_syntax => LjsInitEnv.privSyntaxErrorConstructor
    | J.native_error_eval => LjsInitEnv.privEvalErrorConstructor
    | J.native_error_range => LjsInitEnv.privRangeErrorConstructor
    | J.native_error_ref => LjsInitEnv.privReferenceErrorConstructor
    | J.native_error_type => LjsInitEnv.privTypeErrorConstructor
    end.

Definition ljs_prealloc_native_error jne := 
    ljs_prealloc_constructor_object (native_error_constructor jne) LjsInitEnv.privRunSelfConstructorCall 
        (from_list [("length", attr_constant (L.value_number 1));  
                    ("prototype", attr_constant (native_error_proto_val jne))]).

Lemma object_create_prealloc_native_error_lemma : forall jne,
    object_related initBR
        (JsInit.object_prealloc_native_error jne)
        (ljs_prealloc_native_error jne).
Proof.
    introv.
    apply object_create_prealloc_constructor_lemma; try solve [destruct jne; eauto_js].
    unfolds. intro.
      destruct (classic (s = "length" \/ s = "prototype")) as [Heq|Heq].
      - right. simpl. destruct_hyp Heq; do 2 eexists; repeat rewrite from_list_update; rewrite from_list_empty;
        unfolds JsInit.write_constant; rew_heap_to_libbag; rew_binds_eq; splits; eauto_js 20.
      - rew_logic in Heq. destruct_hyp Heq.
        left. simpl. repeat rewrite from_list_update. rewrite from_list_empty.
        unfolds JsInit.write_constant. rew_heap_to_libbag. rew_index_eq. eauto_js 10.
Qed.

Lemma init_heaps_bisim_obj_ok : heaps_bisim_obj initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    introv Hb1 Hb2.
    unfolds JsInit.state_initial. simpls.
    unfolds J.object_binds. simpls.
    unfolds JsInit.object_heap_initial.
    unfolds JsInit.object_heap_initial_function_objects.
    unfolds JsInit.object_heap_initial_function_objects_3.
    unfolds JsInit.object_heap_initial_function_objects_2.
    unfolds JsInit.object_heap_initial_function_objects_1.
    rewrite heap_binds_to_libbag_eq in Hb1. 
    rew_heap_to_libbag in Hb1. rew_binds_eq in Hb1.
    destruct_hyp Hb1; tryfalse; repeat injects; 
    inverts Hx1; 
    apply from_list_binds in Hb2;
    apply assoc_fast_nat_assoc in Hb2;
    LjsInitEnv.ctx_compute_in Hb2;
    injects Hb2;
    first [apply object_create_prealloc_call_lemma; solve [eauto_js] | 
           apply object_create_prealloc_native_error_lemma |
           apply object_create_prealloc_native_error_proto_lemma | idtac].
    - skip. (* object_create *)
    - skip. (* throw_type_error *)
    - skip. (* error *)
    - skip. (* error_proto *)
    - skip. (* string_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* string *)
    - skip. (* array_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* array *)
    - skip. (* function_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* function *)
    - skip. (* number_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* number *)
    - skip. (* bool_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* bool *)
    - skip. (* object_proto *)
    - apply object_create_prealloc_constructor_lemma; try solve [eauto_js]. skip. (* object *)
    - skip. (* global *)
Qed.

Lemma init_heaps_bisim_env_ok : heaps_bisim_env initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    introv Hb1 Hb2.
    (* TODO simpler? *)
    apply from_list_binds in Hb2.
    apply assoc_fast_nat_assoc in Hb2.
    cbv -[from_list] in Hb2.
    injects Hb2.
    unfolds JsInit.state_initial. simpls.
    unfolds J.env_record_binds. simpls.
    unfolds JsInit.env_record_heap_initial.
    rew_heap_to_libbag in Hb1. binds_inv.
    (* actual lemma *)
    applys env_record_related_object LjsInitEnv.ptr_privglobal.
    repeat rewrite from_list_update. repeat rewrite from_list_empty.
    constructor; eauto_js.
Qed.

Lemma init_heaps_bisim_lfun_obj_ok : heaps_bisim_lfun_obj initBR.
Proof.
    introv Hf1 Hf2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; tryfalse; repeat injects.
    determine. reflexivity.
Qed.

Lemma init_heaps_bisim_lfun_env_ok : heaps_bisim_lfun_env initBR.
Proof.
    introv Hf1 Hf2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; tryfalse; repeat injects.
    reflexivity.
Qed.

Lemma init_heaps_bisim_rfun_ok : heaps_bisim_rfun initBR.
Proof.
    introv Hf1 Hf2 Hfp1 Hfp2. lets H1x : initBR_members Hf1. lets H2x : initBR_members Hf2. 
    destruct_hyp H1x; destruct_hyp H2x; inverts Hfp1; inverts Hfp2; try false_invert.
    + reflexivity.
    + rewrite <- flip_eq in H1x1, H2x1. determine. reflexivity.
Qed.

Lemma init_heaps_bisim_ltotal_obj_ok : heaps_bisim_ltotal_obj initBR JsInit.state_initial.
Proof.
    introv Hidx.
    (* TODO simpler? *)
Transparent index.
    unfolds JsInit.state_initial. simpls.
    unfolds J.object_indom. simpls.
    unfolds JsInit.object_heap_initial.
    rewrite heap_indom_to_libbag_eq in Hidx.
    unfolds JsInit.object_heap_initial_function_objects.
    unfolds JsInit.object_heap_initial_function_objects_3.
    unfolds JsInit.object_heap_initial_function_objects_2.
    unfolds JsInit.object_heap_initial_function_objects_1.
    rew_heap_to_libbag in Hidx. rew_index_eq in Hidx.
    unfolds initBR.
    destruct_hyp Hidx; tryfalse;
    eexists;
    rewrite from_list_in_eq;
    eauto 100 using Mem_here, Mem_next.
Qed.

Lemma init_heaps_bisim_ltotal_env_ok : heaps_bisim_ltotal_env initBR JsInit.state_initial.
Proof.
    introv Hidx.
    (* TODO simpler? *)
    unfolds JsInit.state_initial. simpls.
    unfolds JsCertExt.env_record_indom. simpls.
    unfolds JsInit.env_record_heap_initial.
    rewrite heap_indom_to_libbag_eq in Hidx. rew_heap_to_libbag in Hidx.
    rew_index_eq in Hidx. rew_logic in Hidx. substs.
    eexists. unfold initBR. rew_in_eq. eapply Mem_next. eapply Mem_here.
Qed.

Lemma init_heaps_bisim_lnoghost_obj_ok : heaps_bisim_lnoghost_obj initBR JsInit.state_initial.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    unfolds JsInit.state_initial. simpls.
    unfolds J.object_indom. simpls.
    unfolds JsInit.object_heap_initial.
    rewrite heap_indom_to_libbag_eq.
    unfolds JsInit.object_heap_initial_function_objects.
    unfolds JsInit.object_heap_initial_function_objects_3.
    unfolds JsInit.object_heap_initial_function_objects_2.
    unfolds JsInit.object_heap_initial_function_objects_1.
    rew_heap_to_libbag. rew_index_eq.
    destruct Hx1; eauto_js 150.
    (* TODO: missing in JScert! *)
Admitted. (* TODO *)

Lemma init_heaps_bisim_lnoghost_env_ok : heaps_bisim_lnoghost_env initBR JsInit.state_initial.
Proof.
    introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse. injects.
    (* TODO simpler? *)
    unfolds JsInit.state_initial. simpl.
    unfolds JsCertExt.env_record_indom. simpl.
    unfolds JsInit.env_record_heap_initial. 
    rewrite heap_indom_to_libbag_eq. rew_heap_to_libbag. prove_bag.
Qed.

Lemma init_heaps_bisim_rnoghost_ok : heaps_bisim_rnoghost initBR LjsInitEnv.init_store.
Proof.
    introv Hf Hfp. lets Hx : initBR_members Hf.
    unfolds LjsInitEnv.init_store. rewrite index_binds_eq.
    destruct_hyp Hx; inverts Hfp.
    + eexists. eapply from_list_binds_inv. eapply fast_nat_assoc_assoc.
      cbv -[from_list]. reflexivity.
    + inverts Hx1; eexists; eapply from_list_binds_inv; eapply fast_nat_assoc_assoc;
      cbv -[from_list]; reflexivity.
Qed.

Lemma init_heaps_bisim_consistent_ok :
    heaps_bisim_consistent initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    constructor.
    + apply init_heaps_bisim_obj_ok.
    + apply init_heaps_bisim_env_ok.
    + introv Hf. lets Hx : initBR_members Hf. destruct_hyp Hx; tryfalse.
    + apply init_heaps_bisim_lfun_obj_ok.
    + apply init_heaps_bisim_lfun_env_ok.
    + apply init_heaps_bisim_rfun_ok.
    + apply init_heaps_bisim_ltotal_obj_ok.
    + apply init_heaps_bisim_ltotal_env_ok.
    + apply init_heaps_bisim_lnoghost_obj_ok.
    + apply init_heaps_bisim_lnoghost_env_ok.
    + apply init_heaps_bisim_rnoghost_ok.
Qed.

Lemma init_state_invariant_ok :
    state_invariant initBR JsInit.state_initial LjsInitEnv.init_store.
Proof.
    constructor. 
    + apply init_heaps_bisim_consistent_ok.
    + skip.
    + skip. (* TODO *)
Qed.

Lemma env_records_exist_initial : env_records_exist_env initBR J.lexical_env_initial.
Proof.
    unfolds J.lexical_env_initial.
    introv Hm. inverts Hm; try false_invert. jauto_js.
Qed.

Lemma init_context_invariant_ok : forall b,
    context_invariant initBR (J.execution_ctx_initial b) LjsInitEnv.init_ctx.
Proof.
    constructor.
    + prove_bag.
    + apply execution_ctx_related_init_ctx.
    + apply includes_init_ctx_init_ctx.
    + constructor; apply env_records_exist_initial.
Qed.
