Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import LjsShared.
Require Import Utils.
Require Import LjsRulesCorrectDefinitions.
Require Import LjsRulesCorrectCommon.
Require Import LjsRulesCorrectSpecFuns.
Require Import LjsRulesCorrectCallPrealloc.
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

Lemma arridx_lemma : forall k jvs jv vs v,
    length jvs = length vs ->
    NthDef (J.value_prim J.prim_undef) k jvs jv /\
    NthDef L.value_undefined k vs v ->
    k >= length vs /\ jv = J.value_prim J.prim_undef /\ v = L.value_undefined \/ Nth k jvs jv /\ Nth k vs v.
Proof.
    introv Heq (HnA&HnB).
    apply NthDef_to_Nth in HnA. rewrite Heq in HnA.
    apply NthDef_to_Nth in HnB.
    destruct_hyp HnA; destruct_hyp HnB; eauto.
    apply Nth_lt_length in HnA. false. math.
    apply Nth_lt_length in HnB. false. math.    
Qed.

Lemma binding_inst_formal_params_lemma_lemma : forall BR k jst jc c st st' r is vs jvs1 jvs2 ptr ptr1 jeptr b k',
    ih_call k ->
    L.red_exprh k c st (L.expr_basic (L.expr_seqs_then L.expr_empty
            (map E.init_arg (zipl_stream (LibStream.map string_of_nat (nat_stream_from k')) is)))) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR (jvs1 ++ jvs2) vs ->
    k' = length jvs1 /\ length jvs2 > 0 \/ k' >= length jvs1 /\ jvs2 = [] ->
    binds c "$strict" (L.value_bool b) ->
    binds c "$vcontext" (L.value_object ptr) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_formal_params jvs2 jeptr is b) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv.
    unfolds E.init_args.
    inductions is gen BR k jst st;
    introv IHc;
    introv Hlred Hcinv Hinv Hvrels Hk' Hbinds1 Hbinds2 Hbinds3 Hf1 Hf2. {
        repeat ljs_autoforward.
        jauto_js 10.
    }
    simpl in Hlred.
    rew_map in Hlred.
    repeat ljs_autoforward.
    forwards_th Harridx : array_idx_lemma. reflexivity. eassumption. eassumption.
    destruct Harridx as (?&Heq1&jv&v&Heq2&Hvrel&Harridx). subst_hyp Heq1. subst_hyp Heq2.
    apply arridx_lemma in Harridx; try solve [erewrite <- values_related_length_lemma by eassumption; reflexivity].
    asserts Hjvs2 : (k' >= length jvs1 /\ jvs2 = [] /\ v = L.value_undefined /\ jv = J.value_prim J.prim_undef \/ 
            k' = length jvs1 /\ exists jvs2', jvs2 = jv::jvs2'). {
        destruct Hk' as [(Hk1&Hk2)|(Hk1&Hk2)]. {
            right. split. assumption. 
            destruct jvs2; rew_length in Hk2; try solve [false; math].
            destruct Harridx as [Harridx|Harridx]. {
                erewrite <- values_related_length_lemma in Harridx by eassumption.
                rew_length in Harridx. destruct_hyp Harridx. false. math.
            }
            destruct Harridx as (Harridx1&Harridx2).
            apply Nth_app_inv in Harridx1.
            destruct Harridx1 as [Harridx1|Harridx1]. {
                apply Nth_lt_length in Harridx1. false. math.
            }
            destruct Harridx1 as (k''&Heqk''&Harridx1).
            asserts Hzero : (k'' = 0). { math. } subst_hyp Hzero.
            inverts Harridx1.
            jauto.
        } {
            left. 
            destruct Harridx as [Harridx|Harridx]. {
                destruct_hyp Harridx. jauto.
            }
            subst_hyp Hk2.
            destruct Harridx as (Harridx1&Harridx2).
            rew_app in Harridx1.
            apply Nth_lt_length in Harridx1. false. math.
        }
    }
    clear Harridx. clear Hk'.
    asserts Hexit : (exists jvs1' jvs2', values_related BR (jvs1' ++ jvs2') vs /\
            (S k' = length jvs1' /\ length jvs2' > 0 \/ S k' >= length jvs1' /\ jvs2' = []) /\
            (k' >= length jvs1 /\ jvs2 = [] /\ v = L.value_undefined /\ jv = J.value_prim J.prim_undef /\
                jvs1' = jvs1 /\ jvs2' = jvs2 \/ 
             k' = length jvs1 /\ jvs1' = jvs1 & jv /\ jvs2 = jv::jvs2')). {
        destruct Hjvs2 as [Hjvs2|Hjvs2]. {
            exists jvs1 jvs2.
            destruct_hyp Hjvs2. splits. 
            + assumption. 
            + right. split. math. reflexivity.
            + left. jauto_js.
        } {
            destruct_hyp Hjvs2. destruct jvs2' as [|jv' jvs2']. {
                exists (jvs1&jv) (@nil J.value). splits.
                + rew_app. assumption.
                + right. split. { rew_length. math. } reflexivity.
                + right. jauto_js.
            }
            exists (jvs1&jv) (jv'::jvs2'). splits. 
            + rew_app. assumption.
            + left. split. { rew_length. math. } { rew_length. math. }
            + right. jauto_js.
        }
    }
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b0. { (* binding already exists *)
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct Hexit as (jvs1'&jvs2'&Hvrels'&Hsk'&Hjvs2').
        forwards_th Hx : IHis; try prove_bag. eauto_js.
        destr_concl; [idtac | destruct_hyp Hjvs2'; try ljs_handle_abort].
        destruct_hyp Hjvs2'; jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_mutable_binding_lemma_none. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort].
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; [idtac | destruct_hyp Hjvs2; try ljs_handle_abort]. 
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        destruct Hexit as (jvs1'&jvs2'&Hvrels'&Hsk'&Hjvs2').
        forwards_th Hx : IHis; try prove_bag. eauto_js.
        destr_concl; [idtac | destruct_hyp Hjvs2'; try ljs_handle_abort].
        destruct_hyp Hjvs2'; jauto_js 10.
    }
Qed.

Lemma binding_inst_formal_params_lemma : forall BR k jst jc c st st' r is vs jvs ptr ptr1 jeptr b,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic (E.init_args is)) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    binds c "$strict" (L.value_bool b) ->
    binds c "$vcontext" (L.value_object ptr) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_formal_params jvs jeptr is b) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv IHc Hlred Hcinv Hinv Hvrels Hbinds1 Hbinds2 Hbinds3 Hf1 Hf2.
    asserts Hvrels' : (values_related BR ([]++jvs) vs). { rew_app. assumption. }
    forwards_th : binding_inst_formal_params_lemma_lemma; try prove_bag.
    destruct jvs; rew_length; intuition math.
Qed.

Lemma binding_inst_arg_obj_lemma : forall BR k jst jc c st st' r jptr ptr ptr1 ptr2(*ptr3*)is jvs vs jeptr jlenv v b,
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 LjsInitEnv.privEnvDefineArgsObjOk
        [L.value_object ptr2; L.value_null(*object ptr3*); L.value_object ptr1; L.value_object ptr; L.value_bool b]) 
        (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    lexical_env_related BR jlenv v ->
    fact_js_obj jptr ptr \in BR ->
    fact_iarray ptr1 vs \in BR ->
(*    fact_iarray ptr3 (map L.value_string is) \in BR -> TODO non-strict args obj *)
    fact_js_env jeptr ptr2 \in BR ->
    fact_ctx_parent ptr2 v \in BR ->
    J.execution_ctx_variable_env jc = jeptr::jlenv ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_arg_obj jptr is jvs jeptr b) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc.
    introv Hlred Hcinv Hinv Hvrel Hlrel Hf1 Hf2 Hf3 Hf4 Hvenv.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th Hx : create_arguments_object_ok; try prove_bag.
    rewrite <- Hvenv in Hx.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    destruct b. { (* strict *)
        repeat ljs_autoforward.
        forwards_th : create_immutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : initialize_immutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    } { (* non-strict *)
        repeat ljs_autoforward.
        forwards_th : create_set_mutable_binding_lemma_none. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        jauto_js 10.
    }
Qed.

Lemma binding_inst_function_decls_lemma : forall BR k jst jc c st st' r jfds jeptr ptr b1 b2,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic 
        (E.init_funcs b1 E.make_fobj (map E.js_funcdecl_to_func jfds))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool b2) ->
    binds c "$vcontext" (L.value_object ptr) ->
    fact_js_env jeptr ptr \in BR ->
    (* in ES6, lexical environment is used; in ES5 variable environment is used, which complicates things
       fortunately, the difference can be seen only in non-strict mode *)
    J.execution_ctx_lexical_env jc = J.execution_ctx_variable_env jc -> (* valid in strict mode *)
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_function_decls jeptr jfds b2 b1) (fun jrv => jrv = J.resvalue_empty).    
Proof.
    introv.
    unfolds E.init_funcs.
    inductions jfds gen BR k jst st;
    introv IHc Hlred Hcinv Hinv Hbinds1 Hbinds2 Hf HstrAss. {
        repeat ljs_autoforward.
        jauto_js.
    }
    destruct a. destruct funcdecl_body.
    rew_map in Hlred.
    repeat ljs_autoforward.
    rewrite exprjs_prog_strictness_eq in *.
    forwards_th Hcfo : red_spec_creating_function_object_ok. 
        applys* usercode_context_invariant_lexical_env_lemma.
    rewrite HstrAss in Hcfo.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    ljs_invert_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b. { (* binding already exists *)
        repeat ljs_autoforward.
        cases_decide as Hgctx. { (* on global context *)
            skip. (* TODO global context *)
        }
        asserts Hq : (jeptr <> J.env_loc_global_env_record). {
            unfolds LjsInitEnv.privglobalContext.
            rewrite stx_eq_object_eq_lemma in Hgctx.
            forwards Hger : context_invariant_global_env_record_lemma Hcinv.
            intro Hjeptr. subst_hyp Hjeptr. apply Hgctx.
            determine_fact_js_env.
            reflexivity.
        }
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : IHjfds; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_mutable_binding_lemma_some. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th: set_mutable_binding_lemma. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : IHjfds; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    }
Qed.

Lemma binding_inst_var_decls_lemma : forall BR k jst jc c st st' r is jeptr ptr b1 b2,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic (E.init_vars b1 is)) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool b2) ->
    binds c "$vcontext" (L.value_object ptr) ->
    fact_js_env jeptr ptr \in BR ->
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst_var_decls jeptr is b1 b2) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv.
    unfolds E.init_vars.
    inductions is gen BR k jst st;
    introv IHc Hlred Hcinv Hinv Hbinds1 Hbinds2 Hf. {
        repeat ljs_autoforward.
        jauto_js.
    }
    rew_map in Hlred.
    repeat ljs_autoforward.
    inverts red_exprh H3.
    ljs_apply.
    ljs_context_invariant_after_apply.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. eassumption.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    destruct b. { (* binding already exists *)
        repeat ljs_autoforward.
        forwards_th : IHis; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    } { (* binding does not exist *)
        repeat ljs_autoforward.
        forwards_th: create_set_mutable_binding_lemma_some. prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        forwards_th : IHis; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        jauto_js 10.
    }
Qed.

Opaque E.init_args E.init_vars E.init_funcs.

Lemma binding_inst_global_lemma : forall BR k jst jc c st st' r ptr jp,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_prog false E.make_fobj (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr) ->
    (* see binding_inst_function_decls_lemma *)
    J.execution_ctx_lexical_env jc = J.execution_ctx_variable_env jc -> (* valid in strict mode *)
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_global None jp []) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hbinds1 Hbinds2 HstrAss.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds2.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_var_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    jauto_js 15.
Qed.

Lemma binding_inst_eval_lemma : forall BR k jst jc c st st' r ptr jp,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_prog true E.make_fobj (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr) ->
    (* see binding_inst_function_decls_lemma *)
    J.execution_ctx_lexical_env jc = J.execution_ctx_variable_env jc -> (* valid in strict mode *)
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_eval None jp []) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hbinds1 Hbinds2 HstrAss.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds2.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_var_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    jauto_js 15.
Qed.

Lemma binding_inst_func_lemma : forall BR k jst jc c st st' r ptr ptr1 ptr2 jptr jp jvs vs is,
    ih_call k ->
    L.red_exprh k c st (L.expr_basic
          (E.init_bindings_func E.make_fobj is (concat (List.map E.js_element_to_func (J.prog_elements jp))) 
              (J.prog_vardecl jp))) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    values_related BR jvs vs ->
    binds c "obj" (L.value_object ptr) ->
    binds c "$strict" (L.value_bool (J.prog_intro_strictness jp)) ->
    binds c "$vcontext" (L.value_object ptr2) ->
    binds c "args" (L.value_object ptr1) ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_formal_parameters_ jst jptr (Some is) ->
    (* see binding_inst_function_decls_lemma *)
    J.execution_ctx_lexical_env jc = J.execution_ctx_variable_env jc -> (* valid in strict mode *)
    concl_ext_expr_resvalue BR jst jc c st st' r 
        (J.spec_binding_inst J.codetype_func (Some jptr) jp jvs) (fun jrv => jrv = J.resvalue_empty).
Proof.
    introv IHc Hlred Hcinv Hinv Hvrels.
    introv Hbinds1 Hbinds2 Hbinds3 Hbinds4 Hf1 Hf2 Hom HstrAss.
    asserts_rewrite 
        (concat (List.map E.js_element_to_func (J.prog_elements jp)) = E.prog_funcs (E.js_prog_to_ejs jp)) in Hlred.
    { destruct jp. reflexivity. }
    rewrite E.js_funcdecl_to_func_lemma in Hlred.
    lets Hvenv : execution_ctx_related_variable_env (context_invariant_execution_ctx_related Hcinv) Hbinds3.
    inverts Hvenv as Hf3 Hf4 Hlerel Hvenveq. symmetry in Hvenveq.
    repeat ljs_autoforward.
    forwards_th : binding_inst_formal_params_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    forwards_th : binding_inst_function_decls_lemma; try prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    repeat ljs_autoforward.
    unfolds E.init_args_obj.
    ljs_invert_apply.
    repeat ljs_autoforward.
    cases_decide; [idtac | repeat inv_ljs].
    repeat ljs_autoforward.
    forwards_th: has_binding_lemma. prove_bag.
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_invert.
    destruct b. { (* has binding named "arguments" *)
        repeat ljs_autoforward.
        forwards_th : binding_inst_var_decls_lemma; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    } { (* no binding named "arguments" *)
        repeat ljs_autoforward.
        forwards_th : binding_inst_arg_obj_lemma; try prove_bag. eauto_js. eauto_js.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        resvalue_related_only_invert.
        repeat ljs_autoforward.
        forwards_th : binding_inst_var_decls_lemma; try prove_bag.
        destr_concl; try ljs_handle_abort.
        res_related_invert.
        repeat ljs_autoforward.
        jauto_js 15.
    }
Qed.

Opaque E.init_bindings_func.

Lemma call_lemma : forall BR k jst jc c st st' r jfb is jle v v1 vs ptr ptr1 jptr jv1 jvs,
    ih_stat k ->
    ih_call k ->
    L.red_exprh k c st (L.expr_app_2 v [L.value_object ptr; v1; L.value_object ptr1]) (L.out_ter st' r) ->
    context_invariant BR jc c ->
    state_invariant BR jst st ->
    usercode_related BR jfb is jle v ->
    value_related BR jv1 v1 ->
    values_related BR jvs vs ->
    fact_iarray ptr1 vs \in BR ->
    fact_js_obj jptr ptr \in BR ->
    J.object_method J.object_scope_ jst jptr (Some jle) ->
    J.object_method J.object_formal_parameters_ jst jptr (Some is) ->
    J.object_method J.object_code_ jst jptr (Some jfb) ->
    concl_ext_expr_value BR jst jc c st st' r 
        (J.spec_entering_func_code_3 jptr jvs (J.funcbody_is_strict jfb) jfb jv1 (J.spec_call_default_1 jptr)) 
        (fun jv => True).
Proof.
    introv IHt IHc Hlred Hcinv Hinv Hucrel Hvrel Hvrels Hbs Hbs1.
    introv Hom1 Hom2 Hom3.
    inverts Hucrel as Huci.
    unfolds funcbody_closure. unfolds funcbody_expr. unfolds E.make_lambda_expr.
    cases_let as Hprog.
    ljs_invert_apply.
    subst c'.
    repeat ljs_autoforward.
    lets Hlerel : usercode_context_invariant_lexical_env_related Huci ___; try eassumption.
    forwards_th Hx : usercode_context_invariant_restore; try eassumption. 
    destruct_hyp Hx.
    repeat ljs_autoforward.
    rewrite <- (js_prog_intro_eta jp) in Hprog.
    simpl in Hprog.
    injects Hprog.
    rewrite js_prog_intro_eta in *.
    lets Hstrict : usercode_context_invariant_has_strict Huci. (* TODO do a lemma *)
    rewrite index_binds_eq in Hstrict. destruct_hyp Hstrict.
    lets Hstreq : usercode_context_invariant_strict Huci Hstrict. subst_hyp Hstreq.
    forwards_th : binding_inst_func_lemma; try prove_bag 8. { eauto_js. } skip. (* TODO state consistency *)
    destr_concl; try ljs_handle_abort.
    res_related_invert.
    resvalue_related_only_invert.
    repeat ljs_autoforward.
    asserts Hom3' : (J.object_method J.object_code_ jst' jptr (Some (J.funcbody_intro jp s))). 
        skip. (* TODO state consistency *)
    lets [Hfbe|Hfbe] : classic (J.funcbody_empty (J.funcbody_intro jp s)). { 
        (* special case required by the spec *)
        unfolds J.funcbody_empty. unfolds J.prog_empty.
        simpl in Hfbe. rewrite Hfbe in *.
        repeat ljs_autoforward.
        jauto_js 10.
    }
    forwards_th Hx : prog_ok_call_lemma.
    destruct_hyp Hx. (* TODO destr_concl *)
    res_related_invert; repeat ljs_autoforward. { (* normal exit *)
        jauto_js 10.
    } { (* exception *)
        jauto_js 10.
    } { (* return *)
        jauto_js 10.
    } { (* break *)
        (* TODO: should never happen due to syntax constraints, but unable to prove this now. *)
        skip. 
    } { (* continue *)
        (* TODO: should never happen due to syntax constraints, but unable to prove this now. *)
        skip. 
    }
Qed.

Lemma red_spec_call_prealloc_ok : forall k jpre, ih_call k -> th_call_prealloc k jpre.
Proof.
    introv IHk.
    destruct jpre.
    + skip.
    + skip.
    + applys~ red_expr_call_global_is_finite_ok.
    + applys~ red_expr_call_global_is_nan_ok.
    + skip.
    + skip.
    + applys~ red_expr_call_object_ok.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + applys~ red_expr_call_boolean_ok.
    + skip.
    + skip.
    + skip.
    + applys~ red_expr_call_number_ok.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
    + skip.
Qed.

Lemma red_spec_call_ok : forall k,
    ih_stat k ->
    ih_call k ->
    th_call k.
Proof.
    introv IHt IHc Hcinv Hinv Hvrel Halo Hbs Hvrels Hlred. 
    ljs_invert_apply.
    repeat ljs_autoforward.
    inverts red_exprh H7. (* TODO *)
    lets (jcon&Hmeth&Hcall) : object_method_call_some_lemma Hinv Hbs ___; try eassumption.
    inverts Hcall. { (* prealloc *)
        forwards_th Hx : red_spec_call_prealloc_ok; try eassumption. 
        destr_concl; try ljs_handle_abort.
        jauto_js.
    } { (* default *)
        ljs_invert_apply.
        repeat ljs_autoforward.
        lets (jfb&is&jle&Hmcode&Hparams&Hscope&Hcode) : object_method_code_some_lemma ___; try eassumption.
        lets (str&Heqstr&Hfbstr) : object_strict_lemma ___; try eassumption.
        subst_hyp Heqstr.
        ljs_invert_apply.
        repeat ljs_autoforward.
        symmetry in Hfbstr.
        destruct str. { (* strict *)
            repeat ljs_autoforward.
            forwards_th Hcl : call_lemma; try eassumption.
            rewrite <- Hfbstr in Hcl.
            destr_concl; try ljs_handle_abort.
            jauto_js 15.
        } { (* not strict *)
            do 2 inv_fwd_ljs.
            (* TODO better condition handling *)
            ljs_out_redh_ter.
            ljs_bool_red_exprh; repeat determine_epsilon.
            cases_isTrue as Hevcond. { (* null or undefined *)
                repeat ljs_autoforward.
                rewrite case_classic_l_eq in Hevcond.
                asserts Hmycond : (jv = J.value_prim J.prim_null \/ jv = J.value_prim J.prim_undef). {
                    inverts Hvrel;
                    destruct Hevcond as [Hevcond|Hevcond]; inverts Hevcond; eauto_js.
                }
                forwards_th Hcl : call_lemma; try eassumption.
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            } 
            repeat ljs_autoforward.
            cases_decide as Hisobj. { (* is object *)
                repeat ljs_autoforward.
                inverts Hvrel; inverts Hisobj.
                forwards_th Hcl : call_lemma; try eassumption.
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            } { (* not object *)
                rewrite case_classic_l_eq in Hevcond.
                rew_logic in Hevcond. destruct Hevcond as (Hevcond1&Hevcond2).
                asserts Hmycond : (jv <> JsSyntax.value_prim JsSyntax.prim_null /\
                    jv <> JsSyntax.value_prim JsSyntax.prim_undef /\
                    JsPreliminary.type_of jv <> JsSyntax.type_object). {
                    inverts Hvrel; try solve [false; eauto_js]; eauto_js.
                }
                repeat ljs_autoforward.
                forwards_th : red_spec_to_object_ok.
                destr_concl; try ljs_handle_abort.
                res_related_invert.
                resvalue_related_invert.
                repeat ljs_autoforward.
                forwards_th Hcl : call_lemma; try eauto_js. skip. skip. skip. (* TODO state consistency issue! *)
                rewrite <- Hfbstr in Hcl.
                destr_concl; try ljs_handle_abort.
                jauto_js 15.
            }
        }
    } { (* bind *)
        skip. (* TODO *) (* NOT YET IN JSCERT *)
    }
Qed.
