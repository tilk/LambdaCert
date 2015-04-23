Generalizable All Variables.
Set Implicit Arguments.
Require Import JsNumber.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesIndexed.
Require Import LjsPrettyRulesIndexedInvert.
Require Import LjsPrettyRulesIndexedAux.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import LjsInterpreter.

Import ListNotations.

Open Scope list_scope.

Implicit Type A B : Type.
Implicit Type runs : runs_type.
Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.
Implicit Type re : result.
Implicit Type r : res.

(* Lemmas on monadic ops *)

Lemma assert_deref_lemma : forall {A c i v} cont, binds c i v -> @assert_deref A c i cont = cont v.
Proof.
    introv H. unfolds. rewrite <- read_option_binds_eq in H.
    unfold ctx. rewrite H. reflexivity.
Qed.

Lemma eval_cont_lemma : forall {A runs c st e re} cont,
    runs_type_eval runs c st e = re ->
    @eval_cont A runs c st e cont = cont re.
Proof.
    introv H. unfolds. rewrite H. reflexivity.
Qed.

Lemma if_eval_return_lemma : forall {runs c st st' e v} cont, 
    runs_type_eval runs c st e = result_some (out_ter st' (res_value v)) ->
    if_eval_return runs c st e cont = cont st' v.
Proof.
    introv H. unfolds. lets L : @eval_cont_lemma H. rewrite L. reflexivity.
Qed.

Lemma if_eval_ter_div_lemma : forall {runs c st e} cont, 
    runs_type_eval runs c st e = result_some out_div ->
    if_eval_ter runs c st e cont = result_some out_div.
Proof.
    introv H. unfolds. lets L : @eval_cont_lemma H. rewrite L. reflexivity.
Qed.

Lemma if_eval_ter_lemma : forall {runs c st st' e r} cont, 
    runs_type_eval runs c st e = result_some (out_ter st' r) ->
    if_eval_ter runs c st e cont = cont st' r.
Proof.
    introv H. unfolds. lets L : @eval_cont_lemma H. rewrite L. reflexivity.
Qed.

Lemma assert_get_object_ptr_lemma : forall {A ptr} cont, 
    @assert_get_object_ptr A (value_object ptr) cont = cont ptr.
Proof.
    intros. reflexivity.
Qed.

Lemma assert_get_object_from_ptr_lemma : forall {A st ptr obj} cont, 
    binds st ptr obj -> @assert_get_object_from_ptr A st ptr cont = cont obj.
Proof.
    introv H. unfolds. rewrite <- read_option_binds_eq in H. rewrite H. reflexivity.
Qed.

Lemma assert_get_object_lemma : forall {A st ptr obj} cont, 
    binds st ptr obj -> @assert_get_object A st (value_object ptr) cont = cont obj.
Proof.
    introv H. unfolds. 
    rewrite assert_get_object_ptr_lemma. 
    auto using assert_get_object_from_ptr_lemma.
Qed.

Lemma assert_get_string_lemma : forall {A s} cont, 
    @assert_get_string A (value_string s) cont = cont s.
Proof.
    intros. reflexivity.
Qed.

Lemma assert_get_bool_lemma : forall {A v b} cont,
    value_to_bool v = Some b -> @assert_get_bool A v cont = cont b.
Proof.
    introv H. unfolds. destruct v; inverts H; reflexivity.
Qed.

Lemma assert_get_bool_false_lemma : forall {A} cont,
    @assert_get_bool A value_false cont = cont false.
Proof.
    intros. reflexivity.
Qed.

Lemma assert_get_bool_true_lemma : forall {A} cont,
    @assert_get_bool A value_true cont = cont true.
Proof.
    intros. reflexivity.
Qed.

Lemma if_result_some_lemma : forall {A B res a} cont,
    res = result_some a -> @if_result_some A B res cont = cont a.
Proof.
    introv H. rewrite H. reflexivity.
Qed.

Lemma change_object_cont_lemma : forall {st ptr obj} cont, 
    binds st ptr obj -> 
    change_object_cont st ptr cont = cont obj (fun st new_obj ret =>
        result_some (out_ter (st \(ptr := new_obj)) (res_value ret))).
Proof.
    introv H. unfolds. rewrite <- read_option_binds_eq in H. unfold store. rewrite H. reflexivity.
Qed.

Lemma if_out_ter_lemma : forall {re st r} cont,
    re = result_some (out_ter st r) ->
    if_out_ter re cont = cont st r.
Proof.
    introv H.
    unfolds.
    rewrite (if_result_some_lemma _ H).
    reflexivity.
Qed.

Lemma if_value_abort_lemma : forall {o} cont,
    abort o ->
    if_value (result_some o) cont = result_some o.
Proof.
    introv HA. inversion HA as [ | st r HC ].
    reflexivity.
    inversion HC; reflexivity. 
Qed.

Lemma if_eval_return_abort_lemma : forall {runs c st e o} cont,
    abort o ->
    runs_type_eval runs c st e = result_some o ->
    if_eval_return runs c st e cont = result_some o.
Proof.
    introv HA H. unfolds. lets L : @eval_cont_lemma H. rewrite L.
    applys @if_value_abort_lemma HA.
Qed.

(* Utility lemmas *)

Lemma get_property_from_object_property_is : forall st obj name oattr,
    object_property_is st obj name oattr -> get_property st obj name = result_some oattr.
Proof.
Admitted. (* TODO *)

Lemma get_closure_from_value_is_closure : forall st v clo,
    value_is_closure st v clo -> get_closure st v = result_some clo.
Proof.
Admitted. (* TODO *)

Lemma get_closure_ctx_from_closure_ctx : forall clo sl c,
    closure_ctx clo sl c -> get_closure_ctx clo sl = result_some c.
Proof.
    introv Hc.
    inverts Hc as Hzip;
    simpl;
    unfold add_parameters;
    cases_match_option;
    rewrite (Zip_zip Hzip) in *; tryfalse;
    injects;
    reflexivity.
Qed.

(* Useful tactics *)

Ltac ljs_eval :=
    match goal with
    | H : value_is_closure _ _ _ |- _ => apply get_closure_from_value_is_closure in H
    | H : object_property_is _ _ _ _ |- _ => apply get_property_from_object_property_is in H
    | H : closure_ctx _ _ _ |- _ => apply get_closure_ctx_from_closure_ctx in H
    | H : binds ?c ?i _ |- assert_deref ?c ?i _ = _ => rewrite (assert_deref_lemma _ H)
    | H : runs_type_eval ?runs ?c ?st ?e = _ |- eval_cont ?runs ?c ?st ?e _ = _ => rewrite (eval_cont_lemma _ H)
    | H : runs_type_eval ?runs ?c ?st ?e = result_some (out_ter _ (res_value _)) 
        |- if_eval_return ?runs ?c ?st ?e _ = _ => rewrite (if_eval_return_lemma _ H)
    | H : runs_type_eval ?runs ?c ?st ?e = result_some (out_ter _ _) 
        |- if_eval_ter ?runs ?c ?st ?e _ = _ => rewrite (if_eval_ter_lemma _ H)
    | H : binds ?st ?ptr _ |- assert_get_object_from_ptr ?st ?ptr _ = _ => 
        rewrite (assert_get_object_from_ptr_lemma _ H)
    | H : binds ?st ?ptr _ |- assert_get_object ?st (value_object ?ptr) _ = _ => 
        rewrite (assert_get_object_lemma _ H)
    | H : binds ?st ?ptr _ |- change_object_cont ?st ?ptr _ = _ => 
        rewrite (change_object_cont_lemma _ H)
    | H : value_to_bool ?v = Some _ |- assert_get_bool ?v _ = _ => rewrite (assert_get_bool_lemma _ H)
    | |- assert_get_bool value_true _ = _ => rewrite (assert_get_bool_true_lemma _)
    | |- assert_get_bool value_false _ = _ => rewrite (assert_get_bool_false_lemma _)
    | |- assert_get_string (value_string _) _ = _ => rewrite (assert_get_string_lemma _)
    | |- assert_get_object_ptr (value_object _) _ = _ => rewrite (assert_get_object_ptr_lemma _)
    | H : ?re = result_some (out_ter _ _) |- if_out_ter ?re _ = _ => rewrite (if_out_ter_lemma _ H)
    | |- if_out_ter (result_some (out_ter ?st ?r)) _ = _ => 
        let X := fresh in let H := fresh in 
        sets_eq X H :(result_some (out_ter st r)); rewrite (if_out_ter_lemma _ H); inverts H
    | H : ?res = result_some _ |- if_result_some ?res _ = _ => rewrite (if_result_some_lemma _ H)
    | |- if_result_some (result_some _) _ = _ => unfold if_result_some
    end.

Ltac ljs_abort :=
    match goal with
    | H : abort ?o |- if_value (result_some ?o) _ = result_some ?o => apply (if_value_abort_lemma _ H)
    | H : abort ?o, H1 : runs_type_eval ?runs ?c ?st ?e = result_some ?o 
        |- if_eval_return ?runs ?c ?st ?e ?cont = result_some ?o => apply (if_eval_return_abort_lemma _ H H1)
    | H : runs_type_eval ?runs ?c ?st ?e = result_some out_div 
        |- if_eval_return ?runs ?c ?st ?e ?cont = result_some ?o => apply (if_eval_ter_div_lemma _ H)
    end. 

Lemma lazyruns_lemma : forall runs, suspend_runs (fun _ => runs) = runs.
Proof.
    intros.
    destruct runs. unfolds.
    autorewrite with rew_eta. 
    reflexivity.
Qed.

Ltac ljs_specialize_ih H1 :=
    match goal with
    | H : red_exprh _ _ _ _ _, IH : forall c st e o, red_exprh _ _ _ _ _ -> _ |- _ => 
        lets H1 : IH H; clear H
    end.

Tactic Notation "ljs_specialize_ih" :=
    let H := fresh "H" in ljs_specialize_ih H.

Ltac ljs_inv_red :=
    match goal with
    | H	: red_exprh _ _ _ _ _ |- _ => 
        inverts H
    end.

Ltac ljs_inv_red_internal :=
    match goal with
    | H	: red_exprh _ _ _ ?e _ |- _ => 
        match e with 
        | expr_basic _ => fail 
        | _ => inverts red_exprh H; tryfalse
        end
    end.

Ltac bool_tryfalse := try solve [fold_bool; rew_reflect in *; tryfalse].

Ltac ljs_inv_red_inter := 
    match goal with
    | H	: red_exprh _ _ _ ?e _ |- _ => 
        match e with 
        | expr_eval_many_1 _ _ _ => inverts red_exprh H
        | expr_object_1 _ _ => inverts red_exprh H
        | expr_object_data_1 _ _ _ _ => inverts red_exprh H
        | expr_object_accessor_1 _ _ _ _ => inverts red_exprh H
        | expr_get_attr_1 _ _ => inverts red_exprh H
        | expr_set_attr_1 _ _ => inverts red_exprh H
        | expr_set_obj_attr_1 _ _ => inverts red_exprh H
        | expr_get_field_1 _ => inverts red_exprh H
        | expr_set_field_1 _ => inverts red_exprh H
        | expr_delete_field_1 _ => inverts red_exprh H
        | expr_eval_1 _ => inverts red_exprh H
        end; tryfalse; bool_tryfalse; [idtac]
    end.

Ltac ljs_inv_red_abort := ljs_inv_red_internal; [ | ljs_abort].

Lemma exists_S : forall (P : nat -> Prop), (exists k, P (S k)) -> exists k, P k.
Proof.
    introv H.
    destruct H as (k&H).
    eexists; eassumption.
Qed.

Ltac ljs_eval_step := ljs_specialize_ih; ljs_inv_red_abort; ljs_eval.

Ltac ljs_eval_push := solve [auto] || ljs_specialize_ih || ljs_inv_red_abort || ljs_eval || ljs_inv_red_inter.

(* Lemmas about complex constructions of ljs (object literals and function application) *)

Lemma object_properties_lemma : forall k,
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall l c st obj o,
    red_exprh k c st (expr_object_2 obj l) o ->
    eval_object_properties (runs k) c st l obj (fun st obj =>
                  let (st, loc) := add_object st obj
                  in result_value st loc
          ) = result_some o.
Proof.
    introv IH.
    induction l as [|p l]; introv R.
    (* [] *)
    simpl.
    ljs_inv_red.
    reflexivity.
    (* [] *)
    destruct p as (i&[()|()]); ljs_inv_red; simpl.
    (* data *)
    abstract (repeat ljs_eval_push; eauto).
    (* accessor *)
    abstract (repeat ljs_eval_push; eauto).
Qed.

Lemma apply_lemma : forall k,
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall c st v vs o,
    red_exprh k c st (expr_app_2 v vs) o ->
    apply (runs k) c st v vs = result_some o.
Proof.
    introv IH H.
    substs.
    ljs_inv_red_internal.
    unfolds.
    repeat ljs_eval_push.
Qed.

Lemma eval_arg_list_lemma : forall k, 
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall es c st v vs o,
    red_exprh k c st (expr_eval_many_1 es vs (expr_app_2 v)) o ->
    fold_right (eval_arg_list_aux (runs k) c) (fun st vs => apply (runs k) c st v (rev vs)) es st vs = result_some o.
Proof.
    introv IH.
    induction es; introv H. 
    inverts H; eapply apply_lemma; eauto.
    simpl.
    unfolds.
    repeat ljs_eval_push.
    eauto.
Qed.

Lemma unary_op_lemma : forall op st v v',
    eval_unary_op op st v v' ->
    unary_operator op st v = result_some v'.
Proof.
    introv He.
    inverts He as Hee; try inverts Hee; reflexivity.
Qed.

Lemma binary_op_lemma : forall op st v v1 v',
    eval_binary_op op st v v1 v' ->
    binary_operator op st v v1 = result_some v'.
Proof.
    introv He.
    inverts He as Hee; try inverts Hee; try reflexivity.
    (* has_property *)
    unfolds binary_operator, has_property. 
    repeat ljs_eval_push. skip.
    (* has_own_property *)
    unfolds binary_operator, has_own_property.
    repeat ljs_eval_push. unfolds get_object_property. simpl. 
    unfolds prop_name.
    cases_match_option as Eq1; reflexivity.
    (* is_accessor *)
    unfolds binary_operator, is_accessor.
    repeat ljs_eval_push.
    (* char_at *)
    unfolds binary_operator, char_at.
    cases_if. rewrite H1. reflexivity. false. auto.
Qed.

(* The main lemma *)

Opaque read_option. 

Lemma eval_complete_lemma : forall k c st e o,
    red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o.
Proof.
    induction k; 
    introv R;
    inverts R;
    simpls.
    (* empty *)
    reflexivity.
    (* null *)
    reflexivity.
    (* undefined *)
    reflexivity.
    (* string *)
    reflexivity.
    (* number *)
    reflexivity.
    (* bool *)
    reflexivity.
    (* id *) 
    unfolds.
    repeat ljs_eval; reflexivity.
    (* lambda *)
    reflexivity.
    (* object *)
    abstract (repeat ljs_eval_push;
              eauto using object_properties_lemma).
    (* get_attr *)
    unfolds.
    repeat ljs_eval_push.
    unfolds get_object_pattr, get_object_property.
    cases_match_option as Hopt.
    rewrite read_option_binds_eq in Hopt. binds_determine.
    match goal with H : attributes_pattr_readable _ _ |- _ => inverts H end;
    repeat ljs_eval_push.
    unfolds object_props, prop_name.
    simpl in Hopt.
    match goal with H : binds props _ _ |- _ => 
        rewrite <- read_option_binds_eq in H; rewrite H in Hopt end.
    solve [false].
    (* set_attr *)
    unfolds.
    repeat ljs_eval_push.
    ljs_inv_red_internal;
    repeat ljs_eval_push;
    unfolds set_object_pattr, get_object_property;
    cases_match_option as Hopt. 
    rewrite read_option_binds_eq in Hopt. binds_determine.
    cases_if.
    destruct a as [aa|aa]; destruct aa;
    match goal with H : attributes_pattr_writable _ _ |- _ => inverts H end;
    match goal with H : attributes_pattr_valid _ _ |- _ => inverts H end;
    repeat ljs_eval_push.
    unfolds object_props, prop_name.
    simpl in Hopt.
    match goal with H : binds props _ _ |- _ => 
        rewrite <- read_option_binds_eq in H; rewrite H in Hopt end.
    solve [false]. 
    rewrite read_option_binds_eq in Hopt. false. prove_bag.
    unfolds object_extensible.
    simpls. 
    cases_if.
    match goal with H : attributes_pattr_valid _ _ |- _ => inverts H end;
    repeat ljs_eval_push.
    (* get_obj_attr *)
    unfolds.
    abstract (repeat ljs_eval_push).
    (* set_obj_attr *)
    unfolds.
    repeat ljs_eval_push.
    unfolds set_object_oattr_check.
    cases_let. substs.
    unfolds object_extensible. 
    match goal with H : object_oattr_modifiable _ _ |- _ => inverts H end;
    match goal with H : object_oattr_valid _ _ |- _ => inverts H end;
    simpls; try cases_if; tryfalse; repeat ljs_eval_push.
    (* get_field *)
    unfolds.
    repeat ljs_eval_push.
    destruct oattr as [[|]|].
    ljs_inv_red. reflexivity.
    ljs_inv_red_internal.
    eapply apply_lemma; eauto.
    ljs_inv_red. reflexivity.
    (* set_field *)
    unfolds.
    repeat ljs_eval_push.
    unfold change_object_property, change_object_property_cont.
    destruct oattr as [[|]|]. destruct obj.
    repeat (ljs_eval || cases_if || cases_match_option); ljs_inv_red; 
    unfolds get_object_property, object_extensible; simpls;
    try match goal with H : object_properties\(s?) = _ |- _ => 
        apply read_option_binds in H || apply read_option_not_index in H end;
    tryfalse; bool_tryfalse; try solve [false; prove_bag 8]; try reflexivity.
    ljs_inv_red_internal.
    eapply apply_lemma; eauto. 
    cases_if; ljs_inv_red; unfolds object_extensible; simpls; tryfalse; bool_tryfalse; try ljs_eval; reflexivity.
    (* delete_field *)
    unfolds.
    repeat ljs_eval_push.
    repeat (ljs_eval || cases_if || cases_match_option); ljs_inv_red; tryfalse; bool_tryfalse; reflexivity.
    (* own_field_names *)
    unfolds.
    repeat ljs_eval_push.
    (* op1 *)
    unfolds.
    repeat ljs_eval_push.
    forwards Hop : unary_op_lemma; try eassumption.
    repeat ljs_eval_push.
    (* op2 *)
    unfolds.
    repeat ljs_eval_push. 
    forwards Hop : binary_op_lemma; try eassumption.
    repeat ljs_eval_push.
    (* if *)
    unfolds.
    ljs_specialize_ih. ljs_inv_red_internal.
    ljs_specialize_ih.
    repeat ljs_eval_push.
    ljs_specialize_ih.
    repeat ljs_eval_push.
    ljs_abort.
    (* app *)
    unfolds.
    repeat ljs_eval_push.
    eapply eval_arg_list_lemma; eassumption.
    (* seq *)
    unfolds.
    abstract (repeat ljs_eval_push).
    (* jseq *)
    unfolds.
    repeat ljs_eval_push.
    destruct o1 as [ | zz [ | | ] ]; 
    ljs_inv_red_internal; 
    repeat ljs_eval_push. skip.
    (* let *)
    unfolds.
    repeat ljs_eval_push.
    (* rec *)
    repeat ljs_eval_push.
    (* label *)
    unfolds.
    repeat ljs_eval_push.
    unfolds.
    ljs_eval.
    destruct o as [ | zz [ | | ] ];
    ljs_inv_red_internal;
    simpl; try cases_if; reflexivity.
    (* break *)
    unfolds.
    abstract (repeat ljs_eval_push).
    (* trycatch *)
    unfolds.
    repeat ljs_eval_push.
    unfolds.
    ljs_eval.
    ljs_inv_red_internal.
    destruct o as [ | zz [ | | ] ];
    tryfalse; repeat ljs_eval_push. 
    simpl. repeat ljs_eval_push.
    eapply apply_lemma; eauto.
    (* tryfinally *)
    unfolds.
    repeat ljs_eval_push.
    unfolds.
    ljs_inv_red_internal.
    repeat ljs_eval_push.
    repeat ljs_eval_push.
    (* throw *)
    unfolds.
    abstract (repeat ljs_eval_push).
    (* eval *)
    unfolds.
    repeat ljs_eval_push.
    repeat cases_match_option.
    repeat injects.
    repeat ljs_eval_push.
    (* hint *)
    repeat ljs_eval_push.
Qed.

(* Completeness *)

Lemma eval_complete : forall c st e o,
    red_expr c st e o -> exists k, runs_type_eval (runs k) c st e = result_some o.
Proof.
    introv H.
    lets (k&H1) : red_expr_add_h H.
    exists k.
    applys eval_complete_lemma H1.
Qed.
