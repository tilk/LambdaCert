Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesIndexed.
Require Import LjsPrettyRulesIndexedAux.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import LjsInterpreter.
Require Import JsNumber.
Require Import Coq.Strings.String.

Import ListNotations.

Open Scope list_scope.

Implicit Type A B : Type.
Implicit Type runs : runs_type.
Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type loc : value_loc.
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

Lemma assert_get_loc_lemma : forall {A c i loc} cont, get_loc c i = Some loc -> @assert_get_loc A c i cont = cont loc.
Proof.
    introv H. unfolds. rewrite H. reflexivity.
Qed.

Lemma assert_deref_lemma : forall {A st loc v} cont, get_value st loc = Some v -> @assert_deref A st loc cont = cont v.
Proof.
    introv H. unfolds. rewrite H. reflexivity.
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

Lemma assert_get_object_ptr_lemma : forall {A ptr} cont, 
    @assert_get_object_ptr A (value_object ptr) cont = cont ptr.
Proof.
    intros. reflexivity.
Qed.

Lemma assert_get_object_from_ptr_lemma : forall {A st ptr obj} cont, 
    get_object st ptr = Some obj -> @assert_get_object_from_ptr A st ptr cont = cont obj.
Proof.
    introv H. unfolds. rewrite H. reflexivity.
Qed.

Lemma assert_get_object_lemma : forall {A st ptr obj} cont, 
    get_object st ptr = Some obj -> @assert_get_object A st (value_object ptr) cont = cont obj.
Proof.
    introv H. unfolds. rewrite assert_get_object_ptr_lemma. 
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
    get_object st ptr = Some obj -> 
    change_object_cont st ptr cont = cont obj (fun st new_obj ret =>
        result_some (out_ter (LjsStore.update_object st ptr new_obj) (res_value ret))).
Proof.
    introv H. unfolds. rewrite H. reflexivity.
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

Lemma is_eval_return_abort_lemma : forall {runs c st e o} cont,
    abort o ->
    runs_type_eval runs c st e = result_some o ->
    if_eval_return runs c st e cont = result_some o.
Proof.
    introv HA H. unfolds. lets L : @eval_cont_lemma H. rewrite L.
    applys @if_value_abort_lemma HA.
Qed.

(* Useful tactics *)

Ltac ljs_eval :=
    match goal with
    | H : get_loc ?c ?i = Some _ |- assert_get_loc ?c ?i _ = _ => rewrite (assert_get_loc_lemma _ H)
    | H : get_value ?st ?loc = Some _ |- assert_deref ?st ?loc _ = _ => rewrite (assert_deref_lemma _ H)
    | H : runs_type_eval ?runs ?c ?st ?e = _ |- eval_cont ?runs ?c ?st ?e _ = _ => rewrite (eval_cont_lemma _ H)
    | H : runs_type_eval ?runs ?c ?st ?e = result_some (out_ter _ (res_value _)) 
        |- if_eval_return ?runs ?c ?st ?e _ = _ => rewrite (if_eval_return_lemma _ H)
    | H : get_object ?st ?ptr = Some _ |- assert_get_object_from_ptr ?st ?ptr _ = _ => 
        rewrite (assert_get_object_from_ptr_lemma _ H)
    | H : get_object ?st ?ptr = Some _ |- assert_get_object ?st (value_object ?ptr) _ = _ => 
        rewrite (assert_get_object_lemma _ H)
    | H : get_object ?st ?ptr = Some _ |- change_object_cont ?st ?ptr _ = _ => 
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
    end.

Ltac ljs_abort :=
    match goal with
    | H : abort ?o |- if_value (result_some ?o) _ = result_some ?o => apply (if_value_abort_lemma _ H)
    | H : abort ?o, H1 : runs_type_eval ?runs ?c ?st ?e = result_some ?o 
        |- if_eval_return ?runs ?c ?st ?e ?cont = result_some ?o => apply (is_eval_return_abort_lemma _ H H1)
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
        | _ => inverts H
        end
    end.

Ltac ljs_inv_red_abort := ljs_inv_red_internal; [ | ljs_abort].

Lemma exists_S : forall (P : nat -> Prop), (exists k, P (S k)) -> exists k, P k.
Proof.
    introv H.
    destruct H as (k&H).
    eexists; eassumption.
Qed.

Ltac ljs_eval_step := ljs_specialize_ih; ljs_inv_red_abort; ljs_eval.

Ltac ljs_eval_push := ljs_specialize_ih || ljs_inv_red_abort || ljs_eval || reflexivity || assumption.

(* Lemmas about complex constructions of ljs (object literals and function application) *)

Lemma object_properties_lemma : forall k,
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall l c st obj o,
    red_exprh k c st (expr_object_6 obj l) o ->
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
    cases_let.
    injects.
    reflexivity.
    (* [] *)
    destruct p as (i&[()|()]); ljs_inv_red; simpl.
    (* data *)
    repeat ljs_eval_push.
    eauto.
    (* accessor *)
    repeat ljs_eval_push.
    eauto.
Qed.

Lemma apply_lemma : forall k,
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall c st v vs vsr o,
    red_exprh k c st (expr_app_2 v vsr nil) o ->
    vsr = rev vs ->
    apply (runs k) c st v vs = result_some o.
Proof.
    introv IH H HR.
    substs.
    ljs_inv_red_internal.
    unfolds.
    repeat ljs_eval_push.
    rew_list in *.
    cases_let.
    injects.
    repeat ljs_eval_push.
Qed.

Lemma eval_arg_list_lemma : forall k, 
    (forall c st e o, red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o) -> 
    forall es c st v vs o,
    red_exprh k c st (expr_app_2 v vs es) o ->
    fold_right (eval_arg_list_aux (runs k) c) (fun st vs => apply (runs k) c st v (rev vs)) es st vs = result_some o.
Proof.
    introv IH.
    induction es; introv H.
    eapply apply_lemma; rew_list; eauto.
    simpl.
    unfolds.
    ljs_inv_red_internal.
    repeat ljs_eval_push.
    eauto.
Qed.

(* The main lemma *)

Lemma eval_complete_lemma : forall k c st e o,
    red_exprh k c st e o -> runs_type_eval (runs k) c st e = result_some o.
Proof.
    induction k; 
    introv R;
    inverts R;
    simpls.
    (* null *)
    reflexivity.
    (* undefined *)
    reflexivity.
    (* string *)
    reflexivity.
    (* number *)
    reflexivity.
    (* true *)
    reflexivity.
    (* false *)
    reflexivity.
    (* id *)
    unfolds. 
    repeat ljs_eval; reflexivity.
    (* lambda *)
    unfolds.
    cases_let. injects. reflexivity.
    (* object *)
    repeat ljs_eval_push.
    eauto using object_properties_lemma.
    (* get_attr *)
    unfolds.
    repeat ljs_eval_push.
    (* set_attr *)
    unfolds.
    repeat ljs_eval_push.
    (* get_obj_attr *)
    unfolds.
    repeat ljs_eval_push.
    (* set_obj_attr *)
    unfolds.
    repeat ljs_eval_push.
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
    destruct oattr as [[|]|].
    repeat (ljs_eval || cases_if || cases_match_option); ljs_inv_red; tryfalse; reflexivity.
    ljs_inv_red_internal.
    eapply apply_lemma; eauto.
    cases_if; ljs_inv_red; tryfalse; try ljs_eval; reflexivity.
    (* delete_field *)
    unfolds.
    repeat ljs_eval_push.
    repeat (ljs_eval || cases_if || cases_match_option); ljs_inv_red; tryfalse; reflexivity.
    (* own_field_names *)
    unfolds.
    repeat ljs_eval_push.
    cases_let.
    injects.
    reflexivity.
    (* set_bang *)
    unfolds.
    repeat ljs_eval_push.
    (* op1 *)
    unfolds.
    repeat ljs_eval_push.
    (* op2 *)
    unfolds.
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
    repeat ljs_eval_push.
    (* let *)
    unfolds.
    repeat ljs_eval_push.
    cases_let.
    injects.
    repeat ljs_eval_push.
    (* rec *)
    unfolds.
    repeat ljs_eval_push.
    cases_let.
    injects.
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
    repeat ljs_eval_push.
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
    repeat ljs_eval_push.
    (* eval *)
    unfolds.
    repeat ljs_eval_push.
    repeat cases_match_option.
    cases_let.
    repeat injects.
    repeat ljs_eval_push.
    (* hint *)
    repeat ljs_eval_push.
Admitted. (* faster *)

(* Completeness *)

Lemma eval_complete : forall c st e o,
    red_expr c st e o -> exists k, runs_type_eval (runs k) c st e = result_some o.
Proof.
    introv H.
    lets (k&H1) : red_expr_add_h H.
    exists k.
    applys eval_complete_lemma H1.
Qed.
