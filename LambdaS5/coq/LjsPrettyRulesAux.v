Generalizable All Variables.
Set Implicit Arguments.
Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import LjsSyntaxAux.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import JsNumber.
Import List.ListNotations.

Open Scope list_scope.

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
Implicit Type attrs : attributes.

Lemma out_red_ter : forall c st st' ee r o,
    red_expr c st ee (out_ter st' r) -> out_of_ext_expr ee = Some o -> exists st'' r', o = out_ter st'' r'.
Proof.
    introv Hred Hout.
    unfolds in Hout;
    inverts Hred; tryfalse; injects; jauto.
Qed.

Require Import LibEpsilon. (* TODO move *)

Instance attributes_inhab : Inhab attributes.
Proof. intros. apply (prove_Inhab (attributes_data_of (attributes_data_intro value_null false false false))). Qed.

Instance object_inhab : Inhab object.
Proof. intros. apply (prove_Inhab default_object). Qed.

Fixpoint pure_expr_val c st e : value :=
    match e with
    | expr_undefined => value_undefined
    | expr_null => value_null
    | expr_empty => value_empty
    | expr_bool b => value_bool b
    | expr_string s => value_string s
    | expr_number n => value_number n
    | expr_lambda is e => add_closure c None is e
    | expr_id s => epsilon (binds c s) 
    | expr_if e1 e2 e3 => 
        match pure_expr_val c st e1 with
        | value_bool true => pure_expr_val c st e2
        | value_bool false => pure_expr_val c st e3
        | _ => arbitrary
        end
    | expr_let s e1 e2 => pure_expr_val (c \(s := pure_expr_val c st e1)) st e2
    | expr_seq e1 e2 => pure_expr_val c st e2
    | expr_jseq e1 e2 => overwrite_value_if_empty (pure_expr_val c st e1) (pure_expr_val c st e2)
    | expr_op1 op e => epsilon (eval_unary_op op st (pure_expr_val c st e))
    | expr_op2 op e1 e2 => epsilon (eval_binary_op op st (pure_expr_val c st e1) (pure_expr_val c st e2))
    | expr_get_attr pa e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_object ptr, value_string s => 
            get_attributes_pattr (epsilon (binds (object_properties (epsilon (binds st ptr))) s)) pa
        | _, _ => arbitrary
        end
    | expr_get_obj_attr oa e =>
        match pure_expr_val c st e with
        | value_object ptr => get_object_oattr (epsilon (binds st ptr)) oa
        | _ => arbitrary
        end
    | _ => value_undefined
    end.

Fixpoint pure_expr_pre c st e : Prop :=
    match e with
    | expr_id s => exists v, binds c s v
    | expr_if e1 e2 e3 => pure_expr_pre c st e1 /\
        (exists b, pure_expr_val c st e1 = value_bool b /\ 
            (b -> pure_expr_pre c st e2) /\ (~b -> pure_expr_pre c st e3))
    | expr_let s e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre (c\(s := pure_expr_val c st e1)) st e2
    | expr_seq e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre c st e2
    | expr_jseq e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre c st e2
    | expr_op1 op e => pure_expr_pre c st e /\ 
        exists v, eval_unary_op op st (pure_expr_val c st e) v
    | expr_op2 op e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre c st e2 /\
        exists v, eval_binary_op op st (pure_expr_val c st e1) (pure_expr_val c st e2) v
    | expr_get_attr pa e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre c st e2 /\
        (exists ptr obj s attrs, 
            pure_expr_val c st e1 = value_object ptr /\ pure_expr_val c st e2 = value_string s /\
            binds st ptr obj /\ binds (object_properties obj) s attrs /\
            attributes_pattr_readable attrs pa)
    | expr_get_obj_attr oa e => pure_expr_pre c st e /\
        (exists ptr obj, pure_expr_val c st e = value_object ptr /\ binds st ptr obj)
    | _ => True
    end.

Fixpoint bool_expr_pred c st e : Prop :=
    match e with
    | expr_bool true => True
    | expr_bool false => False
    | expr_if e1 e2 e3 => 
        bool_expr_pred c st e1 /\ bool_expr_pred c st e2 \/ ~bool_expr_pred c st e1 /\ bool_expr_pred c st e3
    | expr_let s e1 e2 =>
        bool_expr_pred (c \(s := pure_expr_val c st e1)) st e2
    | expr_op1 unary_op_is_primitive e => is_primitive (pure_expr_val c st e)
    | expr_op1 unary_op_is_closure e => is_closure (pure_expr_val c st e)
    | expr_op1 unary_op_is_object e => is_object (pure_expr_val c st e)
    | expr_op1 unary_op_prim_to_bool e => value_to_bool_cast (pure_expr_val c st e)
    | expr_op1 unary_op_not e => ~bool_expr_pred c st e
    | expr_op2 binary_op_stx_eq e1 e2 => 
        stx_eq (pure_expr_val c st e1) (pure_expr_val c st e2)
    | expr_op2 binary_op_same_value e1 e2 => 
        same_value (pure_expr_val c st e1) (pure_expr_val c st e2)
    | expr_op2 binary_op_has_own_property e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_object ptr, value_string s =>
            index (object_properties (epsilon (binds st ptr))) s
        | _, _ => False
        end
    | expr_op2 binary_op_has_internal e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_object ptr, value_string s =>
            index (object_internal (epsilon (binds st ptr))) s
        | _, _ => False
        end
    | expr_op2 binary_op_is_accessor e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_object ptr, value_string s =>
            is_accessor (epsilon (binds (object_properties (epsilon (binds st ptr))) s))
        | _, _ => False
        end
    | expr_op2 binary_op_string_lt e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_string s1, value_string s2 => string_lt s1 s2
        | _, _ => False
        end
    | expr_op2 binary_op_locale_compare e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_string s1, value_string s2 => string_lt s1 s2
        | _, _ => False
        end
    | expr_op2 binary_op_lt e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_number n1, value_number n2 => num_lt n1 n2
        | _, _ => False
        end
    | expr_op2 binary_op_gt e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_number n1, value_number n2 => num_gt n1 n2
        | _, _ => False
        end
    | expr_op2 binary_op_le e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_number n1, value_number n2 => num_le n1 n2
        | _, _ => False
        end
    | expr_op2 binary_op_ge e1 e2 => 
        match pure_expr_val c st e1, pure_expr_val c st e2 with
        | value_number n1, value_number n2 => num_ge n1 n2
        | _, _ => False
        end
    | _ => False
    end.

Fixpoint bool_expr_pre c st e : Prop :=
    match e with
    | expr_bool _ => True
    | expr_id s => exists v, binds c s v
    | expr_if e1 e2 e3 => bool_expr_pre c st e1 /\
        (bool_expr_pred c st e1 -> bool_expr_pre c st e2) /\ (~bool_expr_pred c st e1 -> bool_expr_pre c st e3)
    | expr_let s e1 e2 => pure_expr_pre c st e1 /\ bool_expr_pre (c\(s := pure_expr_val c st e1)) st e2
    | expr_op1 unary_op_not e => bool_expr_pre c st e
    | expr_op1 op e => pure_expr_pre c st e /\
        exists v, eval_unary_op op st (pure_expr_val c st e) v
    | expr_op2 op e1 e2 => pure_expr_pre c st e1 /\ pure_expr_pre c st e2 /\
        exists v, eval_binary_op op st (pure_expr_val c st e1) (pure_expr_val c st e2) v
    | _ => False
    end.

Instance object_property_is_deterministic : forall st obj name, Deterministic (object_property_is st obj name).
Proof.
    introv. constructor.
    introv Ho1.
    induction Ho1; introv Ho2; inverts Ho2; 
    repeat determine; substs; tryfalse; try reflexivity; try (false; prove_bag).
    auto.
Qed.

Instance closure_ctx_deterministic : forall clo lv, Deterministic (closure_ctx clo lv).
Proof.
    introv. constructor.
    introv Hc1.
    induction Hc1; introv Hc2; inverts Hc2;
    repeat match goal with H : Zip _ _ _ |- _ => apply Zip_zip in H end;
    rewrite H in *; injects; reflexivity.
Qed.

Instance eval_unary_op_deterministic : forall op st v0, Deterministic (eval_unary_op op st v0).
Proof.
    introv. constructor.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    reflexivity.
Qed.

Instance eval_binary_op_deterministic : forall op st v1 v2, Deterministic (eval_binary_op op st v1 v2).
Proof.
    introv. constructor.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    repeat determine; try reflexivity.
Qed.

Ltac false_abort := 
    match goal with
    | H : abort _ |- _ => solve [invert H as H; invert H]
    end.

Lemma pure_expr_lemma : forall c st st' e r,
    pure_expr e ->
    red_expr c st e (out_ter st' r) ->
    st = st' /\ pure_expr_pre c st e /\
    r = res_value (pure_expr_val c st e).
Proof.
    introv Hpe Hred.
    inductions Hpe gen c st st' r;
    inverts Hred as Hr1 Hr2; simpl; jauto.
    (* id *)
    determine_epsilon.
    jauto.
    (* if *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2. simpl. 
    jauto_set; eauto. rew_refl. iauto.
    specializes IHHpe3 Hr2. destruct_hyp IHHpe3. simpl. 
    jauto_set; eauto. rew_refl. iauto.
    false_abort.
    (* seq *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    inverts Hr2 as Hr2.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    jauto.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    false_abort.
    (* jseq *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2 Hr3; [idtac | false_abort].
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    inverts Hr3.
    jauto.
    (* let *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2; [idtac | false_abort].
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    jauto.
    (* unary *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe Hr1. destruct_hyp IHHpe.
    inverts Hr2 as Hr2; [idtac | false_abort].
    determine_epsilon. jauto.
    (* binary *)    
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2 Hr3; [idtac | false_abort].
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    inverts Hr3 as Hr3; [idtac | false_abort].
    determine_epsilon. jauto.
    (* get_attr *)
    inverts Hr1 as Hr1 Hr2.
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2; [idtac | false_abort].
    inverts Hr2 as Hr2 Hr3.
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    inverts Hr3 as Hr3; [idtac | false_abort].
    inverts Hr3 as Hr3. inverts Hr3 as Hr3.
    do 2 determine_epsilon. jauto.
    (* get_obj_attr *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe Hr1. destruct_hyp IHHpe.
    inverts Hr2 as Hr2; [idtac | false_abort].
    determine_epsilon. jauto.
Qed.

Local Hint Constructors red_expr.

Lemma pure_expr_lemma_inv : forall c st e,
    pure_expr e -> pure_expr_pre c st e -> red_expr c st e (out_ter st (res_value (pure_expr_val c st e))).
Proof.
    introv Hpe Hpre.
    inductions Hpe gen c st; simpls; jauto.
    (* id *)
    destruct_hyp Hpre.
    determine_epsilon. eauto.
    (* if *)
    destruct_hyp Hpre.
    specializes IHHpe1 ___. eassumption.
    rewrite Hpre2 in *. (* TODO *)
    destruct b; rew_refl in *; eauto.
    (* op1 *)
    destruct_hyp Hpre.
    determine_epsilon. eauto.
    (* op2 *)
    destruct_hyp Hpre.
    determine_epsilon. eauto 7.
    (* get_attr *)
    destruct_hyp Hpre.
    specializes IHHpe1 ___. eassumption.
    specializes IHHpe2 ___. eassumption.
    rewrite Hpre1, Hpre3 in *. (* TODO *)
    do 2 determine_epsilon. 
    skip. (* TODO rev in eval_many *)
    (* get_obj_attr *)
    destruct_hyp Hpre.
    specializes IHHpe ___. eassumption.
    rewrite Hpre2 in *. (* TODO *)
    determine_epsilon. eauto.
Qed.

Local Hint Constructors binary_op_type.
Local Hint Constructors eval_unary_op.
Local Hint Constructors eval_binary_op.

Lemma bool_red_expr_lemma : forall c st st' e r,
    bool_expr e ->
    red_expr c st e (out_ter st' r) -> 
    st = st' /\ bool_expr_pre c st e /\ r = res_value (value_bool (isTrue (bool_expr_pred c st e))).
Proof.
    introv Hpe Hred.
    inductions Hpe gen c st st' r;
    inverts Hred as Hr1 Hr2; simpl; jauto.
    (* bool *)
    cases_if; rew_refl; jauto.
    (* if *) 
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    rew_unreflect.
    cases_isTrue in * as Eq;
    rew_bool;
    (inverts Hr2 as Hr2; [idtac | false_abort]). 
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2. iauto.
    specializes IHHpe3 Hr2. destruct_hyp IHHpe3. iauto.
    (* let *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur.
    inverts Hr2 as Hr2; [idtac | false_abort].
    specializes IHHpe Hr2. destruct_hyp IHHpe. jauto. 
    (* not *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe Hr1. destruct_hyp IHHpe.
    inverts Hr2 as Hr2; [idtac | false_abort].
    inverts Hr2. rew_refl. jauto.
    (* op1 *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur. clear Hr1.
    inverts Hr2 as Hr2; [idtac | false_abort].
    destruct op; tryfalse; inverts keep Hr2; try false_invert.
    (* is_primitive *)
    rewrite decide_spec. jauto. 
    (* is_closure *)
    rewrite decide_spec. jauto. 
    (* is_object *)
    rewrite decide_spec. jauto. 
    (* prim_to_bool *)
    rew_refl. jauto.
    (* op2 *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur. clear Hr1.
    inverts Hr2 as Hr2 Hr3; [idtac | false_abort].
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr2. assumption. destruct_hyp Hpur. clear Hr2.
    inverts Hr3 as Hr3; [idtac | false_abort].
    destruct op; tryfalse; inverts keep Hr3 as Hr4; try false_invert.
    (* lt *)
    inverts keep Hr4.
    rew_refl. jauto.
    (* le *)
    inverts keep Hr4.
    rew_refl. jauto.
    (* gt *)
    inverts keep Hr4.
    rew_refl. jauto.
    (* ge *)
    inverts keep Hr4.
    rew_refl. jauto.
    (* stx_eq *) 
    rewrite decide_spec. jauto.
    (* same_value *)
    rewrite decide_spec. jauto.
    (* has_own_property *)
    rew_refl. determine_epsilon. jauto.
    (* has_internal *)
    rew_refl. determine_epsilon. jauto.
    (* is_accessor *)
    rew_refl. do 2 determine_epsilon. jauto.
    (* string_lt *)
    rew_refl. jauto.
    (* locale_compare *)
    rew_refl. jauto.
Qed.

Lemma bool_red_expr_lemma_inv : forall c st e,
    bool_expr e -> bool_expr_pre c st e -> 
    red_expr c st e (out_ter st (res_value (value_bool (isTrue (bool_expr_pred c st e))))).
Proof.
    introv Hpe Hpre.
    inductions Hpe gen c st; simpls; jauto.
    (* bool *)
    destruct b; rew_refl; eauto.
    (* if *)
    destruct Hpre as (Hpre1&Hpre2&Hpre3).
    specializes IHHpe1 ___. eauto.
    destruct (classic (bool_expr_pred c st e1));
    [specializes IHHpe2 ___; eauto | specializes IHHpe3 ___; eauto];
    rew_unreflect;
    [rewrite isTrue_true in * by auto | rewrite isTrue_false in * by auto];
    rew_bool;
    eauto.
    (* let *)
    destruct_hyp Hpre.
    forwards Hppre : pure_expr_lemma_inv. eassumption. eassumption.
    jauto.
    (* not *)
    rew_refl. eauto. 
    (* op1 *)
    destruct op; tryfalse; destruct_hyp Hpre.
    (* is_primitive *)
    rewrite <- decide_spec. 
    eauto using pure_expr_lemma_inv.
    (* is_closure *)
    rewrite <- decide_spec. 
    eauto using pure_expr_lemma_inv.
    (* is_object *)
    rewrite <- decide_spec. 
    eauto using pure_expr_lemma_inv.
    (* prim_to_bool *)
    rew_refl.
    eauto using pure_expr_lemma_inv.
    (* op2 *)
    destruct op; tryfalse; 
    destruct Hpre as (Hpre1&Hpre2&v&Heval);
    inverts keep Heval as Hevalop; try inverts keep Hevalop. 
    (* lt *)
    rew_refl. eauto 80 using pure_expr_lemma_inv.
    (* le *) 
    rew_refl. eauto 80 using pure_expr_lemma_inv.
    (* gt *)
    rew_refl. eauto 80 using pure_expr_lemma_inv.
    (* ge *) 
    rew_refl. eauto 80 using pure_expr_lemma_inv.
    (* stx_eq *)
    rew_refl. rewrite <- decide_spec. 
    eauto 8 using pure_expr_lemma_inv.
    (* same_value *)
    rew_refl. rewrite <- decide_spec. 
    eauto 8 using pure_expr_lemma_inv.
    (* has_own_property *)
    determine_epsilon. rewrite <- decide_spec.
    eauto 8 using pure_expr_lemma_inv.
    (* has_internal *)
    determine_epsilon. rewrite <- decide_spec.
    eauto 8 using pure_expr_lemma_inv.
    (* is_accessor *)
    do 2 determine_epsilon. rewrite <- decide_spec.
    eauto 8 using pure_expr_lemma_inv.
    (* string_lt *)
    rew_refl. eauto 80 using pure_expr_lemma_inv.
    (* locale_compare *)
    rew_refl. eauto 80 using pure_expr_lemma_inv.
Qed.

Module Export Tactics.

Tactic Notation "object_property_is_determine" :=
    match goal with
    | H1 : object_property_is ?st ?obj ?name ?oattr1, H2 : object_property_is ?st ?obj ?name ?oattr2 |- _ =>
        not (first [constr_eq H1 H2 | constr_eq oattr1 oattr2 | is_hyp (oattr1=oattr2) | is_hyp (oattr2=oattr1)]);
        determine H1 H2
    end.

Tactic Notation "closure_ctx_determine" :=
    match goal with
    | H1 : closure_ctx ?clo ?lv ?c1, H2 : closure_ctx ?clo ?lv ?c2 |- _ =>
        not (first [constr_eq H1 H2 | constr_eq c1 c2 | is_hyp (c1=c2) | is_hyp (c2=c1)]);
        determine H1 H2
    end.

Tactic Notation "eval_unary_op_determine" :=
    match goal with
    | H1 : eval_unary_op ?op ?st ?v0 ?v1, H2 : eval_unary_op ?op ?st ?v0 ?v2 |- _ =>
        not (first [constr_eq H1 H2 | constr_eq v1 v2 | is_hyp (v1=v2) | is_hyp (v2=v1)]);
        determine H1 H2
    end.

Tactic Notation "eval_binary_op_determine" :=
    match goal with
    | H1 : eval_binary_op ?op ?st ?v0 ?v0' ?v1, H2 : eval_binary_op ?op ?st ?v0 ?v0' ?v2 |- _ =>
        not (first [constr_eq H1 H2 | constr_eq v1 v2 | is_hyp (v1=v2) | is_hyp (v2=v1)]);
        determine H1 H2
    end.

Ltac ljs_out_red_ter Hred :=
    let H := fresh in
    forwards (?st&?r&H) : out_red_ter Hred; [reflexivity | ]; 
    match type of H with ?x = _ => is_var x end; 
    rewrite H in *; clear H.

Tactic Notation "ljs_out_red_ter" "in" constr(Hred) := ljs_out_red_ter Hred.

Tactic Notation "ljs_out_red_ter" := match goal with 
    | H : red_expr _ _ _ (out_ter _ _) |- _ => ljs_out_red_ter H
    end.

Ltac ljs_bool_red_expr Hred :=
    let H := fresh in 
    lets H : bool_red_expr_lemma Hred; [solve [eauto 20 with ljs] | idtac];
    simpl in H; rew_logic in H; destruct_hyp H.

Tactic Notation "ljs_bool_red_expr" "in" hyp(Hred) := ljs_bool_red_expr Hred(*; clear Hred*).

Ltac invert_binary_op :=
    match goal with
    | H : eval_binary_op _ _ _ _ _ |- _ =>
        let H1 := fresh in
        inverts H as H1; 
        try match type of H1 with
        | num_binary_op _ _ => inverts H1
        | int_binary_op _ _ => inverts H1
        | num_cmp_binary_op _ _ => inverts H1
        end
    end.

Ltac invert_unary_op :=
    match goal with
    | H : eval_unary_op _ _ _ _ |- _ =>
        let H1 := fresh in
        inverts H as H1; 
        try match type of H1 with
        | num_unary_op _ _ => inverts H1
        | int_unary_op _ _ => inverts H1
        end
    end.

End Tactics.
 