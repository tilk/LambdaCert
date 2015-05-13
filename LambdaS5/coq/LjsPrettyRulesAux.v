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

Fixpoint pure_expr_pred c st e v : Prop :=
    match e with
    | expr_undefined => v = value_undefined
    | expr_null => v = value_null
    | expr_empty => v = value_empty
    | expr_bool b => v = value_bool b
    | expr_string s => v = value_string s
    | expr_number n => v = value_number n
    | expr_lambda is e => v = add_closure c None is e
    | expr_id s => binds c s v 
    | expr_if e1 e2 e3 => exists b, pure_expr_pred c st e1 (value_bool b) /\ 
        (b /\ pure_expr_pred c st e2 v \/ ~b /\ pure_expr_pred c st e3 v) 
    | expr_let s e1 e2 => exists v', pure_expr_pred c st e1 v' /\ pure_expr_pred (c \(s := v')) st e2 v
    | expr_seq e1 e2 => pure_expr_pred c st e2 v
    | expr_jseq e1 e2 => exists v1 v2, pure_expr_pred c st e1 v1 /\ pure_expr_pred c st e2 v2 /\
        v = overwrite_value_if_empty v1 v2
    | expr_op1 op e => exists v', pure_expr_pred c st e v' /\ eval_unary_op op st v' v
    | expr_op2 op e1 e2 => exists v1 v2, pure_expr_pred c st e1 v1 /\ pure_expr_pred c st e2 v2 /\
        eval_binary_op op st v1 v2 v
    | expr_get_attr pa e1 e2 => exists ptr obj s attrs, 
        pure_expr_pred c st e1 (value_object ptr) /\ 
        pure_expr_pred c st e2 (value_string s) /\
        binds st ptr obj /\ binds (object_properties obj) s attrs /\
        attributes_pattr_readable attrs pa /\ v = get_attributes_pattr attrs pa
    | expr_get_obj_attr oa e => exists ptr obj,
        pure_expr_pred c st e (value_object ptr) /\
        binds st ptr obj /\
        v = get_object_oattr obj oa
    | _ => False
    end.

Fixpoint bool_expr_pred c st e : Prop :=
    match e with
    | expr_bool true => True
    | expr_bool false => False
    | expr_if e1 e2 e3 => 
        bool_expr_pred c st e1 /\ bool_expr_pred c st e2 \/ ~bool_expr_pred c st e1 /\ bool_expr_pred c st e3
    | expr_let s e1 e2 =>
        exists v, pure_expr_pred c st e1 v /\ bool_expr_pred (c \(s := v)) st e2
    | expr_op1 unary_op_is_primitive e => exists v, pure_expr_pred c st e v /\ is_primitive v
    | expr_op1 unary_op_is_closure e => exists v, pure_expr_pred c st e v /\ is_closure v
    | expr_op1 unary_op_is_object e => exists v, pure_expr_pred c st e v /\ is_object v
    | expr_op1 unary_op_prim_to_bool e => exists v, pure_expr_pred c st e v /\ value_to_bool_cast v
    | expr_op1 unary_op_not e => ~bool_expr_pred c st e
    | expr_op2 binary_op_stx_eq e1 e2 => 
        exists v1 v2, pure_expr_pred c st e1 v1 /\ pure_expr_pred c st e2 v2 /\ stx_eq v1 v2
    | expr_op2 binary_op_same_value e1 e2 => 
        exists v1 v2, pure_expr_pred c st e1 v1 /\ pure_expr_pred c st e2 v2 /\ same_value v1 v2
    | expr_op2 binary_op_has_property e1 e2 => 
        exists ptr obj s, pure_expr_pred c st e1 (value_object ptr) /\ pure_expr_pred c st e2 (value_string s) /\
        binds st ptr obj /\ exists att, object_property_is st obj s (Some att)
    | expr_op2 binary_op_has_own_property e1 e2 => 
        exists ptr obj s, pure_expr_pred c st e1 (value_object ptr) /\ pure_expr_pred c st e2 (value_string s) /\
        binds st ptr obj /\ index (object_properties obj) s
    | expr_op2 binary_op_has_internal e1 e2 => 
        exists ptr obj s, pure_expr_pred c st e1 (value_object ptr) /\ pure_expr_pred c st e2 (value_string s) /\
        binds st ptr obj /\ index (object_internal obj) s
    | expr_op2 binary_op_is_accessor e1 e2 => 
        exists ptr obj s att, pure_expr_pred c st e1 (value_object ptr) /\ pure_expr_pred c st e2 (value_string s) /\
        binds st ptr obj /\ object_property_is st obj s (Some att) /\ is_accessor att
    | expr_op2 binary_op_string_lt e1 e2 => 
        exists s1 s2, pure_expr_pred c st e1 (value_string s1) /\ pure_expr_pred c st e2 (value_string s2) /\
        string_lt s1 s2
    | expr_op2 binary_op_locale_compare e1 e2 => 
        exists s1 s2, pure_expr_pred c st e1 (value_string s1) /\ pure_expr_pred c st e2 (value_string s2) /\
        string_lt s1 s2
    | expr_op2 binary_op_lt e1 e2 => 
        exists n1 n2, pure_expr_pred c st e1 (value_number n1) /\ pure_expr_pred c st e2 (value_number n2) /\
        num_lt n1 n2
    | expr_op2 binary_op_gt e1 e2 => 
        exists n1 n2, pure_expr_pred c st e1 (value_number n1) /\ pure_expr_pred c st e2 (value_number n2) /\
        num_gt n1 n2
    | expr_op2 binary_op_le e1 e2 => 
        exists n1 n2, pure_expr_pred c st e1 (value_number n1) /\ pure_expr_pred c st e2 (value_number n2) /\
        num_le n1 n2
    | expr_op2 binary_op_ge e1 e2 => 
        exists n1 n2, pure_expr_pred c st e1 (value_number n1) /\ pure_expr_pred c st e2 (value_number n2) /\
        num_ge n1 n2
    | _ => False
    end.

Lemma object_property_is_deterministic : forall st obj name oattr oattr',
    object_property_is st obj name oattr -> object_property_is st obj name oattr' -> oattr = oattr'.
Proof.
    introv Ho1.
    induction Ho1; introv Ho2; inverts Ho2; 
    repeat binds_determine; substs; tryfalse; try reflexivity; try (false; prove_bag). 
    rewrite H0 in H6.
    injects.
    binds_determine; substs.
    auto.
Qed.

Lemma value_is_closure_deterministic : forall st v clo clo',
    value_is_closure st v clo -> value_is_closure st v clo' -> clo = clo'.
Proof.
    introv Hc1.
    induction Hc1; introv Hc2; inverts Hc2.
    reflexivity.
    binds_determine.
    substs.
    auto.
Qed.

Lemma closure_ctx_deterministic : forall clo lv c c',
    closure_ctx clo lv c -> closure_ctx clo lv c' -> c = c'.
Proof.
    introv Hc1.
    induction Hc1; introv Hc2; inverts Hc2;
    repeat match goal with H : Zip _ _ _ |- _ => apply Zip_zip in H end;
    rewrite H in *; injects; reflexivity.
Qed.

Lemma eval_unary_op_deterministic : forall op st v0 v v',
    eval_unary_op op st v0 v -> eval_unary_op op st v0 v' -> v = v'.
Proof.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    reflexivity.
Qed.

Lemma eval_binary_op_deterministic : forall op st v1 v2 v v',
    eval_binary_op op st v1 v2 v -> eval_binary_op op st v1 v2 v' -> v = v'.
Proof.
    introv He1 He2.
    destruct op; inverts He1 as Hu1; try inverts Hu1; inverts He2 as Hu2; try inverts Hu2;
    repeat binds_determine; try reflexivity.
    rewrite H1 in *. injects. reflexivity. 
    lets X : object_property_is_deterministic H1 H5. injects. reflexivity.
Qed.

Ltac false_abort := 
    match goal with
    | H : abort _ |- _ => solve [invert H as H; invert H]
    end.

Lemma pure_expr_lemma : forall c st st' e r,
    pure_expr e ->
    red_expr c st e (out_ter st' r) ->
    st = st' /\ exists v,
    r = res_value v /\ pure_expr_pred c st e v.
Proof.
    introv Hpe Hred.
    inductions Hpe gen c st st' r Hred;
    inverts Hred as Hr1 Hr2; simpl; jauto.
    (* if *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    jauto.
    specializes IHHpe3 Hr2. destruct_hyp IHHpe3.
    jauto.
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
    jauto.
    (* binary *)    
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe1 Hr1. destruct_hyp IHHpe1.
    inverts Hr2 as Hr2 Hr3; [idtac | false_abort].
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2.
    inverts Hr3 as Hr3; [idtac | false_abort].
    jauto.
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
    jauto.
    (* get_obj_attr *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe Hr1. destruct_hyp IHHpe.
    inverts Hr2 as Hr2; [idtac | false_abort].
    jauto.
Qed.

Lemma pure_expr_pred_deterministic : forall c st e v v',
    pure_expr_pred c st e v -> pure_expr_pred c st e v' -> v = v'.
Proof.
    introv Hpe1 Hpe2.
    inductions e gen c st Hpe1 Hpe2; simpls; substs; repeat binds_determine; try reflexivity; tryfalse.
    (* get_attr *)
    destruct Hpe1 as (?ptr&?obj&?s&?attrs&Hpe1&Hpf1&Hb1&Hbp1&Hre1&Heq1).
    destruct Hpe2 as (?ptr&?obj&?s&?attrs&Hpe2&Hpf2&Hb2&Hbp2&Hre2&Heq2).
    specializes IHe1 Hpe1 Hpe2.
    specializes IHe2 Hpf1 Hpf2.
    repeat injects. substs. repeat binds_determine.
    reflexivity.
    (* get_obj_attr *)
    destruct Hpe1 as (?ptr&?obj&Hpe1&Hb1&Heq1).
    destruct Hpe2 as (?ptr&?obj&Hpe2&Hb2&Heq2).
    specializes IHe Hpe1 Hpe2.
    repeat injects. substs. repeat binds_determine.
    reflexivity.
    (* unary *)
    destruct Hpe1 as (?v&Hpe1&Hun1).
    destruct Hpe2 as (?v&Hpe2&Hun2).
    specializes IHe Hpe1 Hpe2. substs.
    applys eval_unary_op_deterministic Hun1 Hun2.
    (* binary *)
    destruct Hpe1 as (?v&?v&Hpe1&Hpf1&Hun1).
    destruct Hpe2 as (?v&?v&Hpe2&Hpf2&Hun2).
    specializes IHe1 Hpe1 Hpe2.
    specializes IHe2 Hpf1 Hpf2. substs.
    applys eval_binary_op_deterministic Hun1 Hun2.
    (* if *)
    destruct Hpe1 as (b1&Hpe1&Hcond1).
    destruct Hpe2 as (b2&Hpe2&Hcond2).
    specializes IHe1 Hpe1 Hpe2.
    injects.
    destruct b2;
    rew_refl in Hcond1; rew_refl in Hcond2;
    rew_logic in Hcond1; rew_logic in Hcond2.
    specializes IHe2 Hcond1 Hcond2.
    specializes IHe3 Hcond1 Hcond2.
    (* seq *)
    eauto.
    (* jseq *)
    destruct Hpe1 as (?v&?v&Hpe1&Hpf1&Heq1).
    destruct Hpe2 as (?v&?v&Hpe2&Hpf2&Heq2).
    specializes IHe1 Hpe1 Hpe2.
    specializes IHe2 Hpf1 Hpf2.
    substs. reflexivity.
    (* let *)
    destruct Hpe1 as (?v&Hpe1&Hpf1).
    destruct Hpe2 as (?v&Hpe2&Hpf2).
    specializes IHe1 Hpe1 Hpe2. substs.
    specializes IHe2 Hpf1 Hpf2.
Qed.

Lemma pure_expr_pred_op1_lemma : forall P c st e v,
    pure_expr_pred c st e v ->
    P v = exists v', pure_expr_pred c st e v' /\ P v'.
Proof.
    introv Hpur.
    rew_logic. split. jauto.
    introv (v'&Hpur'&Hp').
    lets Heq : pure_expr_pred_deterministic Hpur Hpur'. substs. 
    assumption.
Qed.

Lemma pure_expr_pred_op2_lemma : forall P c st e1 e2 v1 v2,
    pure_expr_pred c st e1 v1 ->
    pure_expr_pred c st e2 v2 ->
    P v1 v2 = exists v1' v2', pure_expr_pred c st e1 v1' /\ pure_expr_pred c st e2 v2' /\ P v1' v2'.
Proof.
    introv Hpur1 Hpur2.
    rew_logic. split. jauto.
    introv (v1'&v2'&Hpur1'&Hpur2'&Hp').
    lets Heq1 : pure_expr_pred_deterministic Hpur1 Hpur1'. 
    lets Heq2 : pure_expr_pred_deterministic Hpur2 Hpur2'. 
    substs. 
    assumption.
Qed.

Lemma pure_expr_pred_op2_number_lemma : forall P c st e1 e2 n1 n2,
    pure_expr_pred c st e1 (value_number n1) ->
    pure_expr_pred c st e2 (value_number n2) ->
    P n1 n2 = exists n1' n2', 
        pure_expr_pred c st e1 (value_number n1') /\ pure_expr_pred c st e2 (value_number n2') /\ P n1' n2'.
Proof.
    introv Hpur1 Hpur2.
    rew_logic. split. jauto.
    introv (v1'&v2'&Hpur1'&Hpur2'&Hp').
    lets Heq1 : pure_expr_pred_deterministic Hpur1 Hpur1'. 
    lets Heq2 : pure_expr_pred_deterministic Hpur2 Hpur2'. 
    repeat injects. 
    assumption.
Qed.

Lemma pure_expr_pred_op2_string_lemma : forall P c st e1 e2 s1 s2,
    pure_expr_pred c st e1 (value_string s1) ->
    pure_expr_pred c st e2 (value_string s2) ->
    P s1 s2 = exists s1' s2', 
        pure_expr_pred c st e1 (value_string s1') /\ pure_expr_pred c st e2 (value_string s2') /\ P s1' s2'.
Proof.
    introv Hpur1 Hpur2.
    rew_logic. split. jauto.
    introv (v1'&v2'&Hpur1'&Hpur2'&Hp').
    lets Heq1 : pure_expr_pred_deterministic Hpur1 Hpur1'. 
    lets Heq2 : pure_expr_pred_deterministic Hpur2 Hpur2'. 
    repeat injects. 
    assumption.
Qed.

Lemma pure_expr_pred_op2_object_string_lemma : forall P c st e1 e2 obj ptr s,
    pure_expr_pred c st e1 (value_object ptr) ->
    pure_expr_pred c st e2 (value_string s) ->
    binds st ptr obj ->
    P obj s = exists ptr' obj' s', 
        pure_expr_pred c st e1 (value_object ptr') /\ pure_expr_pred c st e2 (value_string s') /\ 
        binds st ptr' obj' /\ P obj' s'.
Proof.
    introv Hpur1 Hpur2 Hbinds.
    rew_logic. split. jauto.
    introv (obj'&ptr'&s'&Hpur1'&Hpur2'&Hbinds'&Hp').
    lets Heq1 : pure_expr_pred_deterministic Hpur1 Hpur1'. 
    lets Heq2 : pure_expr_pred_deterministic Hpur2 Hpur2'. 
    repeat injects. 
    binds_determine.
    assumption.
Qed.

Lemma pure_expr_pred_op2_object_attrs_string_lemma : forall P c st e1 e2 obj ptr att s,
    pure_expr_pred c st e1 (value_object ptr) ->
    pure_expr_pred c st e2 (value_string s) ->
    binds st ptr obj ->
    object_property_is st obj s (Some att) ->
    P obj s att = exists ptr' obj' s' att', 
        pure_expr_pred c st e1 (value_object ptr') /\ pure_expr_pred c st e2 (value_string s') /\ 
        binds st ptr' obj' /\ object_property_is st obj' s' (Some att') /\ P obj' s' att'.
Proof.
    introv Hpur1 Hpur2 Hbinds Hprop.
    rew_logic. split. jauto.
    introv (obj'&ptr'&s'&att'&Hpur1'&Hpur2'&Hbinds'&Hprop'&Hp').
    lets Heq1 : pure_expr_pred_deterministic Hpur1 Hpur1'. 
    lets Heq2 : pure_expr_pred_deterministic Hpur2 Hpur2'. 
    repeat injects. 
    binds_determine.
    lets Heq3 : object_property_is_deterministic Hprop Hprop'.
    injects.
    assumption.
Qed.

Lemma bool_red_expr_lemma : forall c st st' e r,
    bool_expr e ->
    red_expr c st e (out_ter st' r) ->
    st = st' /\ r = res_value (value_bool (isTrue (bool_expr_pred c st e))).
Proof.
    introv Hpe Hred.
    inductions Hpe gen c st st' r Hred;
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
    specializes IHHpe2 Hr2. destruct_hyp IHHpe2. jauto.
    specializes IHHpe3 Hr2. destruct_hyp IHHpe3. jauto.
    (* let *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur.
    inverts Hr2 as Hr2; [idtac | false_abort].
    specializes IHHpe Hr2. destruct_hyp IHHpe. 
    forwards Heq : pure_expr_pred_op1_lemma (fun v => bool_expr_pred (c\(s:=v)) st' e2). eassumption.
    rewrite Heq. jauto. 
    (* not *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    specializes IHHpe Hr1. destruct_hyp IHHpe.
    inverts Hr2 as Hr2; [idtac | false_abort].
    inverts Hr2. rew_refl. jauto.
    (* op1 *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur. clear Hr1.
    inverts Hr2 as Hr2; [idtac | false_abort].
    destruct op; tryfalse; inverts Hr2; try false_invert.
    (* is_primitive *)
    forwards Heq : pure_expr_pred_op1_lemma is_primitive. eassumption. 
    rewrite decide_spec. rewrite Heq. jauto. 
    (* is_closure *)
    forwards Heq : pure_expr_pred_op1_lemma is_closure. eassumption. 
    rewrite decide_spec. rewrite Heq. jauto. 
    (* is_object *)
    forwards Heq : pure_expr_pred_op1_lemma is_object. eassumption. 
    rewrite decide_spec. rewrite Heq. jauto. 
    (* prim_to_bool *)
    forwards Heq : pure_expr_pred_op1_lemma value_to_bool_cast. eassumption. 
    rewrite <- (isTrue_istrue (value_to_bool_cast v)).
    rewrite Heq. jauto.
    (* op2 *)
    forwards Hx : out_red_ter Hr2. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr1. assumption. destruct_hyp Hpur. clear Hr1.
    inverts Hr2 as Hr2 Hr3; [idtac | false_abort].
    forwards Hx : out_red_ter Hr3. reflexivity. destruct_hyp Hx.
    forwards Hpur : pure_expr_lemma Hr2. assumption. destruct_hyp Hpur. clear Hr2.
    inverts Hr3 as Hr3; [idtac | false_abort].
    destruct op; tryfalse; inverts Hr3 as Hr3; try false_invert.
    (* lt *)
    inverts Hr3.
    forwards Heq : pure_expr_pred_op2_number_lemma num_lt Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (num_lt n1 n2)).
    rewrite Heq. jauto.
    (* le *)
    inverts Hr3.
    forwards Heq : pure_expr_pred_op2_number_lemma num_le Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (num_le n1 n2)).
    rewrite Heq. jauto.
    (* gt *)
    inverts Hr3.
    forwards Heq : pure_expr_pred_op2_number_lemma num_gt Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (num_gt n1 n2)).
    rewrite Heq. jauto.
    (* ge *)
    inverts Hr3.
    forwards Heq : pure_expr_pred_op2_number_lemma num_ge Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (num_ge n1 n2)).
    rewrite Heq. jauto.
    (* stx_eq *) 
    forwards Heq : pure_expr_pred_op2_lemma stx_eq Hpur2 Hpur3.
    rewrite decide_spec. rewrite Heq. jauto.
    (* same_value *)
    forwards Heq : pure_expr_pred_op2_lemma same_value Hpur2 Hpur3.
    rewrite decide_spec. rewrite Heq. jauto.
    (* object_has_property *)
    forwards Heq : pure_expr_pred_op2_object_string_lemma
        (fun obj s => exists att, object_property_is st' obj s (Some att)) Hpur2 Hpur3 Hr3.
    rewrite Heq. jauto.
    (* has_own_property *)
    forwards Heq : pure_expr_pred_op2_object_string_lemma
        (fun obj s => index (object_properties obj) s) Hpur2 Hpur3 Hr3.
    rewrite decide_spec. rewrite Heq. jauto.
    (* has_internal *)
    forwards Heq : pure_expr_pred_op2_object_string_lemma
        (fun obj s => index (object_internal obj) s) Hpur2 Hpur3 Hr3.
    rewrite decide_spec. rewrite Heq. jauto.
    (* is_accessor *)
    forwards Heq : pure_expr_pred_op2_object_attrs_string_lemma
        (fun obj s attrs => is_accessor attrs) Hpur2 Hpur3 Hr3. eassumption.
    rewrite decide_spec. rewrite Heq. jauto.
    (* string_lt *)
    forwards Heq : pure_expr_pred_op2_string_lemma string_lt Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (string_lt s1 s2)).
    rewrite Heq. jauto.
    (* locale_compare *)
    forwards Heq : pure_expr_pred_op2_string_lemma string_lt Hpur2 Hpur3.
    rewrite <- (isTrue_istrue (string_lt s1 s2)).
    rewrite Heq. jauto.
Qed.

Module Export Tactics.

Ltac object_property_is_determine_then :=
    match goal with
    | H1 : object_property_is ?st ?obj ?name ?oattr1, H2 : object_property_is ?st ?obj ?name ?oattr2 |- _ =>
        not constr_eq oattr1 oattr2; 
        not is_hyp (oattr1 = oattr2);
        let H := fresh "H" in asserts H : (oattr1 = oattr2); [eauto using object_property_is_deterministic | idtac];
        revert H
    end.

Ltac object_property_is_determine_eq := object_property_is_determine_then; intro.
Ltac object_property_is_determine := object_property_is_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac value_is_closure_determine_then :=
    match goal with
    | H1 : value_is_closure ?st ?v ?clo1, H2 : value_is_closure ?st ?v ?clo2 |- _ =>
        not constr_eq clo1 clo2; 
        not is_hyp (clo1 = clo2);
        let H := fresh "H" in asserts H : (clo1 = clo2); [eauto using value_is_closure_deterministic | idtac];
        revert H
    end.

Ltac value_is_closure_determine_eq := value_is_closure_determine_then; intro.
Ltac value_is_closure_determine := value_is_closure_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac closure_ctx_determine_then :=
    match goal with
    | H1 : closure_ctx ?clo ?lv ?c1, H2 : closure_ctx ?clo ?lv ?c2 |- _ =>
        not constr_eq c1 c2; 
        not is_hyp (c1 = c2);
        let H := fresh "H" in asserts H : (c1 = c2); [eauto using closure_ctx_deterministic | idtac];
        revert H
    end.

Ltac closure_ctx_determine_eq := closure_ctx_determine_then; intro.
Ltac closure_ctx_determine := closure_ctx_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac eval_unary_op_determine_then :=
    match goal with
    | H1 : eval_unary_op ?op ?st ?v0 ?v1, H2 : eval_unary_op ?op ?st ?v0 ?v2 |- _ =>
        not constr_eq v1 v2; 
        not is_hyp (v1 = v2);
        let H := fresh "H" in asserts H : (v1 = v2); [eauto using eval_unary_op_deterministic | idtac];
        revert H
    end.

Ltac eval_unary_op_determine_eq := eval_unary_op_determine_then; intro.
Ltac eval_unary_op_determine := eval_unary_op_determine_then; let H := fresh in intro H; try subst_hyp H.

Ltac eval_binary_op_determine_then :=
    match goal with
    | H1 : eval_binary_op ?op ?st ?v0 ?v0' ?v1, H2 : eval_binary_op ?op ?st ?v0 ?v0' ?v2 |- _ =>
        not constr_eq v1 v2; 
        not is_hyp (v1 = v2);
        let H := fresh "H" in asserts H : (v1 = v2); [eauto using eval_binary_op_deterministic | idtac];
        revert H
    end.

Ltac eval_binary_op_determine_eq := eval_binary_op_determine_then; intro.
Ltac eval_binary_op_determine := eval_binary_op_determine_then; let H := fresh in intro H; try subst_hyp H.

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

Tactic Notation "ljs_bool_red_expr" "in" hyp(Hred) := ljs_bool_red_expr Hred; clear Hred.

End Tactics.
