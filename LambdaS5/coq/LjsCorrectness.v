Set Implicit Arguments.
Require Import LjsShared.
Require Import Syntax.
Require Import PrettyInterm.
Require Import PrettyRules.
Require Import Store.
Require Import Context.
Require Import Values.
Require Import Operators.
Require Import Monads.
Require Import Interpreter.
Require Import Coq.Strings.String.

Require Import List.
Import ListNotations.

Open Scope list_scope.

Implicit Type A B : Type.
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

Record runs_type_correct runs :=
    make_runs_type_correct {
        runs_type_correct_eval : forall c st e o,
            runs_type_eval runs c st e = result_some o -> red_expr c st e o
}.

(* Lemmas on monadic ops *)

Definition is_some {A} ra (Pred : A -> Prop) :=
    exists a, ra = result_some a /\ Pred a.

Hint Unfold is_some.

Lemma is_some_covariant : forall A (P1 P2 : A -> Prop), 
    (forall a, P1 a -> P2 a) -> 
    forall ra, is_some ra P1 -> is_some ra P2. 
Proof. unfold is_some. jauto. Qed.

Hint Resolve is_some_covariant.

Lemma if_result_some_out : forall A B (ra : resultof A) (b : B) cont, 
    if_result_some ra cont = result_some b -> 
    is_some ra (fun a => cont a = result_some b).
Proof. introv E. destruct* ra; intros; false. Qed.

Definition if_out_ter_post (cont : store -> res -> result) o' o :=
    (exists st r, o = out_ter st r /\ cont st r = result_some o') \/
    (o = out_div /\ o' = o).

Lemma if_out_ter_out : forall re o cont, 
    if_out_ter re cont = result_some o -> 
    is_some re (if_out_ter_post cont o).
Proof.
    introv E.
    lets H: if_result_some_out E.
    gen H. 
    apply is_some_covariant.
    intros o1 E1.  
    destruct o1; inverts E1; unfolds*; tryfalse.
Qed.

Definition eqabort o' o := abort o /\ o' = o.

Hint Unfold eqabort.

Definition if_value_post (cont : store -> value -> result) o' o := 
    (exists st v, o = out_ter st (res_value v) /\ cont st v = result_some o') \/
    eqabort o' o.

Lemma if_value_out : forall re o cont,
    if_value re cont = result_some o ->
    is_some re (if_value_post cont o).
Proof.
    introv E. 
    apply if_out_ter_out in E. 
    gen E.
    apply is_some_covariant.
    intros o1 E.
    unfolds.
    destruct o1;
    (inverts E as H; [inverts H as H; inverts H as H; inverts H as H H1 | inverts H as H]); jauto; tryfalse.
    destruct* x0; inverts H; inverts H1; jauto.
Qed.

Lemma assert_get_object_ptr_out : forall v o cont,
    assert_get_object_ptr v cont = result_some o ->
    exists ptr, v = value_object ptr /\ cont ptr = result_some o.
Proof.
    introv E. destruct* v; false.
Qed.

Lemma assert_get_string : forall v o cont,
    assert_get_string v cont = result_some o ->
    exists s, v = value_string s /\ cont s = result_some o.
Proof.
    introv E. destruct* v; false.
Qed.

Lemma assert_get_bool : forall v o cont,
    assert_get_bool v cont = result_some o ->
    exists b, v = bool_to_value b /\ cont b = result_some o.
Proof.
    introv E. destruct* v; tryfalse; [exists true | exists false]; jauto. 
Qed.

Lemma assert_get_object_from_ptr_out : forall st ptr o cont,
    assert_get_object_from_ptr st ptr cont = result_some o ->
    exists obj, get_object st ptr = Some obj /\ cont obj = result_some o.
Proof.
    introv E. unfold assert_get_object_from_ptr in E.
    destruct* (get_object st ptr); tryfalse.
Qed.

Lemma assert_get_loc_out : forall c s o cont, 
    assert_get_loc c s cont = result_some o ->
    exists loc, get_loc c s = Some loc /\ cont loc = result_some o.
Proof.
    introv E. unfold assert_get_loc in E.
    destruct* (get_loc c s); tryfalse.
Qed.

Lemma assert_get_object_out : forall st v o cont,
    assert_get_object st v cont = result_some o -> 
    exists ptr obj, v = value_object ptr /\ get_object st ptr = Some obj /\ cont obj = result_some o.
Proof. 
    introv E. 
    unfold assert_get_object in E.
    lets (ptr&Hptr&Cptr): assert_get_object_ptr_out E.
    lets (obj&Hobj&Cobj): assert_get_object_from_ptr_out Cptr.
    jauto.
Qed.

Lemma assert_some_out : forall A opt cont (o : option A),
    assert_some opt cont = result_some o ->
    exists (a : A), opt = Some a /\ cont a = result_some o.
Proof. 
    introv E.
    destruct* opt; tryfalse.
Qed.

Lemma assert_deref_out : forall st loc cont o,
    assert_deref st loc cont = result_some o ->
    exists v, get_value st loc = Some v /\ cont v = result_some o.
Proof.
    introv E. unfold assert_deref in E.
    destruct* (get_value st loc); tryfalse.
Qed.

Lemma if_eval_ter_out : forall runs c st e cont o,
    if_eval_ter runs c st e cont = result_some o ->
    is_some (runs_type_eval runs c st e) (if_out_ter_post cont o).
Proof. 
    auto using if_out_ter_out.
Qed.

Lemma if_eval_return_out : forall runs c st e cont o,
    if_eval_return runs c st e cont = result_some o ->
    is_some (runs_type_eval runs c st e) (if_value_post cont o).
Proof. 
    auto using if_value_out.
Qed.

(* Tactics *)

(* TODO *)
Ltac ljs_run_select_ifres H :=
    match type of H with ?T = result_some _ => match T with
    | assert_get_loc _ _ _ => constr:(assert_get_loc_out)
    | assert_get_object_ptr _ _ => constr:(assert_get_object_ptr_out)
    | assert_get_bool _ _ => constr:(assert_get_bool)
    | assert_get_string _ _ => constr:(assert_get_string)
    | assert_deref _ _ _ => constr:(assert_deref_out)
    | if_out_ter _ _ => constr:(if_out_ter_out)
    | if_value _ _ => constr:(if_value_out)
    | if_eval_ter _ _ _ _ _ => constr:(if_eval_ter_out)
    | if_eval_return _ _ _ _ _ => constr:(if_eval_return_out)
    | _ => fail
    end end
.

Ltac ljs_run_push H a H1 H2 :=
    let L := ljs_run_select_ifres H in
    lets (a&H1&H2): L H; clear H
.

Tactic Notation "ljs_run_push" hyp(H) "as" ident(a) ident(H1) ident(H2) :=
    ljs_run_push H a H1 H2. 

Ltac ljs_run_push_auto :=
    repeat
    match goal with
    | H : _ = result_some _ |- _ => 
        let a := fresh "a" in
        let H1 := fresh "H" in
        let R := fresh "R" in
        try ljs_run_push H as a H1 R 
    end
.

Ltac ljs_run_post H st v Ho :=
    match type of H with 
    | if_value_post _ _ _ => destruct H as [(st&v&Ho&H)|H]
    | if_out_ter_post _ _ _ => destruct H as [(st&r&Ho&H)|H]
    end
.

Tactic Notation "ljs_run_post" hyp(H) "as" ident(st) ident(v) ident(Ho) :=
    ljs_run_post H st v Ho.

Ltac ljs_run_post_auto :=
    repeat
    match goal with
    | H : _ |- _ => 
        let st := fresh "st" in
        let v := fresh "v" in
        let Ho := fresh "Ho" in
        ljs_run_post H as st v Ho
    end
.

Ltac ljs_run_push_post_auto := repeat (ljs_run_push_auto; ljs_run_post_auto). 

Ltac ljs_run_inv :=
    repeat
    match goal with
    | H : result_value _ _ = _ |- _ => inverts H
    | H : result_break _ _ _ = _ |- _ => inverts H
    | H : result_exception _ _ = _ |- _ => inverts H
    | H : out_ter _ _ = out_ter _ _|- _  => inverts H
    | H : eqabort _ _ |- _ => let H' := fresh "H" in destruct H as (H&H'); inverts H'
    end
. 

Ltac ljs_eval_ih := eapply runs_type_correct_eval; eassumption.

(* Main lemma *)

Lemma eval_id_correct : forall runs c st s o,
    runs_type_correct runs -> 
    eval_id runs c st s = result_some o -> 
    exists loc v, get_loc c s = Some loc /\ 
        get_value st loc = Some v /\ o = out_ter st (res_value v).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_auto.
    ljs_run_inv. eauto.
Qed.

Lemma eval_if_correct : forall runs c st e e1 e2 o,
    runs_type_correct runs ->
    eval_if runs c st e e1 e2 = result_some o ->
    is_some (runs_type_eval runs c st e) (fun o' =>
        (exists st', o' = out_ter st' (res_value value_true) /\ 
            runs_type_eval runs c st' e1 = result_some o) \/
        (exists st', o' = out_ter st' (res_value value_false) /\
            runs_type_eval runs c st' e2 = result_some o) \/
        eqabort o o').
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push R as o' Ho' Co'.
    destruct Co' as [(st'&()&Ho&Hr)|H]; jauto; tryfalse.
Qed.

Lemma eval_seq_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_seq runs c st e1 e2 = result_some o -> 
    is_some (runs_type_eval runs c st e1) (fun o' =>
        (exists st' v, o' = out_ter st' (res_value v) /\
            runs_type_eval runs c st' e2 = result_some o) \/
        eqabort o o').
Proof. 
    introv IH R. unfolds. unfolds in R. 
    ljs_run_push_auto; jauto.
Qed.

Lemma eval_setbang_correct : forall runs c st s e o,
    runs_type_correct runs ->
    eval_setbang runs c st s e = result_some o ->
    is_some (runs_type_eval runs c st e) (fun o' =>
        (exists st' loc v, o' = out_ter st' (res_value v) /\
            get_loc c s = Some loc /\ 
            o = out_ter (add_value_at_location st' loc v) (res_value v)) \/
        eqabort o o').
Proof.
    introv IH R. unfolds. unfolds in R. 
    ljs_run_push_post_auto; ljs_run_inv; jauto.
    eexists. intuition jauto. 
Qed.

Lemma eval_let_correct : forall runs c st s e1 e2 o,
    runs_type_correct runs ->
    eval_let runs c st s e1 e2 = result_some o ->
    is_some (runs_type_eval runs c st e1) (fun o' =>
        (exists st' st'' c' v, o' = out_ter st' (res_value v) /\
            (c', st'') = add_named_value c st' s v /\ 
            runs_type_eval runs c' st'' e2 = result_some o) \/
        eqabort o o').
Proof. 
    introv IH R. unfolds. unfolds in R.
    unfold eval_cont_terminate, eval_cont in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
    (* TODO: make a tactic for doing this! *)
    assert (Z : exists t, t = add_named_value c st0 s v).
    eauto.
    destruct Z as ((c0,st1)&Z).
    rewrite <- Z in R0.
    eexists. intuition jauto.
Qed. 

Lemma eval_break_correct : forall runs c st s e o,
    runs_type_correct runs ->
    eval_break runs c st s e = result_some o ->
    is_some (runs_type_eval runs c st e) (fun o' =>
        (exists st' v, o' = out_ter st' (res_value v) /\
            o = out_ter st' (res_break s v)) \/
        eqabort o o').
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_throw_correct : forall runs c st e o,
    runs_type_correct runs ->
    eval_throw runs c st e = result_some o ->
    is_some (runs_type_eval runs c st e) (fun o' =>
        (exists st' v, o' = out_ter st' (res_value v) /\
            o = out_ter st' (res_exception v)) \/
        eqabort o o').
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_label_correct : forall runs c st s e o,
    runs_type_correct runs ->
    eval_label runs c st s e = result_some o ->
    is_some (runs_type_eval runs c st e) (fun o' =>
        (exists st' v, o' = out_ter st' (res_break s v) /\ 
            o = out_ter st' (res_value v)) \/
        (o = o' /\ forall st' v, o' <> out_ter st' (res_break s v))).
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push_post_auto; eexists; intuition (jauto || tryfalse).
    destruct r; ljs_run_inv; intuition (jauto || tryfalse).
Admitted. (* TODO *)

Lemma eval_correct : forall runs c st e o,
    runs_type_correct runs -> eval runs c st e = result_some o -> red_expr c st e o.
Proof.
    introv IH R. unfolds in R.
    destruct e.
    (* null *)
    ljs_run_inv. apply red_expr_null.
    (* undefined *)
    ljs_run_inv. apply red_expr_undefined.
    (* string *)
    ljs_run_inv. apply red_expr_string.
    (* number *)
    ljs_run_inv. apply red_expr_number.
    (* true *)
    ljs_run_inv. apply red_expr_true.
    (* false *)
    ljs_run_inv. apply red_expr_false.
    (* id *)
    lets (loc&v&Hloc&Hv&Ho): eval_id_correct IH R.
    inverts Ho.
    eapply red_expr_id; eassumption.
    (* object *)
    skip.
    (* get_attr *)
    skip.
    (* set_attr *)
    skip.
    (* get_obj_attr *)
    skip.
    (* set_obj_attr *)
    skip.
    (* get_field *)
    skip.
    (* set_field *)
    skip.
    (* delete_field *)
    skip.
    (* own_field_names *)
    skip.
    (* set_bang *)
    lets (o'&Ho&H): eval_setbang_correct IH R.
    eapply red_expr_set_bang. ljs_eval_ih.
    destruct H as [(st'&loc&v&Ho1&Hl&Ho2)|H].
    inverts Ho1. inverts Ho2.
    ljs_run_inv.
    eapply red_expr_set_bang_1. reflexivity. assumption.
    ljs_run_inv.
    eapply red_expr_set_bang_1_abort; assumption.
    (* op1 *)
    skip.
    (* op2 *)
    skip.
    (* if *)
    lets (o'&Ho&H): eval_if_correct IH R.
    eapply red_expr_if. 
    ljs_eval_ih.
    destruct H as [(st'&Hst'&Est')|[(st'&Hst'&Est')|H]].
    inverts Hst'. eapply red_expr_if_1_true; ljs_eval_ih.
    inverts Hst'. eapply red_expr_if_1_false; ljs_eval_ih.
    ljs_run_inv. eapply red_expr_if_1_abort; assumption.
    (* app *)
    skip.
    (* seq *)
    lets (o'&Ho&H): eval_seq_correct IH R.
    eapply red_expr_seq.
    ljs_eval_ih.
    destruct H as [(st'&v&Ho1&H)|H].
    inverts Ho1.
    eapply red_expr_seq_1.
    ljs_eval_ih.
    ljs_run_inv.
    eapply red_expr_seq_1_abort; assumption.
    (* let *)
    lets (o'&Ho&H): eval_let_correct IH R.
    eapply red_expr_let.
    ljs_eval_ih.
    destruct H as [(st'&st''&c'&v&Ho1&H&Ho2)|H].
    inverts Ho1.
    eapply red_expr_let_1. eassumption. ljs_eval_ih.
    ljs_run_inv.
    eapply red_expr_let_1_abort; assumption.
    (* recc *)
    skip.
    (* label *)
    lets (o'&Ho&H): eval_label_correct IH R.
    eapply red_expr_label.
    ljs_eval_ih.
    destruct H as [(st'&v&Ho1&Ho2)|(He&H)].
    inverts Ho1.
    inverts Ho2.
    eapply red_expr_label_1_break.
    inverts He.
    eapply red_expr_label_1; assumption.
    (* break *)
    lets (o'&Ho&H): eval_break_correct IH R.
    eapply red_expr_break.
    ljs_eval_ih.
    destruct H as [(st'&v&Ho1&Ho2)|H].
    inverts Ho1.
    inverts Ho2.
    eapply red_expr_break_1.
    ljs_run_inv.
    eapply red_expr_break_1_abort; assumption.
    (* try_catch *)
    skip.
    (* try_finally *)
    skip.
    (* throw *)
    lets (o'&Ho&H): eval_throw_correct IH R.
    eapply red_expr_throw.
    ljs_eval_ih.
    destruct H as [(st'&v&Ho1&Ho2)|H].
    inverts Ho1.
    inverts Ho2.
    eapply red_expr_throw_1.
    ljs_run_inv.
    eapply red_expr_throw_1_abort; assumption.
    (* lambda *)
    skip.
    (* eval *)
    skip.
Admitted.

Lemma runs_0_correct : runs_type_correct runs_0.
Proof.
    apply make_runs_type_correct.
    introv H.
    tryfalse.
Qed.

Lemma runs_S_correct : forall runs, runs_type_correct runs -> runs_type_correct (runs_S runs).
Proof.
    introv IH.
    apply make_runs_type_correct.
    eauto using eval_correct.
Qed.

Lemma runs_correct : forall k, runs_type_correct (runs k). 
Proof.
    induction k; eauto using runs_0_correct, runs_S_correct. 
Qed.
