Set Implicit Arguments.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
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

Record runs_type_correct runs :=
    make_runs_type_correct {
        runs_type_correct_eval : forall c st e o,
            runs_type_eval runs c st e = result_some o -> red_expr c st e o
}.

(* Useful lemmas *)

Lemma out_is_value_or_abort : forall o, (exists st v, o = out_ter st (res_value v)) \/ abort o.
Proof. 
    intro o.
    destruct o. eauto. destruct r; eauto.
Qed.

Lemma bool_to_value_to_bool : forall b, value_to_bool (bool_to_value b) = Some b.
Proof.
    intro b. destruct b; eauto.
Qed.

Hint Resolve bool_to_value_to_bool.
Hint Rewrite bool_to_value_to_bool.

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

Lemma assert_get_string_out : forall v o cont,
    assert_get_string v cont = result_some o ->
    exists s, v = value_string s /\ cont s = result_some o.
Proof.
    introv E. destruct* v; false.
Qed.

Lemma assert_get_bool_out : forall v o cont,
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

Ltac ljs_run_select_ifres H :=
    match type of H with ?T = result_some _ => match T with
    | assert_get_loc _ _ _ => constr:(assert_get_loc_out)
    | assert_get_object_ptr _ _ => constr:(assert_get_object_ptr_out)
    | assert_get_object_from_ptr _ _ _ => constr:(assert_get_object_from_ptr_out)
    | assert_get_bool _ _ => constr:(assert_get_bool_out)
    | assert_get_string _ _ => constr:(assert_get_string_out)
    | assert_deref _ _ _ => constr:(assert_deref_out)
    | if_out_ter _ _ => constr:(if_out_ter_out)
    | if_value _ _ => constr:(if_value_out)
    | if_eval_ter _ _ _ _ _ => constr:(if_eval_ter_out)
    | if_eval_return _ _ _ _ _ => constr:(if_eval_return_out)
    | if_result_some _ _ => constr:(if_result_some_out)
    | _ => fail
    end end
.

Ltac ljs_run_push H a H1 H2 :=
    let L := ljs_run_select_ifres H in
    lets (a&H1&H2): L H;  
    clear H
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
        unfold assert_get_object in H;
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
    | H : result_res _ _ = _ |- _ => inverts H
    | H : result_value _ _ = _ |- _ => inverts H
    | H : result_break _ _ _ = _ |- _ => inverts H
    | H : result_exception _ _ = _ |- _ => inverts H
    | H : out_ter _ _ = out_ter _ _|- _  => inverts H
    | H : Some _ = Some _ |- _ => inverts H
    | H : eqabort _ _ |- _ => let H' := fresh "H" in destruct H as (H&H'); inverts H'
    end
. 

Ltac ljs_eval_ih := eapply runs_type_correct_eval; eassumption.

Ltac destruct_exists H :=
    match type of H with
    | exists v, _ => destruct H as (v&H)
    end
.

Ltac destruct_or H :=
    match type of H with
    | _ \/ _ => destruct H as [H | H]
    end
.

Tactic Notation "cases_match_attributes" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [match ?B with attributes_data_of _ => _ | attributes_accessor_of _ => _ end] => case_if_on B as Eq
  | K: context [match ?B with attributes_data_of _ => _ | attributes_accessor_of _ => _ end] |- _ => case_if_on B as Eq
  end.

Tactic Notation "cases_match_attributes" :=
  let Eq := fresh in cases_match_attributes as Eq.

(* Main lemma *)

Definition is_some_value o res (Pred : store -> value -> Prop) := 
    is_some res (fun o' => (exists st v, o' = out_ter st (res_value v) /\ Pred st v) \/ eqabort o o'). 

Hint Unfold is_some_value.

Lemma is_some_value_munch : forall o' o res Pred,
    res = result_some o' -> 
    (exists st v, o' = out_ter st (res_value v) /\ Pred st v) \/ eqabort o o' ->
    is_some_value o res Pred.
Proof. eauto. Qed.

Hint Resolve is_some_value_munch.

Ltac ljs_is_some_value_munch := eapply is_some_value_munch; [eassumption | (right; eassumption) || (left; eexists; eexists; split; [eassumption | ])].

(* Prerequisites for proving correctness for application *)

Fixpoint is_some_values_eval runs c st o (es : list expr) (lv : list value) (Pred : store -> list value -> Prop) : Prop := 
    match es with
    | nil => Pred st (rev lv)
    | e :: es' => is_some_value o (runs_type_eval runs c st e) (fun st' v => 
        is_some_values_eval runs c st' o es' (v :: lv) Pred)
    end.

Lemma is_some_values_eval_lemma : forall runs c o es cont (Pred : _ -> _ -> Prop),
    runs_type_correct runs -> 
    (forall vs st, cont st vs = result_some o -> Pred st vs) ->
    forall vs st,
    fold_right (eval_arg_list_aux runs c)
        (fun st args => cont st (rev args)) es st vs = result_some o -> 
    is_some_values_eval runs c st o es vs Pred.
Proof. 
    introv IH CH.
    induction es.
    simpl; intros; eauto.
    simpl.
    introv H.
    unfold eval_arg_list_aux in H at 1.
    ljs_run_push_post_auto;
    ljs_is_some_value_munch.
    eapply IHes; assumption.
Qed.

Definition apply_post runs c st v vs o := exists k c'' is vls c' st' e, 
    get_closure st v = result_some (value_closure k c'' is e) /\ 
    (st', vls) = add_values st vs /\
    add_parameters c'' is vls = result_some c' /\
    runs_type_eval runs c' st' e = result_some o.

Lemma apply_correct : forall runs c st v vs o,
    runs_type_correct runs ->
    apply runs c st v vs = result_some o ->
    apply_post runs c st v vs o.
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto.
    destruct a; tryfalse.
    cases_let.
    ljs_run_push_auto.
    unfolds apply_post. jauto. 
Qed.

(* Lemmas for proving the main lemma *)

Lemma eval_app_correct : forall runs c st e es o,
    runs_type_correct runs ->
    eval_app runs c st e es = result_some o ->
    is_some_value o (runs_type_eval runs c st e) (fun st' v => 
        is_some_values_eval runs c st' o es nil (fun st'' vs => 
            apply_post runs c st'' v vs o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch.
    apply is_some_values_eval_lemma with (cont := fun st args => apply runs c st v args); try assumption.
    eauto using apply_correct.
Qed.

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
    is_some_value o (runs_type_eval runs c st e) (fun st' v =>
        (v = value_true /\ 
            runs_type_eval runs c st' e1 = result_some o) \/
        (v = value_false /\
            runs_type_eval runs c st' e2 = result_some o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch. cases_if; eauto.
Qed.

Lemma eval_seq_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_seq runs c st e1 e2 = result_some o -> 
    is_some_value o (runs_type_eval runs c st e1) (fun st' v =>
        runs_type_eval runs c st' e2 = result_some o).
Proof. 
    introv IH R. unfolds in R.  
    ljs_run_push_auto; jauto.
Qed.

Lemma eval_setbang_correct : forall runs c st s e o,
    runs_type_correct runs ->
    eval_setbang runs c st s e = result_some o ->
    is_some_value o (runs_type_eval runs c st e) (fun st' v =>
        exists loc, get_loc c s = Some loc /\ 
            o = out_ter (add_value_at_location st' loc v) (res_value v)).
Proof.
    introv IH R. unfolds in R. 
    ljs_run_push_post_auto; ljs_is_some_value_munch; ljs_run_inv; jauto.
Qed.

Lemma eval_let_correct : forall runs c st s e1 e2 o,
    runs_type_correct runs ->
    eval_let runs c st s e1 e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v =>
        exists st'' c', (c', st'') = add_named_value c st' s v /\ 
            runs_type_eval runs c' st'' e2 = result_some o).
Proof. 
    introv IH R. unfolds in R.
    unfold eval_cont in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch; ljs_run_inv; jauto.
    cases_let; jauto.
Qed. 

Lemma eval_rec_correct : forall runs c st s e1 e2 o,
    runs_type_correct runs ->
    eval_rec runs c st s e1 e2 = result_some o ->
    exists c' st' loc, (c', st', loc) = add_named_value_loc c st s value_undefined /\
        is_some_value o (runs_type_eval runs c' st' e1) (fun st' v =>
            runs_type_eval runs c' (add_value_at_location st' loc v) e2 = result_some o).
Proof.
    introv IH R. unfolds in R.
    unfold eval_cont in R.
    repeat cases_let. substs. do 3 eexists. split. reflexivity.
    ljs_run_push_post_auto; ljs_is_some_value_munch. assumption.
Qed.

Definition is_some_eval_objattrs o runs c st attrs Pred : Prop :=
    let 'objattrs_intro e1 e2 e3 e4 e5 := attrs in
    is_some_value o (runs_type_eval runs c st e1) (fun st1 v1 =>
    is_some_value o (runs_type_eval runs c st1 e2) (fun st2 v2 =>
    is_some_value o (runs_type_eval runs c st2 e3) (fun st3 v3 =>
    is_some_value o (runs_type_eval runs c st3 e4) (fun st4 v4 =>
    is_some_value o (runs_type_eval runs c st4 e5) (fun st5 v5 =>
        exists b s, v1 = value_string s /\ value_to_bool v2 = Some b /\
            Pred st5 s b v3 v4 v5))))). 

Definition is_some_eval_objprop o runs c st s prop Pred : Prop :=
    match prop with
    | property_data (data_intro e3 e4 e2 e1) =>
        is_some_value o (runs_type_eval runs c st e1) (fun st1 v1 =>
        is_some_value o (runs_type_eval runs c st1 e2) (fun st2 v2 =>
        is_some_value o (runs_type_eval runs c st2 e3) (fun st3 v3 =>
        is_some_value o (runs_type_eval runs c st3 e4) (fun st4 v4 =>
            exists b1 b2 b4, 
                value_to_bool v1 = Some b1 /\
                value_to_bool v2 = Some b2 /\
                value_to_bool v4 = Some b4 /\
                Pred st4 (attributes_data_of (attributes_data_intro v3 b4 b2 b1))))))
    | property_accessor (accessor_intro e3 e4 e2 e1) =>
        is_some_value o (runs_type_eval runs c st e1) (fun st1 v1 =>
        is_some_value o (runs_type_eval runs c st1 e2) (fun st2 v2 =>
        is_some_value o (runs_type_eval runs c st2 e3) (fun st3 v3 =>
        is_some_value o (runs_type_eval runs c st3 e4) (fun st4 v4 =>
             exists b1 b2, 
                value_to_bool v1 = Some b1 /\
                value_to_bool v2 = Some b2 /\
                Pred st4 (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1))))))
    end.

Fixpoint is_some_eval_objprops o runs c st props obj Pred : Prop :=
    match props with
    | nil => Pred st obj
    | (s, prop) :: props' => 
        is_some_eval_objprop o runs c st s prop (fun st' attr =>
            is_some_eval_objprops o runs c st' props' (set_object_property obj s attr) Pred)
    end.

Lemma is_some_eval_objprops_lemma : forall runs c o props cont (Pred : _ -> _ -> Prop),
    runs_type_correct runs ->
    (forall st obj, cont st obj = result_some o -> Pred st obj) ->
    forall st obj,
        eval_object_properties runs c st props obj cont = result_some o ->
        is_some_eval_objprops o runs c st props obj Pred.
Proof.
    introv IH CH.
    induction props.
    eauto.
    introv H.
    destruct a as (s&[(data)|(acc)]);
    simpls;
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch; substs; repeat eexists; eauto.
Qed.

Lemma eval_object_correct : forall runs c st attrs l o,
    runs_type_correct runs ->
    eval_object_decl runs c st attrs l = result_some o ->
    is_some_eval_objattrs o runs c st attrs (fun st' class ext proto code prim => 
        let obj := object_intro (oattrs_intro proto class ext prim code) Heap.empty in
        is_some_eval_objprops o runs c st' l obj (fun st'' obj =>
            exists st''' v,
                (st''', v) = add_object st'' obj /\
                o = out_ter st''' (res_value v))).
Proof.
    introv IH R. unfolds in R.
    cases_let.
    unfolds.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    do 2 eexists; splits.
    eassumption. substs; eauto.
    eapply is_some_eval_objprops_lemma; try eassumption.
    intros. simpl in H7. cases_let. ljs_run_inv. eauto.
Qed.

Lemma eval_break_correct : forall runs c st s e o,
    runs_type_correct runs ->
    eval_break runs c st s e = result_some o ->
    is_some_value o (runs_type_eval runs c st e) (fun st' v =>
        o = out_ter st' (res_break s v)).
Proof.
    introv IH R. unfolds. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_throw_correct : forall runs c st e o,
    runs_type_correct runs ->
    eval_throw runs c st e = result_some o ->
    is_some_value o (runs_type_eval runs c st e) (fun st' v =>
        o = out_ter st' (res_exception v)).
Proof.
    introv IH R. unfolds. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_tryfinally_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_tryfinally runs c st e1 e2 = result_some o ->
    is_some (runs_type_eval runs c st e1) (fun o' =>
        (exists st' r, o' = out_ter st' r /\
            is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 => 
                o = out_ter st'' r)) \/
        (o = o' /\ o' = out_div)). 
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push_post_auto; eexists; (split; [eassumption | ]); jauto;
    left; do 2 eexists; (split; [eassumption | ]);
    ljs_is_some_value_munch; ljs_run_inv; jauto.
Qed.

Lemma eval_trycatch_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_trycatch runs c st e1 e2 = result_some o ->
    is_some (runs_type_eval runs c st e1) (fun o' =>
        (exists st' v, o' = out_ter st' (res_exception v) /\
            is_some_value o (runs_type_eval runs c st' e2) (fun st'' vv => 
                apply_post runs c st'' vv [v] o)) \/
        (o = o' /\ forall st' v, o' <> out_ter st' (res_exception v))).
Proof. 
    introv IH R. unfolds. unfolds in R.
    ljs_run_push R as o' Ho' R'.
    ljs_run_post R' as st' q Ho; eexists; intuition (jauto || tryfalse).
    inverts Ho. 
    destruct r; inverts R'; ljs_run_inv; intuition (jauto || tryfalse).
    left. eexists; eexists; split. reflexivity.
    ljs_run_push_post_auto;
    ljs_is_some_value_munch.
    eauto using apply_correct.
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
    case_if. destruct e0.  ljs_run_inv. jauto.
    ljs_run_inv. intuition (eauto || tryfalse).
Qed.

Lemma eval_lambda_correct : forall runs c st vs e o,
    runs_type_correct runs ->
    eval_lambda runs c st vs e = result_some o ->
    exists st' v, (st', v) = add_closure c st vs e /\ o = out_ter st' (res_value v).
Proof.
    introv IH R. unfolds in R.
    cases_let.
    ljs_run_inv. eauto.
Qed.

Lemma eval_eval_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_eval runs c st e1 e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v' =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v'' =>
            exists s ptr obj c1 st1 e, 
                v' = value_string s /\
                v'' = value_object ptr /\ 
                get_object st'' ptr = Some obj /\ 
                envstore_of_obj st'' obj = Some (c1, st1) /\
                desugar_expr s = Some e /\ 
                runs_type_eval runs c1 st1 e = result_some o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_match_option.
    cases_match_option.
    cases_let as Eq.
    inverts Eq.
    jauto.
Qed.

Lemma eval_op1_correct : forall runs c st op e1 o,
    runs_type_correct runs ->
    eval_op1 runs c st op e1 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        exists v, unary_operator op st' v1 = result_some v /\ o = out_ter st' (res_value v)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. eauto.
Qed.

Lemma eval_op2_correct : forall runs c st op e1 e2 o,
    runs_type_correct runs ->
    eval_op2 runs c st op e1 e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            exists v, binary_operator op st'' v1 v2 = result_some v /\ o = out_ter st'' (res_value v))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. eauto.
Qed.

Lemma eval_get_obj_attr_correct : forall runs c st oa e1 o,
    runs_type_correct runs ->
    eval_get_obj_attr runs c st e1 oa = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        exists ptr obj, v1 = value_object ptr /\ 
            get_object st' ptr = Some obj /\ 
            o = out_ter st' (res_value (get_object_oattr obj oa))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. eauto.
Qed.

Lemma eval_set_obj_attr_correct : forall runs c st oa e1 e2 o,
    runs_type_correct runs ->
    eval_set_obj_attr runs c st e1 oa e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            exists ptr obj obj', v1 = value_object ptr /\
                get_object st'' ptr = Some obj /\
                set_object_oattr obj oa v2 = result_some obj' /\
                o = out_ter (update_object st'' ptr obj') (res_value v2))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    unfolds change_object_cont.
    cases_match_option; tryfalse.
    ljs_run_push_post_auto.
    inverts R.
    jauto.
Qed.

Lemma eval_get_attr_correct : forall runs c st pa e1 e2 o,
    runs_type_correct runs ->
    eval_get_attr runs c st e1 e2 pa = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            exists ptr obj s v, v1 = value_object ptr /\
                v2 = value_string s /\
                get_object st'' ptr = Some obj /\
                get_object_pattr obj s pa = result_some v /\
                o = out_ter st'' (res_value v))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. jauto. 
Qed.

Lemma eval_set_attr_correct : forall runs c st pa e1 e2 e3 o,
    runs_type_correct runs ->
    eval_set_attr runs c st e1 e2 pa e3 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            is_some_value o (runs_type_eval runs c st'' e3) (fun st''' v3 =>
                exists ptr obj obj' s, v1 = value_object ptr /\
                    v2 = value_string s /\
                    get_object st''' ptr = Some obj /\
                    set_object_pattr obj s pa v3 = result_some obj' /\
                    o = out_ter (update_object st''' ptr obj') (res_value v3)))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    unfolds change_object_cont.
    cases_match_option; tryfalse.
    ljs_run_push_post_auto.
    inverts R.
    jauto.
Qed.

Lemma eval_get_field_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_get_field runs c st e1 e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            exists ptr s oattrs, v1 = value_object ptr /\
                v2 = value_string s /\
                get_property st'' ptr s = result_some oattrs /\
                ((oattrs = None /\ o = out_ter st'' (res_value value_undefined)) \/
                 (exists data, oattrs = Some (attributes_data_of data) /\
                    o = out_ter st'' (res_value (attributes_data_value data))) \/
                 (exists acc st''' v3, oattrs = Some (attributes_accessor_of acc) /\
                    (st''', v3) = add_object st'' (default_object) /\
                    apply_post runs c st''' (attributes_accessor_get acc) [value_object ptr; v3] o)))).
Proof.
    introv IH RR. unfolds in RR.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    repeat eexists; try eassumption.
    cases_match_option;
    [cases_match_attributes | ];
    ljs_run_inv; jauto.
    cases_let.
    lets HR: apply_correct IH R.
    match goal with H : _ = value_object _ |- _ => inverts H end.
    intuition jauto.
Qed.

Lemma eval_set_field_correct : forall runs c st e1 e2 e3 o,
    runs_type_correct runs ->
    eval_set_field runs c st e1 e2 e3 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            is_some_value o (runs_type_eval runs c st'' e3) (fun st''' v3 =>
                exists ptr obj s oattrs, v1 = value_object ptr /\
                    get_object st''' ptr = Some obj /\
                    v2 = value_string s /\
                    get_property st''' ptr s = result_some oattrs /\
                    ((oattrs = None /\ object_extensible obj = true /\
                        o = out_ter (update_object st''' ptr (set_object_property obj s 
                            (attributes_data_of (attributes_data_intro v3 true true true)))) (res_value v3)) \/
                     (oattrs = None /\ object_extensible obj = false /\
                        o = out_ter st''' (res_value value_undefined)) \/
                     (exists data, oattrs = Some (attributes_data_of data) /\
                        attributes_data_writable data = false /\
                        o = out_ter st''' (res_exception (value_string "unwritable-field"))) \/
                     (exists data, oattrs = Some (attributes_data_of data) /\
                        get_object_property obj s <> None /\
                        attributes_data_writable data = true /\
                        o = out_ter (update_object st''' ptr (set_object_property obj s
                            (attributes_data_of (attributes_data_value_update data v3)))) (res_value v3)) \/
                     (exists data, oattrs = Some (attributes_data_of data) /\
                        get_object_property obj s = None /\
                        object_extensible obj = true /\
                        attributes_data_writable data = true /\
                        o = out_ter (update_object st''' ptr (set_object_property obj s 
                            (attributes_data_of (attributes_data_intro v3 true true true)))) (res_value v3)) \/
                     (exists data, oattrs = Some (attributes_data_of data) /\
                        attributes_data_writable data = true /\
                        get_object_property obj s = None /\
                        object_extensible obj = false /\
                        o = out_ter st''' (res_value value_undefined)) \/
                     (exists acc st'''' v4, oattrs = Some (attributes_accessor_of acc) /\
                        (st'''', v4) = add_object st''' (object_with_properties 
                            (Heap.write Heap.empty "0" (attributes_data_of 
                                (attributes_data_intro v3 true false false))) default_object) /\
                        apply_post runs c st'''' (attributes_accessor_set acc) [value_object ptr; v4] o))))).
Proof.
    introv IH RR. unfolds in RR.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    repeat eexists; try eassumption. 
    repeat (cases_match_option || cases_match_attributes || cases_let || cases_if || unfolds change_object_property, change_object_property_cont, change_object_cont); inverts R; ljs_run_inv; substs.
    branch 4. eexists. intuition (eauto ; tryfalse).
    branch 3. jauto. 
    branch 7. eexists. forwards HR: apply_correct IH. eassumption. eauto.
    branch 5. jauto.
    branch 6. jauto.
    branch 3. jauto.
    branch 7. eexists. forwards HR: apply_correct IH. eassumption. eauto.
    branch 1. jauto.
    branch 2. jauto.
Qed.

Lemma eval_delete_field_correct : forall runs c st e1 e2 o,
    runs_type_correct runs ->
    eval_delete_field runs c st e1 e2 = result_some o ->
    is_some_value o (runs_type_eval runs c st e1) (fun st' v1 =>
        is_some_value o (runs_type_eval runs c st' e2) (fun st'' v2 =>
            exists ptr obj s oattrs, v1 = value_object ptr /\
                get_object st'' ptr = Some obj /\
                v2 = value_string s /\
                get_object_property obj s = oattrs /\
                ((oattrs = None /\ o = out_ter st'' (res_value value_false)) \/
                 (exists attrs, oattrs = Some attrs /\ 
                  attributes_configurable attrs = false /\
                  o = out_ter st'' (res_exception (value_string "unconfigurable-delete"))) \/
                 (exists attrs, oattrs = Some attrs /\
                  attributes_configurable attrs = true /\
                  o = out_ter (update_object st'' ptr (delete_object_property obj s)) (res_value value_true))))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    repeat eexists; try eassumption. 
    repeat (cases_match_option || cases_if); try inverts R; substs; ljs_run_inv; intuition eauto.
Qed. 

Lemma eval_own_field_names_correct : forall runs c st e o,
    runs_type_correct runs ->
    eval_own_field_names runs c st e = result_some o ->
    is_some_value o (runs_type_eval runs c st e) (fun st' v =>
        exists ptr obj st'' v', v = value_object ptr /\
            get_object st' ptr = Some obj /\
            (st'', v') = add_object st' (make_prop_list obj) /\
            o = out_ter st'' (res_value v')).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_let.
    ljs_run_inv. jauto.
Qed.

(* Help for proving the main lemma *)

Ltac ljs_is_some_value_push H o st v H1 H2 :=
    match type of H with
    | is_some_value _ _ _ => let H' := fresh in destruct H as (o&H1&[(st&v&H'&H)|H]); [inverts H' | inverts H]
    end.

Tactic Notation "ljs_is_some_value_push" hyp(H) "as" ident(o) ident(st) ident(v) ident(H1) ident(H2) :=
    ljs_is_some_value_push H o st v H1 H2. 

Ltac ljs_is_some_push :=
    match goal with
    | H : is_some_value _ _ _ |- _ => 
        let o := fresh "o" in
        let st := fresh "st" in
        let v := fresh "v" in
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        try ljs_is_some_value_push H as o st v H1 H2 
    end
.

Ltac ljs_pretty_advance rule rulea :=
    ljs_is_some_push;
    (eapply rule; [solve [ljs_eval_ih] | ]);
    [ | eapply rulea; assumption]. 

Lemma red_expr_app_2_lemma : forall runs c st v vl o,
    runs_type_correct runs ->
    apply_post runs c st v vl o ->
    red_expr c st (expr_app_2 v vl) o.
Proof.
    introv IH R.
    unfolds in R.
    repeat destruct_exists R.
    destruct R as (R1&R2&R3&R4).
    eapply red_expr_app_2; eauto.
    ljs_eval_ih.
Qed.

Lemma red_expr_eval_many_lemma : forall runs c o C (Pred : _ -> _ -> Prop),
    runs_type_correct runs -> 
    (forall st vs, Pred st (rev vs) -> red_expr c st (C (rev vs)) o) ->
    forall es st vs,
    is_some_values_eval runs c st o es vs Pred ->
    red_expr c st (expr_eval_many_1 es vs C) o.
Proof.
    introv IH PH.
    induction es; introv R.
    eapply red_expr_eval_many_1.
    eauto.
    unfold is_some_values_eval in R at 1.
    ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort.
    eapply red_expr_eval_many_2.
    eauto.
Qed.

(*
Lemma red_expr_app_2_lemma : forall runs c o v (Pred : _ -> _ -> Prop),
    runs_type_correct runs -> 
    (forall st vs, Pred st (rev vs) -> red_expr c st (expr_app_2 v vs nil) o) ->
    forall es st vs,
    is_some_values_eval runs c st o es vs Pred ->
    red_expr c st (expr_app_2 v vs es) o.
Proof.
    introv IH PH.
    induction es. eauto.
    introv R. 
    unfold is_some_values_eval in R at 1.
    ljs_pretty_advance red_expr_app_2_next red_expr_app_3_abort.
    eapply red_expr_app_3.
    eauto.
Qed.
*)

Lemma red_expr_object_2_lemma : forall runs c o (Pred : _ -> _ -> Prop),
    runs_type_correct runs ->
    (forall st obj, Pred st obj -> red_expr c st (expr_object_2 obj nil) o) ->
    forall props st obj,
    is_some_eval_objprops o runs c st props obj Pred ->
    red_expr c st (expr_object_2 obj props) o.
Proof.
    introv IH PH.
    induction props. eauto.
    introv R.
    unfold is_some_eval_objprops in R at 1.
    destruct a as (s&[data|acc]).
    destruct data.
    unfolds in R.
    eapply red_expr_object_2_data.
    repeat (ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort;
            eapply red_expr_eval_many_2).
    eapply red_expr_eval_many_1.
    destruct R as (b1&b2&b3&Hb1&Hb2&Hb3&R).
    eapply red_expr_object_data_1; eauto. 
    destruct acc.
    unfolds in R.
    eapply red_expr_object_2_accessor.
    repeat (ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort;
            eapply red_expr_eval_many_2).
    eapply red_expr_eval_many_1.
    destruct R as (b1&b2&Hb1&Hb2&R).
    eapply red_expr_object_accessor_1; eauto.
Qed.

(* Main lemma *)

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
    lets H: eval_object_correct IH R.
    match goal with H : objattrs |- _ => destruct H end.
    unfolds in H.
    eapply red_expr_object. 
    repeat (ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort;
            eapply red_expr_eval_many_2).
    eapply red_expr_eval_many_1.
    destruct H as (b&s&Hs&Hb&H).
    substs.
    eapply red_expr_object_1; try eassumption.
    applys red_expr_object_2_lemma IH; try eassumption.
    introv Ho.
    simpl in Ho.
    destruct Ho as (st'''&v&Ho).
    destructs Ho. substs.
    eapply red_expr_object_2; eassumption.
    (* get_attr *)
    lets H: eval_get_attr_correct IH R.
    ljs_pretty_advance red_expr_get_attr red_expr_get_attr_1_abort.
    ljs_pretty_advance red_expr_get_attr_1 red_expr_get_attr_2_abort.
    destruct H as (ptr&obj&s&v1&Hy1&Hy2&Hy3&Hy4&Hy5).
    inverts Hy1. inverts Hy2.
    inverts Hy5.
    eapply red_expr_get_attr_2; eauto.
    (* set_attr *)
    lets H: eval_set_attr_correct IH R.
    ljs_pretty_advance red_expr_set_attr red_expr_set_attr_1_abort.
    ljs_pretty_advance red_expr_set_attr_1 red_expr_set_attr_2_abort.
    ljs_pretty_advance red_expr_set_attr_2 red_expr_set_attr_3_abort.
    destruct H as (ptr&obj&obj'&s&Hy1&Hy2&Hy3&Hy4&Hy5).
    inverts Hy1. inverts Hy2.
    inverts Hy5.
    eapply red_expr_set_attr_3; eauto.
    (* get_obj_attr *)
    lets H: eval_get_obj_attr_correct IH R.
    ljs_pretty_advance red_expr_get_obj_attr red_expr_get_obj_attr_1_abort.
    destruct H as (ptr&obj&Hy1&Hy2&Hy3).
    inverts Hy1. inverts Hy3.
    eapply red_expr_get_obj_attr_1; eauto.
    (* set_obj_attr *)
    lets H: eval_set_obj_attr_correct IH R.
    ljs_pretty_advance red_expr_set_obj_attr red_expr_set_obj_attr_1_abort.
    ljs_pretty_advance red_expr_set_obj_attr_1 red_expr_set_obj_attr_2_abort.
    destruct H as (ptr&obj&obj'&Hy1&Hy2&Hy3&Hy4).
    inverts Hy1. inverts Hy4.
    eapply red_expr_set_obj_attr_2; eauto.
    (* get_field *)
    lets H: eval_get_field_correct IH R.
    ljs_pretty_advance red_expr_get_field red_expr_get_field_1_abort.
    ljs_pretty_advance red_expr_get_field_1 red_expr_get_field_2_abort.
    destruct H as (ptr&s&oattrs&Ho&Hs&Hp&H).
    substs.
    eapply red_expr_get_field_2; try eassumption.
    branches H; repeat destruct_exists H; destructs H; substs.
    eapply red_expr_get_field_3_no_field.
    eapply red_expr_get_field_3_get_field.
    eapply red_expr_get_field_3_getter; try eassumption.
    eauto using red_expr_app_2_lemma. 
    (* set_field *)
    lets H: eval_set_field_correct IH R.
    ljs_pretty_advance red_expr_set_field red_expr_set_field_1_abort.
    ljs_pretty_advance red_expr_set_field_1 red_expr_set_field_2_abort.
    ljs_pretty_advance red_expr_set_field_2 red_expr_set_field_3_abort.
    destruct H as (ptr&obj&s&oattrs&Hv&Ho&Hs&Hp&H).
    substs.
    eapply red_expr_set_field_3; try eassumption.
    repeat destruct_or H; repeat destruct_exists H; destructs H; try subst o;
    match goal with H : oattrs = _ |- _ => inverts H end.
    eapply red_expr_set_field_4_add_field; eauto.
    eapply red_expr_set_field_4_unextensible_add; eauto. 
    eapply red_expr_set_field_4_unwritable; eauto. 
    eapply red_expr_set_field_4_set_field; eauto.
    eapply red_expr_set_field_4_shadow_field; eauto.
    eapply red_expr_set_field_4_unextensible_shadow; eauto. 
    eapply red_expr_set_field_4_setter; try eassumption.
    eauto using red_expr_app_2_lemma. 
    (* delete_field *)
    lets H: eval_delete_field_correct IH R.
    ljs_pretty_advance red_expr_delete_field red_expr_delete_field_1_abort.
    ljs_pretty_advance red_expr_delete_field_1 red_expr_delete_field_2_abort.
    destruct H as (ptr&obj&s&oattrs&Hv&Ho&Hs&Hp&H).
    inverts Hv. inverts Hs.
    eapply red_expr_delete_field_2; try eassumption.
    repeat destruct_or H; repeat destruct_exists H; destructs H; subst o;
    match goal with H : oattrs = _ |- _ => inverts H end.
    eapply red_expr_delete_field_3_not_found.
    eapply red_expr_delete_field_3_unconfigurable; eauto.
    eapply red_expr_delete_field_3_found; eauto.
    (* own_field_names *)
    lets H: eval_own_field_names_correct IH R.
    ljs_pretty_advance red_expr_own_field_names red_expr_own_field_names_1_abort.
    repeat destruct_exists H.
    destructs H.
    substs.
    eapply red_expr_own_field_names_1; eauto.
    (* set_bang *)
    lets H: eval_setbang_correct IH R.
    ljs_pretty_advance red_expr_set_bang red_expr_set_bang_1_abort.
    destruct H as (loc&Hl&Ho2).
    inverts Ho2.
    eapply red_expr_set_bang_1. reflexivity. assumption.
    (* op1 *)
    lets H: eval_op1_correct IH R.
    ljs_pretty_advance red_expr_op1 red_expr_op1_1_abort.
    destruct H as (v0&H&Ho).
    inverts Ho.
    eapply red_expr_op1_1; assumption.
    (* op2 *)
    lets H: eval_op2_correct IH R.
    ljs_pretty_advance red_expr_op2 red_expr_op2_1_abort.
    ljs_pretty_advance red_expr_op2_1 red_expr_op2_2_abort.
    destruct H as (v1&H&Ho).
    inverts Ho.
    eapply red_expr_op2_2; assumption.
    (* if *)
    lets H: eval_if_correct IH R.
    ljs_pretty_advance red_expr_if red_expr_if_1_abort.
    destruct H as [(Hv&H)|(Hv&H)]; inverts Hv.
    eapply red_expr_if_1_true; ljs_eval_ih.
    eapply red_expr_if_1_false; ljs_eval_ih.
    (* app *)
    lets H: eval_app_correct IH R.
    ljs_pretty_advance red_expr_app red_expr_app_1_abort.
    eapply red_expr_app_1.
    eapply red_expr_eval_many_lemma; try eassumption.
    introv Hy.
    simpl in Hy.
    repeat destruct_exists Hy.
    eauto using red_expr_app_2_lemma. 
    (* seq *)
    lets H: eval_seq_correct IH R.
    ljs_pretty_advance red_expr_seq red_expr_seq_1_abort.
    eapply red_expr_seq_1.
    ljs_eval_ih.
    (* let *)
    lets H: eval_let_correct IH R.
    ljs_pretty_advance red_expr_let red_expr_let_1_abort.
    destruct H as (st''&c'&H&Ho2).
    eapply red_expr_let_1. eassumption. ljs_eval_ih.
    (* recc *)
    lets H: eval_rec_correct IH R.
    repeat destruct_exists H.
    destruct H as (Hv&H).
    ljs_is_some_push;
    (eapply red_expr_rec; [eassumption | ljs_eval_ih | ]);
    [ | eapply red_expr_rec_1_abort; assumption].
    eapply red_expr_rec_1. reflexivity. ljs_eval_ih. 
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
    lets H: eval_break_correct IH R.
    ljs_pretty_advance red_expr_break red_expr_break_1_abort.
    inverts H.
    eapply red_expr_break_1.
    (* try_catch *)
    lets (o'&Ho&H): eval_trycatch_correct IH R. 
    eapply red_expr_try_catch.
    ljs_eval_ih.
    destruct H as [(st'&v&Ho1&Ho2)|(He&H)].
    inverts Ho1.
    ljs_pretty_advance red_expr_try_catch_1_exc red_expr_try_catch_2_abort.
    eapply red_expr_try_catch_2.
    eauto using red_expr_app_2_lemma. 
    inverts He.
    eapply red_expr_try_catch_1; eauto.
    (* try_finally *)
    lets (o'&Ho&H): eval_tryfinally_correct IH R. 
    eapply red_expr_try_finally. ljs_eval_ih.
    destruct H as [(st'&r&Ho'&H)|(Ho'&H)].
    subst o'.
    ljs_pretty_advance red_expr_try_finally_1 red_expr_try_finally_2_abort.
    subst o. eapply red_expr_try_finally_2.
    substs.
    eapply red_expr_try_finally_1_div.
    (* throw *)
    lets H: eval_throw_correct IH R.
    ljs_pretty_advance red_expr_throw red_expr_throw_1_abort.
    inverts H.
    eapply red_expr_throw_1.
    (* lambda *)
    lets (st'&v&Ho&H): eval_lambda_correct IH R.
    inverts H.
    eapply red_expr_lambda; assumption.
    (* eval *)
    lets H: eval_eval_correct IH R.
    ljs_pretty_advance red_expr_eval red_expr_eval_1_abort.
    ljs_pretty_advance red_expr_eval_1 red_expr_eval_2_abort.
    repeat destruct_exists H.
    destruct H as (st2&e&H).
    destructs H.
    ljs_run_inv.
    inverts H. inverts H4.
    eapply red_expr_eval_2; try eassumption.
    ljs_eval_ih.
    (* hint *)
    eapply red_expr_hint.
    ljs_eval_ih.
    (* dump *)
    tryfalse.
Qed.

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

Lemma runs_lazy_correct : forall runs, runs_type_correct runs -> runs_type_correct (suspend_runs (fun _ => runs)).
Proof.
    introv IH.
    eapply make_runs_type_correct.
    eauto using runs_type_correct_eval. 
Qed.

Lemma lazy_runs_correct : forall k, runs_type_correct (lazy_runs k). 
Proof.
    induction k; eauto using runs_0_correct, runs_S_correct, runs_lazy_correct. 
Qed.

Lemma runs_correct : forall k, runs_type_correct (runs k). 
Proof.
    induction k; eauto using runs_0_correct, runs_S_correct. 
Qed.

   