Set Implicit Arguments.
Require Import LjsShared.
Require Import Utils.
Require Import LjsSyntax.
Require Import LjsPrettyInterm.
Require Import LjsPrettyRules.
Require Import LjsPrettyRulesAux.
Require Import LjsStore.
Require Import LjsCommon.
Require Import LjsValues.
Require Import LjsOperators.
Require Import LjsMonads.
Require Import LjsInterpreter.
Require Import JsNumber.

Import ListNotations.

Open Scope list_scope.
Open Scope container_scope.

Implicit Type A B : Type.
Implicit Type eval : eval_fun.
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

Definition eval_fun_correct eval := forall c st e o,
  eval c st e = result_some o -> red_expr c st e o.

(* Useful lemmas *)

Lemma out_is_value_or_abort : forall o, (exists st v, o = out_ter st (res_value v)) \/ abort o.
Proof. 
    intro o.
    destruct o. eauto. destruct r; eauto.
Qed.

Lemma bool_to_value_to_bool : forall b, value_to_bool (value_bool b) = Some b.
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
    exists b, v = value_bool b /\ cont b = result_some o.
Proof.
    introv E. destruct* v; tryfalse.
Qed.

Lemma assert_get_object_from_ptr_out : forall A (a : A) st ptr cont,
    assert_get_object_from_ptr st ptr cont = result_some a ->
    exists obj, st \(ptr?) = Some obj /\ cont obj = result_some a.
Proof.
    introv E. unfold assert_get_object_from_ptr in E.
    cases_match_option; eauto.
Qed.

Lemma assert_get_object_out : forall st v o cont,
    assert_get_object st v cont = result_some o -> 
    exists ptr obj, v = value_object ptr /\ st \(ptr?) = Some obj /\ cont obj = result_some o.
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

Lemma assert_deref_out : forall c i cont o,
    assert_deref c i cont = result_some o ->
    exists v, c \(i?) = Some v /\ cont v = result_some o.
Proof.
    introv E. unfold assert_deref in E.
    cases_match_option. jauto.
Qed.

Lemma if_eval_ter_out : forall eval c st e cont o,
    if_eval_ter eval c st e cont = result_some o ->
    is_some (eval c st e) (if_out_ter_post cont o).
Proof. 
    auto using if_out_ter_out.
Qed.

Lemma if_eval_return_out : forall eval c st e cont o,
    if_eval_return eval c st e cont = result_some o ->
    is_some (eval c st e) (if_value_post cont o).
Proof. 
    auto using if_value_out.
Qed.

(* Utility lemmas *)

Lemma get_object_property_some_lemma : forall obj name attr,
    get_object_property obj name = Some attr ->
    binds (object_properties obj) name attr.
Proof.
    introv Hgop.
    unfolds get_object_property.
    eauto using read_option_binds.
Qed.

Lemma get_object_property_none_lemma : forall obj name,
    get_object_property obj name = None ->
    ~index (object_properties obj) name.
Proof.
    introv Hgop.
    unfolds get_object_property.
    eauto using read_option_not_index.
Qed.

Lemma object_property_is_from_get_property : forall st obj name oattr,
    get_property st obj name = result_some oattr -> 
    object_property_is st obj name oattr.
Proof.
    unfolds get_property.
    introv. gen obj.
    induction (card st); introv Hgp; destruct obj;
    simpls;
    (cases_match_option as Heq;
    [apply get_object_property_some_lemma in Heq; injects; apply object_property_is_own; assumption | apply get_object_property_none_lemma in Heq]);
    destruct object_attrs; destruct oattrs_proto; simpls; tryfalse.
    injects.
    apply object_property_is_none; auto.
    injects.
    apply object_property_is_none; auto.
    apply assert_get_object_from_ptr_out in Hgp.
    destruct_hyp Hgp.
    eapply object_property_is_proto; eauto using read_option_binds.
Qed.

Lemma closure_ctx_from_get_closure_ctx : forall clo sl c,
    get_closure_ctx clo sl = result_some c -> closure_ctx clo sl c.
Proof.
    introv Hgc;
    destruct clo as (cl&os);
    destruct os; simpls;
    unfolds add_parameters;
    cases_match_option;
    injects Hgc;
    eauto using closure_ctx_rec, closure_ctx_nonrec, zip_Zip.
Qed.

Hint Resolve 
    object_property_is_from_get_property
    closure_ctx_from_get_closure_ctx.

(* Tactics *)

Ltac ljs_run_select_ifres H :=
    match type of H with ?T = result_some _ => match T with
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
        ljs_run_push H as a H1 R
    | |- _ => idtac
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

Ltac ljs_eval_ih := eassumption.

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

Fixpoint is_some_values_eval eval c st o (es : list expr) (lv : list value) (Pred : store -> list value -> Prop) : Prop := 
    match es with
    | nil => Pred st (rev lv)
    | e :: es' => is_some_value o (eval c st e) (fun st' v => 
        is_some_values_eval eval c st' o es' (v :: lv) Pred)
    end.

Lemma is_some_values_eval_lemma : forall eval c o es cont (Pred : _ -> _ -> Prop),
    eval_fun_correct eval -> 
    (forall vs st, cont st vs = result_some o -> Pred st vs) ->
    forall vs st,
    fold_right (eval_arg_list_aux eval c)
        (fun st args => cont st (rev args)) es st vs = result_some o -> 
    is_some_values_eval eval c st o es vs Pred.
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

Definition apply_post eval c st v vs o := exists clo c', 
    (v = value_closure clo /\ get_closure_ctx clo vs = result_some c' \/
     exists ptr obj, v = value_object ptr /\ binds st ptr obj /\ 
         object_code obj = value_closure clo /\ get_closure_ctx clo (v::vs) = result_some c') /\
    eval c' st (closure_body clo) = result_some o.

Lemma apply_correct : forall eval c st v vs o,
    eval_fun_correct eval ->
    apply eval c st v vs = result_some o ->
    apply_post eval c st v vs o.
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto.
    destruct v; tryfalse.
    (* object *)
    ljs_run_push_auto.
    destruct a; tryfalse. 
    destruct object_attrs; tryfalse. 
    destruct oattrs_code; tryfalse. 
    simpls. 
    ljs_run_push_auto.
    unfolds apply_post. jauto_set; eauto. right. jauto_set; try prove_bag.
    (* closure *)
    ljs_run_push_auto.
    unfolds apply_post. jauto.
Qed.

(* Lemmas for proving the main lemma *)

Lemma eval_app_correct : forall eval c st e es o,
    eval_fun_correct eval ->
    eval_app eval c st e es = result_some o ->
    is_some_value o (eval c st e) (fun st' v => 
        is_some_values_eval eval c st' o es nil (fun st'' vs => 
            apply_post eval c st'' v vs o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch.
    apply is_some_values_eval_lemma with (cont := fun st args => apply eval c st v args); try assumption.
    eauto using apply_correct.
Qed.

Lemma eval_id_correct : forall eval c st s o,
    eval_fun_correct eval -> 
    eval_id eval c st s = result_some o -> 
    exists v, c \(s?) = Some v /\ 
        o = out_ter st (res_value v).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_auto.
    ljs_run_inv. eauto.
Qed.

Lemma eval_if_correct : forall eval c st e e1 e2 o,
    eval_fun_correct eval ->
    eval_if eval c st e e1 e2 = result_some o ->
    is_some_value o (eval c st e) (fun st' v =>
        (v = value_true /\ 
            eval c st' e1 = result_some o) \/
        (v = value_false /\
            eval c st' e2 = result_some o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch. cases_if; eauto.
Qed.

Lemma eval_seq_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_seq eval c st e1 e2 = result_some o -> 
    is_some_value o (eval c st e1) (fun st' v =>
        eval c st' e2 = result_some o).
Proof. 
    introv IH R. unfolds in R.  
    ljs_run_push_auto; jauto.
Qed.

Lemma eval_let_correct : forall eval c st s e1 e2 o,
    eval_fun_correct eval ->
    eval_let eval c st s e1 e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v =>
        exists c', c' = c \(s := v) /\ 
            eval c' st' e2 = result_some o).
Proof. 
    introv IH R. unfolds in R.
    unfold eval_cont in R.
    ljs_run_push_post_auto; ljs_is_some_value_munch; ljs_run_inv; jauto.
Qed. 

Lemma eval_rec_correct : forall eval c st s e1 e2 o,
    eval_fun_correct eval ->
    eval_rec eval c st s e1 e2 = result_some o ->
    exists args body c' v, e1 = expr_lambda args body /\
            v = add_closure c (Some s) args body /\
            c' = c \(s := v) /\
            eval c' st e2 = result_some o.
Proof.
    introv IH R. unfolds in R.
    destruct e1; tryfalse.
    jauto.
Qed.

Definition is_some_eval_objattrs o eval c st attrs Pred : Prop :=
    let 'objattrs_intro e1 e2 e3 e4 := attrs in
    is_some_value o (eval c st e1) (fun st1 v1 =>
    is_some_value o (eval c st1 e2) (fun st2 v2 =>
    is_some_value o (eval c st2 e3) (fun st3 v3 =>
    is_some_value o (eval c st3 e4) (fun st4 v4 =>
        exists b s, v1 = value_string s /\ value_to_bool v2 = Some b /\
            object_oattr_valid oattr_code v4 /\ object_oattr_valid oattr_proto v3 /\
            Pred st4 s b v3 v4)))). 

Definition is_some_eval_objprop o eval c st s prop Pred : Prop :=
    match prop with
    | property_data (data_intro e3 e4 e2 e1) =>
        is_some_value o (eval c st e1) (fun st1 v1 =>
        is_some_value o (eval c st1 e2) (fun st2 v2 =>
        is_some_value o (eval c st2 e3) (fun st3 v3 =>
        is_some_value o (eval c st3 e4) (fun st4 v4 =>
            exists b1 b2 b4, 
                value_to_bool v1 = Some b1 /\
                value_to_bool v2 = Some b2 /\
                value_to_bool v4 = Some b4 /\
                Pred st4 (attributes_data_of (attributes_data_intro v3 b4 b2 b1))))))
    | property_accessor (accessor_intro e3 e4 e2 e1) =>
        is_some_value o (eval c st e1) (fun st1 v1 =>
        is_some_value o (eval c st1 e2) (fun st2 v2 =>
        is_some_value o (eval c st2 e3) (fun st3 v3 =>
        is_some_value o (eval c st3 e4) (fun st4 v4 =>
             exists b1 b2, 
                value_to_bool v1 = Some b1 /\
                value_to_bool v2 = Some b2 /\
                Pred st4 (attributes_accessor_of (attributes_accessor_intro v3 v4 b2 b1))))))
    end.

Fixpoint is_some_eval_objprops o eval c st props obj Pred : Prop :=
    match props with
    | nil => Pred st obj
    | (s, prop) :: props' => 
        is_some_eval_objprop o eval c st s prop (fun st' attr =>
            is_some_eval_objprops o eval c st' props' (set_object_property obj s attr) Pred)
    end.

Fixpoint is_some_eval_internal o eval c st iprops obj Pred : Prop :=
    match iprops with
    | nil => Pred st obj
    | (s, e) :: iprops' =>
        is_some_value o (eval c st e) (fun st' v =>
            is_some_eval_internal o eval c st' iprops' (set_object_internal obj s v) Pred)
    end.

Lemma is_some_eval_objprops_lemma : forall eval c o props cont (Pred : _ -> _ -> Prop),
    eval_fun_correct eval ->
    (forall st obj, cont st obj = result_some o -> Pred st obj) ->
    forall st obj,
        eval_object_properties eval c st props obj cont = result_some o ->
        is_some_eval_objprops o eval c st props obj Pred.
Proof.
    introv IH CH.
    induction props.
    eauto.
    introv H.
    destruct a as (s&[(data)|(acc)]);
    simpls;
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch; substs; repeat eexists; eauto.
Qed.

Lemma is_some_eval_internal_lemma : forall eval c o iprops cont (Pred : _ -> _ -> Prop),
    eval_fun_correct eval ->
    (forall st obj, cont st obj = result_some o -> Pred st obj) ->
    forall st obj,
        eval_object_internal eval c st iprops obj cont = result_some o ->
        is_some_eval_internal o eval c st iprops obj Pred.
Proof.
    introv IH CH.
    induction iprops.
    eauto.
    introv H.
    destruct a as (s&e).
    simpls; ljs_run_push_post_auto; repeat ljs_is_some_value_munch; substs; eauto.
Qed.

Lemma eval_object_correct : forall eval c st attrs l1 l2 o,
    eval_fun_correct eval ->
    eval_object_decl eval c st attrs l1 l2 = result_some o ->
    is_some_eval_objattrs o eval c st attrs (fun st' class ext proto code => 
        let obj := object_intro (oattrs_intro proto class ext code) \{} \{} in
        is_some_eval_internal o eval c st' l1 obj (fun st' obj =>
        is_some_eval_objprops o eval c st' l2 obj (fun st'' obj =>
            exists st''' v,
                (st''', v) = add_object st'' obj /\
                o = out_ter st''' (res_value v)))).
Proof.
    introv IH R. unfolds in R.
    cases_let.
    unfolds.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    case_if. destruct n.
    substs.
    do 2 eexists; splits.
    reflexivity. reflexivity. assumption. assumption.
    eapply is_some_eval_internal_lemma; try eassumption.
    eapply is_some_eval_objprops_lemma; try eassumption.
    intros. cbv beta in H6. cases_let. ljs_run_inv. eauto.
Qed.

Lemma eval_break_correct : forall eval c st s e o,
    eval_fun_correct eval ->
    eval_break eval c st s e = result_some o ->
    is_some_value o (eval c st e) (fun st' v =>
        o = out_ter st' (res_break s v)).
Proof.
    introv IH R. unfolds. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_throw_correct : forall eval c st e o,
    eval_fun_correct eval ->
    eval_throw eval c st e = result_some o ->
    is_some_value o (eval c st e) (fun st' v =>
        o = out_ter st' (res_exception v)).
Proof.
    introv IH R. unfolds. unfolds. unfolds in R.
    ljs_run_push_post_auto; ljs_run_inv; jauto.
Qed.

Lemma eval_tryfinally_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_tryfinally eval c st e1 e2 = result_some o ->
    is_some (eval c st e1) (fun o' =>
        (exists st' r, o' = out_ter st' r /\
            is_some_value o (eval c st' e2) (fun st'' v2 => 
                o = out_ter st'' r)) \/
        (o = o' /\ o' = out_div)). 
Proof.
    introv IH R. unfolds. unfolds in R.
    ljs_run_push_post_auto; eexists; (split; [eassumption | ]); jauto;
    left; do 2 eexists; (split; [eassumption | ]);
    ljs_is_some_value_munch; ljs_run_inv; jauto.
Qed.

Lemma eval_trycatch_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_trycatch eval c st e1 e2 = result_some o ->
    is_some (eval c st e1) (fun o' =>
        (exists st' v, o' = out_ter st' (res_exception v) /\
            is_some_value o (eval c st' e2) (fun st'' vv => 
                apply_post eval c st'' vv [v] o)) \/
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

Lemma eval_label_correct : forall eval c st s e o,
    eval_fun_correct eval ->
    eval_label eval c st s e = result_some o ->
    is_some (eval c st e) (fun o' =>
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

Lemma eval_jseq_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_jseq eval c st e1 e2 = result_some o -> 
    is_some_value o (eval c st e1) (fun st' v =>
        is_some (eval c st' e2) (fun o' =>
            (exists st' v', o' = out_ter st' (res_value v') /\
                o = out_ter st' (res_value (overwrite_value_if_empty v v'))) \/
            (exists s st' v', o' = out_ter st' (res_break s v') /\
                o = out_ter st' (res_break s (overwrite_value_if_empty v v'))) \/
            (exists st' v', o' = out_ter st' (res_exception v') /\
                o = out_ter st' (res_exception v')) \/
            o = out_div /\ o' = out_div)).
Proof. 
    introv IH R. unfolds in R. 
    ljs_run_push_post_auto; substs. 
    eapply is_some_value_munch. eassumption. left. do 2 eexists.
    split. reflexivity. eexists. split. eassumption.
    destruct r; ljs_run_inv; intuition jauto.
    destruct R; substs.
    eapply is_some_value_munch. eassumption.
    left. do 2 eexists. split. reflexivity.
    do 2 eexists; intuition eauto.
    ljs_run_inv. eauto.
Qed.

Lemma eval_lambda_correct : forall eval c st vs e o,
    eval_fun_correct eval ->
    eval_lambda eval c st vs e = result_some o ->
    exists v, v = add_closure c None vs e /\ o = out_ter st (res_value v).
Proof.
    introv IH R. unfolds in R.
    ljs_run_inv. eauto.
Qed.

Lemma eval_eval_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_eval eval c st e1 e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v' =>
        is_some_value o (eval c st' e2) (fun st'' v'' =>
            (exists s ptr obj,
                v' = value_string s /\
                v'' = value_object ptr /\ 
                st'' \(ptr?) = Some obj /\ 
                EjsFromJs.desugar_expr true s = None /\
                o = out_ter st'' (res_exception (value_string "parse-error"))) \/
            exists s ptr obj c1 e, 
                v' = value_string s /\
                v'' = value_object ptr /\ 
                st'' \(ptr?) = Some obj /\ 
                ctx_of_obj obj = Some c1 /\
                EjsFromJs.desugar_expr true s = Some e /\ 
                eval c1 st'' e = result_some o)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_match_option.
    cases_match_option.
    + right. jauto.
    + injects. left. jauto.
Qed.

Local Hint Constructors eval_unary_op int_unary_op num_unary_op.

Lemma eval_op1_correct : forall eval c st op e1 o,
    eval_fun_correct eval ->
    eval_op1 eval c st op e1 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        exists v, eval_unary_op op st' v1 v /\ o = out_ter st' (res_value v)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. 
    destruct op; destruct v; tryfalse; repeat injects; repeat substs; simpls; tryfalse; eauto.
    destruct s; tryfalse; injects; eauto.
Qed.

Local Hint Constructors eval_binary_op int_binary_op num_binary_op num_cmp_binary_op.

Lemma eval_op2_correct : forall eval c st op e1 e2 o,
    eval_fun_correct eval ->
    eval_op2 eval c st op e1 e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            exists v, eval_binary_op op st'' v1 v2 v /\ o = out_ter st'' (res_value v))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. 
    destruct op; destruct v; tryfalse; destruct v0; tryfalse; repeat injects; repeat substs; eauto;
    unfolds binary_operator.
    (* has_own_property *)
    unfolds has_own_property.
    ljs_run_push_post_auto. 
    cases_match_option; repeat injects; substs; eexists; (split; [prove_bag | idtac]);
    apply func_eq_2; try reflexivity; apply func_eq_1; apply func_eq_1;
    unfolds get_object_property; simpl; cases_match_option; reflexivity.
    (* has_internal *)
    unfolds has_internal.
    ljs_run_push_post_auto.
    injects. prove_bag 10.
    (* char_at *)
    unfolds char_at.
    cases_if.
    cases_match_option.
    injects. eauto.
    (* is_accessor *)
    unfolds is_accessor, assert_get_object_ptr.
    ljs_run_push_post_auto.
    cases_match_option; repeat injects; substs. 
    eexists. split. prove_bag. eauto. 
Qed.

Lemma eval_get_internal_correct : forall eval c st s e1 o,
    eval_fun_correct eval ->
    eval_get_internal eval c st e1 s = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        exists ptr obj v, v1 = value_object ptr /\ 
            binds st' ptr obj /\ 
            binds (object_internal obj) s v /\
            o = out_ter st' (res_value v)).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_match_option as Eq.
    injects.
    jauto_set; prove_bag.
Qed.

Lemma eval_set_internal_correct : forall eval c st s e1 e2 o,
    eval_fun_correct eval ->
    eval_set_internal eval c st e1 s e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            exists ptr obj, v1 = value_object ptr /\
                binds st'' ptr obj /\
                index (object_internal obj) s /\
                o = out_ter (st'' \(ptr := set_object_internal obj s v2)) (res_value v2))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    unfolds change_object_cont.
    cases_match_option.
    cases_if.
    injects.
    jauto_set; prove_bag.
Qed.

Lemma eval_get_obj_attr_correct : forall eval c st oa e1 o,
    eval_fun_correct eval ->
    eval_get_obj_attr eval c st e1 oa = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        exists ptr obj, v1 = value_object ptr /\ 
            binds st' ptr obj /\ 
            o = out_ter st' (res_value (get_object_oattr obj oa))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. substs. 
    match goal with obj : object |- _ => destruct obj end.
    jauto_set; prove_bag.
Qed.

Local Hint Constructors object_oattr_valid oattrs_oattr_modifiable.

Lemma eval_set_obj_attr_correct : forall eval c st oa e1 e2 o,
    eval_fun_correct eval ->
    eval_set_obj_attr eval c st e1 oa e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            exists ptr obj, v1 = value_object ptr /\
                binds st'' ptr obj /\
                object_oattr_valid oa v2 /\
                object_oattr_modifiable obj oa /\
                o = out_ter (st'' \(ptr := set_object_oattr obj oa v2)) (res_value v2))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    unfolds change_object_cont.
    cases_match_option; tryfalse.
    ljs_run_push_post_auto.
    injects.
    unfolds set_object_oattr_check.
    cases_let. cases_let. 
    destruct oa; try cases_if; substs; tryfalse;
    repeat injects; simpls; unfold object_oattr_modifiable; try solve [jauto_set; prove_bag];
    destruct v0; tryfalse; repeat injects; jauto_set; prove_bag.
Qed.

Local Hint Constructors attributes_pattr_readable.

Lemma eval_get_attr_correct : forall eval c st pa e1 e2 o,
    eval_fun_correct eval ->
    eval_get_attr eval c st e1 e2 pa = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            exists ptr obj s attrs, v1 = value_object ptr /\
                v2 = value_string s /\
                st'' \(ptr?) = Some obj /\
                binds (object_properties obj) s attrs /\
                attributes_pattr_readable attrs pa /\
                o = out_ter st'' (res_value (get_attributes_pattr attrs pa)))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    ljs_run_inv. substs. 
    unfolds get_object_pattr.
    cases_match_option as Hop;
    apply get_object_property_some_lemma in Hop.
    destruct pa; tryfalse; destruct a; tryfalse; repeat injects; jauto.
Qed.

Local Hint Constructors attributes_pattr_valid attributes_pattr_writable.

Lemma eval_set_attr_correct : forall eval c st pa e1 e2 e3 o,
    eval_fun_correct eval ->
    eval_set_attr eval c st e1 e2 pa e3 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            is_some_value o (eval c st'' e3) (fun st''' v3 =>
                exists ptr obj s, v1 = value_object ptr /\
                    v2 = value_string s /\
                    st''' \(ptr?) = Some obj /\
                    (~index (object_properties obj) s /\
                     object_extensible obj /\
                     attributes_pattr_valid pa v3 /\
                     o = out_ter (st''' \(ptr := set_object_property obj s (new_attributes_pattr pa v3))) 
                             (res_value v3) \/
                     exists attrs, 
                     binds (object_properties obj) s attrs /\
                     attributes_pattr_writable attrs pa /\
                     attributes_pattr_valid pa v3 /\
                     o = out_ter (st''' \(ptr := set_object_property obj s (set_attributes_pattr attrs pa v3))) 
                             (res_value v3))))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    unfolds change_object_cont.
    cases_match_option; tryfalse.
    ljs_run_push_post_auto.
    injects.
    unfolds set_object_pattr.
    substs.
    cases_match_option as Hprop.
    apply get_object_property_some_lemma in Hprop.
    cases_if.
    match goal with H : attributes_pattr_writable ?attrs _ |- _ => 
        destruct attrs as [aa|aa]; destruct aa end;
    destruct pa; try cases_match_option; injects; try solve [jauto_set; eauto 7];
    match goal with H : context [ value_to_bool ?v ] |- _ => destruct v; simpl in H; tryfalse end;
    injects; jauto_set; eauto 7.
    cases_if.
    cases_match_option as Hsome.
    apply get_object_property_none_lemma in Hprop.
    destruct pa;
    try match goal with H : context [ value_to_bool ?v ] |- _ => destruct v; simpl in H; tryfalse end;
    injects; injects; jauto.
Qed.

Lemma eval_delete_field_correct : forall eval c st e1 e2 o,
    eval_fun_correct eval ->
    eval_delete_field eval c st e1 e2 = result_some o ->
    is_some_value o (eval c st e1) (fun st' v1 =>
        is_some_value o (eval c st' e2) (fun st'' v2 =>
            exists ptr obj s attrs, v1 = value_object ptr /\
                st'' \(ptr?) = Some obj /\
                v2 = value_string s /\
                binds (object_properties obj) s attrs /\
                attributes_configurable attrs /\
                o = out_ter (st'' \(ptr := delete_object_property obj s)) (res_value value_undefined))).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_match_option as Hprop.
    apply get_object_property_some_lemma in Hprop.
    cases_if.
    fold_bool.
    do 4 eexists; try eassumption.
    ljs_run_inv. substs. intuition eauto. 
Qed. 

Lemma eval_own_field_names_correct : forall eval c st e o,
    eval_fun_correct eval ->
    eval_own_field_names eval c st e = result_some o ->
    is_some_value o (eval c st e) (fun st' v =>
        exists ptr obj st'' v', v = value_object ptr /\
            st' \(ptr?) = Some obj /\
            (st'', v') = add_object st' (make_prop_list obj) /\
            o = out_ter st'' (res_value v')).
Proof.
    introv IH R. unfolds in R.
    ljs_run_push_post_auto; repeat ljs_is_some_value_munch.
    cases_let.
    ljs_run_inv. unfolds add_object. injects. jauto. 
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
    (eapply rule; [solve [eauto] | ]);
    [ | eapply rulea; assumption]. 

Lemma red_expr_app_2_lemma : forall eval c st v vl o,
    eval_fun_correct eval ->
    apply_post eval c st v vl o ->
    red_expr c st (expr_app_2 v vl) o.
Proof.
    introv IH R.
    unfolds in R.
    repeat destruct_exists R.
    destruct R as ([(R1&R2)|(?&?&R1&R1b&R1c&R2)]&R3).
    (* closure *)
    * substs.
      eapply red_expr_app_2; eauto.
    (* object *)
    * substs.
      eapply red_expr_app_2_object; eauto.
      eapply red_expr_app_2; eauto.
Qed.

Lemma red_expr_eval_many_lemma : forall eval c o C (Pred : _ -> _ -> Prop),
    eval_fun_correct eval -> 
    (forall st vs, Pred st (rev vs) -> red_expr c st (C (rev vs)) o) ->
    forall es st vs,
    is_some_values_eval eval c st o es vs Pred ->
    red_expr c st (expr_eval_many_1 es vs C) o.
Proof.
    introv IH PH.
    induction es; introv R.
    * eapply red_expr_eval_many_1.
      eauto.
    * unfold is_some_values_eval in R at 1.
      ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort.
      eapply red_expr_eval_many_2.
      eauto.
Qed.

Ltac value_to_bool := 
    repeat match goal with H : value_to_bool ?v = Some _ |- _ => destruct v; tryfalse; injects H end.

Ltac ljs_advance_eval_many :=
    repeat (ljs_pretty_advance red_expr_eval_many_1_next red_expr_eval_many_2_abort;
            eapply red_expr_eval_many_2);
    eapply red_expr_eval_many_1.

Lemma red_expr_object_2_lemma1 : forall eval c o (Pred : _ -> _ -> Prop),
    eval_fun_correct eval ->
    (forall st obj, Pred st obj -> red_expr c st (expr_object_2 nil nil obj) o) ->
    forall props st obj,
    is_some_eval_objprops o eval c st props obj Pred ->
    red_expr c st (expr_object_2 nil props obj) o.
Proof.
    introv IH PH.
    induction props. eauto.
    introv R.
    unfold is_some_eval_objprops in R at 1.
    destruct a as (s&[data|acc]).
    destruct data.
    unfolds in R.
    eapply red_expr_object_2_data.
    ljs_advance_eval_many.
    destruct_hyp R.
    value_to_bool.
    eapply red_expr_object_data_1; eauto. 
    destruct acc.
    unfolds in R.
    eapply red_expr_object_2_accessor.
    ljs_advance_eval_many.
    destruct_hyp R.
    value_to_bool.
    eapply red_expr_object_accessor_1; eauto.
Qed.

Lemma red_expr_object_2_lemma2 : forall eval c o props (Pred : _ -> _ -> Prop),
    eval_fun_correct eval ->
    (forall st obj, Pred st obj -> red_expr c st (expr_object_2 nil props obj) o) ->
    forall iprops st obj,
    is_some_eval_internal o eval c st iprops obj Pred ->
    red_expr c st (expr_object_2 iprops props obj) o.
Proof.
    introv IH PH.
    induction iprops. eauto.
    introv R.
    unfold is_some_eval_internal in R at 1.
    destruct a as (s&e).
    eapply red_expr_object_2_internal.
    ljs_advance_eval_many.
    eapply red_expr_object_internal_1; eauto.
Qed.

(* Main lemma *)

Lemma eval_S_correct : forall eval,
    eval_fun_correct eval -> eval_fun_correct (eval_S eval).
Proof.
    introv IH R. unfolds in R.
    destruct e.
    (* empty *)
    ljs_run_inv. apply red_expr_empty.
    (* null *)
    ljs_run_inv. apply red_expr_null.
    (* undefined *)
    ljs_run_inv. apply red_expr_undefined.
    (* string *)
    ljs_run_inv. apply red_expr_string.
    (* number *)
    ljs_run_inv. apply red_expr_number.
    (* int *)
    ljs_run_inv. apply red_expr_int.
    (* bool *)
    ljs_run_inv. apply red_expr_bool.
    (* id *)
    lets (v&Hv&Ho): eval_id_correct IH R.
    rewrite read_option_binds_eq in Hv. 
    inverts Ho.
    eapply red_expr_id; eassumption.
    (* object *)
    lets H: eval_object_correct IH R.
    match goal with H : objattrs |- _ => destruct H end.
    unfolds in H.
    eapply red_expr_object. 
    ljs_advance_eval_many.
    destruct H as (b&s&Hs&Hb&?H&?H&H).
    substs.
    value_to_bool.
    eapply red_expr_object_1; try eassumption.
    applys red_expr_object_2_lemma2 IH; try eassumption.
    applys red_expr_object_2_lemma1 IH; try eassumption.
    introv Ho.
    destruct_hyp Ho.
    injects.
    eapply red_expr_object_2; eauto.
    (* get_attr *)
    lets H: eval_get_attr_correct IH R.
    eapply red_expr_get_attr.
    ljs_advance_eval_many.
    destruct H as (ptr&obj&s&v1&Hy1&Hy2&Hy3&Hy4&Hy5).
    inverts Hy1. inverts Hy2.
    inverts Hy5.
    rewrite read_option_binds_eq in Hy3. 
    destruct obj.
    eapply red_expr_get_attr_1; eauto.
    (* set_attr *)
    lets H: eval_set_attr_correct IH R. 
    eapply red_expr_set_attr.
    ljs_advance_eval_many.
    destruct H as (ptr&obj&s&Hy1&Hy2&Hy3&H).
    rewrite read_option_binds_eq in Hy3.  
    substs.
    destruct obj.
    destruct_hyp H.
    eapply red_expr_set_attr_1_add_field; prove_bag.
    eapply red_expr_set_attr_1; prove_bag.
    (* get_obj_attr *)
    lets H: eval_get_obj_attr_correct IH R.
    ljs_pretty_advance red_expr_get_obj_attr red_expr_get_obj_attr_1_abort.
    destruct_hyp H.
    eapply red_expr_get_obj_attr_1; eauto.
    (* set_obj_attr *)
    lets H: eval_set_obj_attr_correct IH R.
    eapply red_expr_set_obj_attr.
    ljs_advance_eval_many.
    destruct_hyp H.
    eapply red_expr_set_obj_attr_1; eauto.
    (* delete_field *)
    lets H: eval_delete_field_correct IH R.
    eapply red_expr_delete_field.
    ljs_advance_eval_many.
    destruct H as (ptr&obj&s&oattrs&Hv&Ho&Hs&Hp&Hc&H).
    rewrite read_option_binds_eq in Ho. 
    inverts Hv. inverts Hs. subst o.
    eapply red_expr_delete_field_1; eauto.
    (* get_internal *)
    lets H: eval_get_internal_correct IH R.
    eapply red_expr_get_internal.
    ljs_advance_eval_many.
    destruct_hyp H.
    eapply red_expr_get_internal_1; eauto.
    (* set_internal *)
    lets H: eval_set_internal_correct IH R.
    eapply red_expr_set_internal.
    ljs_advance_eval_many.
    destruct_hyp H.
    eapply red_expr_set_internal_1; eauto.
    (* own_field_names *)
    lets H: eval_own_field_names_correct IH R.
    ljs_pretty_advance red_expr_own_field_names red_expr_own_field_names_1_abort.
    repeat destruct_exists H.
    destruct H as (Hv&Ho&Ha&Hb).
    rewrite read_option_binds_eq in Ho. 
    substs. injects.
    eapply red_expr_own_field_names_1; eauto.
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
    eapply red_expr_if_1_true; eauto.
    eapply red_expr_if_1_false; eauto.
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
    eauto.
    (* jseq *)
    lets H: eval_jseq_correct IH R.
    ljs_pretty_advance red_expr_jseq red_expr_jseq_1_abort.
    destruct H as (o'&Ho'&He).
    eapply red_expr_jseq_1.
    eauto.
    destruct_hyp He.
    eapply red_expr_jseq_2.
    eapply red_expr_jseq_2_break.
    eapply red_expr_jseq_2_exception.
    eapply red_expr_jseq_2_div.
    (* let *)
    lets H: eval_let_correct IH R.
    ljs_pretty_advance red_expr_let red_expr_let_1_abort.
    destruct H as (c'&H&Ho2).
    eapply red_expr_let_1. eassumption. eauto.
    (* recc *)
    lets H: eval_rec_correct IH R.
    jauto_set.
    substs.
    eapply red_expr_rec; eauto.
    eauto.
    (* label *)
    lets (o'&Ho&H): eval_label_correct IH R.
    eapply red_expr_label.
    eauto.
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
    eauto.
    destruct H as [(st'&v&Ho1&Ho2)|(He&H)].
    inverts Ho1.
    ljs_pretty_advance red_expr_try_catch_1_exc red_expr_try_catch_2_abort.
    eapply red_expr_try_catch_2.
    eauto using red_expr_app_2_lemma. 
    inverts He.
    eapply red_expr_try_catch_1; eauto.
    (* try_finally *)
    lets (o'&Ho&H): eval_tryfinally_correct IH R. 
    eapply red_expr_try_finally. eauto.
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
    lets (v&Ho&H): eval_lambda_correct IH R.
    inverts H.
    eapply red_expr_lambda; assumption.
    (* eval *)
    lets H: eval_eval_correct IH R.
    eapply red_expr_eval.
    ljs_advance_eval_many.
    inverts H. {
        jauto_set.
        rewrite read_option_binds_eq in H5. 
        substs.
        eapply red_expr_eval_1_parse_error; eauto.
    }
    jauto_set.
    rewrite read_option_binds_eq in H5. 
    substs.
    eapply red_expr_eval_1; eauto.
    ljs_run_inv.
    eauto.
    (* hint *)
    eapply red_expr_hint.
    eauto.
    (* fail *)
    tryfalse.
    (* dump *)
    tryfalse.
Qed.

Lemma eval_0_correct : eval_fun_correct eval_0.
Proof.
    introv H.
    tryfalse.
Qed.

Lemma eval_lazy_correct : forall eval, eval_fun_correct eval -> eval_fun_correct (suspend_eval (fun _ => eval)).
Proof.
    introv IH.
    unfolds.
    eauto. 
Qed.

Lemma lazy_eval_k_correct : forall k, eval_fun_correct (lazy_eval k). 
Proof.
    induction k; eauto using eval_0_correct, eval_S_correct, eval_lazy_correct. 
Qed.

Lemma eval_k_correct : forall k, eval_fun_correct (eval_k k). 
Proof.
    induction k; eauto using eval_0_correct, eval_S_correct. 
Qed.

   