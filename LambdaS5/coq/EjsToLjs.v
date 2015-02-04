Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax.
Require EjsSyntax.
Require JsSyntax.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Local Coercion JsNumber.of_int : Z >-> JsNumber.number.

Module L := LjsSyntax.
Module E := EjsSyntax.
Module J := JsSyntax.

(* TODO move to TLC *)
Global Instance Exists_decidable : 
    forall `(l : list A) P (HD : forall a, Decidable (P a)), Decidable (Exists P l).
Proof.
    introv HD.
    applys decidable_make (exists_st (fun a => decide (P a)) l).
    induction l as [ | a l]; unfolds exists_st; simpl.
    fold_bool; rew_reflect. eauto using Exists_nil_inv. 
    rew_refl.
    rewrite IHl.
    remember (isTrue (P a)) as b1 eqn: Eq1.
    destruct b1; rew_bool; fold_bool. 
    rew_refl in *.
    apply~ Exists_here.
    remember (isTrue (Exists P l)) as b2 eqn: Eq2.
    destruct b2; fold_bool.
    rew_reflect in *.
    apply~ Exists_next.
    rew_reflect in *.
    intro.
    inverts~ H.
Defined.

(* TODO move to utilities *)

Inductive Has_dupes {A : Type} : list A -> Prop :=
    | Has_dupes_here : forall a l, Exists (fun b => a = b) l -> Has_dupes (a :: l)
    | Has_dupes_next : forall a l, Has_dupes l -> Has_dupes (a :: l).

Fixpoint has_dupes `{c : Comparable A} (l : list A) := 
    match l with
    | a :: l' => exists_st (fun b => decide (a = b)) l' || has_dupes l'
    | nil => false
    end.

Global Instance Has_dupes_decidable : forall `(l : list A) `(c : Comparable A),
    Decidable (Has_dupes l).
Proof.
    intros.
    applys decidable_make (has_dupes l).
    induction l as [ | a l]; unfold has_dupes; simpl.
    fold_bool; rew_reflect. intro. inverts H.
    fold has_dupes.
    rewrite IHl.
    skip. (* TODO *)
Defined.


Module DesugarUtils.

Definition make_builtin s := L.expr_id s.

Definition context := make_builtin "%context".

Definition eq e1 e2 := L.expr_op2 L.binary_op_stx_eq e1 e2.

Definition undef_test e := eq e L.expr_undefined.

Definition null_test e := eq e L.expr_null.

Definition type_test e s := eq (L.expr_op1 L.unary_op_typeof e) (L.expr_string s).

Definition make_app_builtin s es := L.expr_app (make_builtin s) es.

Definition is_object_type e := make_app_builtin "%IsObject" e. 

Definition to_object e := make_app_builtin "%ToObject" [e].

Definition to_string e :=
    match e with
    | L.expr_string s => e
    | _ => make_app_builtin "%ToString" [e]
    end.

Definition to_bool e := make_app_builtin "%ToBoolean" [e].

Definition with_error_dispatch e :=
    L.expr_try_catch e (make_builtin "%ErrorDispatch").

Definition prop_accessor_check e := make_app_builtin "%PropAccessorCheck" [e].

(* TODO: get rid of this argsobj nonsense someday *)
Definition make_get_field obj fld :=
    let argsobj := L.expr_object L.default_objattrs [] in
    L.expr_get_field obj (to_string fld) argsobj.

Definition make_set_field_naked obj fld v :=
    let prop := L.property_data (L.data_intro (L.expr_id "%v") L.expr_true L.expr_true L.expr_true) in 
    let argsobj := L.expr_object L.default_objattrs [("0", prop)] in 
    L.expr_let "%v" v (L.expr_set_field obj (to_string fld) (L.expr_id "%v") argsobj).

Definition make_set_field obj fld v :=
    with_error_dispatch (make_app_builtin "%set-property" [to_object obj; to_string fld; v]).

Definition make_var_set fld v :=
    make_app_builtin "%EnvCheckAssign" [L.expr_id "%context"; L.expr_string fld; v; L.expr_id "#strict"].

Definition make_while (tst bdy after : L.expr) := L.expr_undefined.

Definition prop_itr := 
    let tst := L.expr_op2 L.binary_op_has_own_property (L.expr_id "%obj") 
        (L.expr_op1 L.unary_op_prim_to_str (L.expr_id "%index")) in
    let cns := L.expr_let "%rval" 
        (L.expr_get_field (L.expr_id "%obj") (L.expr_op1 L.unary_op_prim_to_str (L.expr_id "%index")) L.expr_null) 
        (L.expr_seq 
            (L.expr_set_bang "%index" (L.expr_op2 L.binary_op_add (L.expr_id "%index") (L.expr_number 1))) 
            (L.expr_id "%rval")) in 
    L.expr_lambda ["%obj"] 
        (L.expr_let "%index" (L.expr_number 0) 
            (L.expr_lambda [] (L.expr_if tst cns L.expr_undefined))).

Definition make_for_in s robj bdy := 
    let sv := L.expr_string s in
    let tst := L.expr_op1 L.unary_op_not (undef_test (L.expr_get_field context sv L.expr_null)) in
    let after := make_set_field context sv (L.expr_app (L.expr_id "%prop_itr") []) in
    L.expr_let "%do_loop"
        (L.expr_lambda nil
            (L.expr_recc "%get_itr" prop_itr
            (L.expr_let "%pnameobj" (make_app_builtin "%propertyNames" [robj; L.expr_false])
            (L.expr_let "%prop_itr"
                (L.expr_app (L.expr_id "%get_itr") [L.expr_id "%pnameobj"])
                (L.expr_seq
                    (make_app_builtin "%set-property" [context; sv; L.expr_app (L.expr_id "%prop_itr") []])
                    (make_while tst bdy after))))))
        (L.expr_if (undef_test robj) 
            L.expr_undefined
            (L.expr_if (null_test robj)
                L.expr_undefined
                (L.expr_app (L.expr_id "%do_loop") []))).

Definition make_if e e1 e2 := L.expr_if (to_bool e) e1 e2.

Definition make_throw e :=
    L.expr_throw (L.expr_object L.default_objattrs 
        [("%js-exn", L.property_data (L.data_intro e L.expr_false L.expr_false L.expr_false))]).

Definition make_with e1 e2 := 
    L.expr_let "%context" (make_app_builtin "%makeWithContext" [context; e1]) e2.

Definition if_strict e1 e2 := L.expr_if (L.expr_id "#strict") e1 e2.

Definition syntax_error s := make_app_builtin "%SyntaxError" [L.expr_string s].

Definition new_context_in ctx e :=
    L.expr_let "%parent" context (L.expr_let "%context" ctx e).

Definition derived_context_in flds e :=
    new_context_in (L.expr_object (L.objattrs_with_proto (L.expr_id "%parent") L.default_objattrs) flds) e.

Definition to_js_error e := make_app_builtin "%ToJSError" [e].

(*

Definition create_context args body parent := 
    

Definition make_lambda args body := 

*)

Definition make_fobj is (e ctx : L.expr) :=
    ifb Exists (fun nm => nm = "arguments" \/ nm = "eval") is \/ Has_dupes is then 
        if_strict (syntax_error "Illegal function definition") L.expr_undefined else
    L.expr_null.

Definition make_func_stmt i is e :=
    let fobj := make_fobj is e context in
    make_set_field_naked context (L.expr_string i) fobj.

Definition make_try_catch body i catch :=
    let prop := L.property_data (L.data_intro (to_js_error (L.expr_id i)) L.expr_true L.expr_false L.expr_false) in
    L.expr_try_catch body (L.expr_lambda [i] (derived_context_in [(i, prop)] catch)).

Definition make_xfix s e :=
    match e with
    | L.expr_get_field obj fld _ => make_app_builtin s [obj; fld]
    | _ => syntax_error "Illegal use of an prefix/postfix operator"
    end.

Definition make_typeof e :=
    match e with
    | L.expr_get_field (L.expr_id "%context") fldexpr _ => 
        make_app_builtin "%Typeof" [context; fldexpr]
    | _ => L.expr_op1 L.unary_op_typeof e    
    end.

Definition make_delete e :=
    match e with
    | L.expr_get_field obj fldexpr _ =>
        match obj with
        | L.expr_id "%context" => syntax_error "Delete on context"
        | _ => L.expr_delete_field obj (to_string fldexpr)
        end
    | _ => L.expr_true
    end.

Definition make_op1 op e :=
    match op with
    | J.unary_op_delete => make_delete e
    | J.unary_op_post_incr => make_xfix "%PostIncrement" e
    | J.unary_op_post_decr => make_xfix "%PostDecrement" e
    | J.unary_op_pre_incr => make_xfix "%PrefixIncrement" e
    | J.unary_op_pre_decr => make_xfix "%PrefixDecrement" e
    | J.unary_op_neg => make_app_builtin "%UnaryNeg" [e]
    | J.unary_op_add => make_app_builtin "%UnaryPlus" [e]
    | J.unary_op_bitwise_not => make_app_builtin "%BitwiseNot" [e]
    | J.unary_op_not => L.expr_op1 L.unary_op_not e
    | J.unary_op_typeof => make_typeof e
    | J.unary_op_void => L.expr_op1 L.unary_op_void e
    end.

Definition op2_func op := L.expr_lambda ["%x1";"%x2"] (L.expr_op2 op (L.expr_id "%x1") (L.expr_id "%x2")).

Definition make_op2 op e1 e2 :=
    match op with
    | J.binary_op_coma => syntax_error "Unknown infix operator"
    | J.binary_op_mult => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_mul]
    | J.binary_op_div => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_div]
    | J.binary_op_mod => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_mod]
    | J.binary_op_bitwise_and => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_band]
    | J.binary_op_bitwise_or => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_bor]
    | J.binary_op_bitwise_xor => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_bxor]
    | J.binary_op_and => L.expr_let "%e" e1 (L.expr_if (to_bool e1) e2 (L.expr_id "%e"))
    | J.binary_op_or => L.expr_let "%e" e1 (L.expr_if (to_bool e1) (L.expr_id "%e") e2)
    | J.binary_op_add => make_app_builtin "%PrimAdd" [e1; e2] 
    | J.binary_op_sub => make_app_builtin "%PrimSub" [e1; e2] 
    | J.binary_op_left_shift => make_app_builtin "%LeftShift" [e1; e2] 
    | J.binary_op_right_shift => make_app_builtin "%SignedRightShift" [e1; e2] 
    | J.binary_op_unsigned_right_shift => make_app_builtin "%UnsignedRightShift" [e1; e2] 
    | J.binary_op_lt => make_app_builtin "%LessThan" [e1; e2] 
    | J.binary_op_gt => make_app_builtin "%GreaterThan" [e1; e2] 
    | J.binary_op_le => make_app_builtin "%LessEqual" [e1; e2] 
    | J.binary_op_ge => make_app_builtin "%GreaterEqual" [e1; e2] 
    | J.binary_op_instanceof => make_app_builtin "%instanceof" [e1; e2] 
    | J.binary_op_in => make_app_builtin "%in" [e1; e2] 
    | J.binary_op_equal => make_app_builtin "%EqEq" [e1; e2] 
    | J.binary_op_strict_equal => L.expr_op2 L.binary_op_stx_eq e1 e2 
    | J.binary_op_disequal => L.expr_op1 L.unary_op_not (make_app_builtin "%EqEq" [e1; e2])
    | J.binary_op_strict_disequal => L.expr_op1 L.unary_op_not (L.expr_op2 L.binary_op_stx_eq e1 e2)
    end.

Definition make_array es :=
    let mkprop e := L.property_data (L.data_intro e L.expr_true L.expr_true L.expr_true) in
    let exp_props := number_list_from 0 (map mkprop es) in
    let l_prop := L.property_data (L.data_intro (L.expr_number (length exp_props)) L.expr_true L.expr_false L.expr_false) in
    let attrs := L.objattrs_intro (L.expr_string "Array") L.expr_true (make_builtin "%ArrayProto") L.expr_null L.expr_undefined in 
    L.expr_object attrs (("length", l_prop) :: exp_props).

Definition make_args_obj is_new (es : list L.expr) := 
    let mkprop e := L.property_data (L.data_intro e L.expr_true L.expr_true L.expr_true) in
    let props := zipl_stream (id_stream_from 0) (map mkprop es) in
    let arg_constructor := if is_new then make_builtin "%mkNewArgsObj" else make_builtin "%mkArgsObj" in
    L.expr_app arg_constructor [L.expr_object L.default_objattrs props].

Definition throw_typ_error msg := make_app_builtin "%TypeError" [L.expr_string msg].

Definition appexpr_check e1 e2  := 
    L.expr_if (type_test e1 "function") e2 (throw_typ_error "Not a function").

Definition make_app (e : L.expr) es := 
    let args_obj := make_args_obj false es in 
    match e with
    | L.expr_get_field (L.expr_id "%context") (L.expr_string "eval") _ =>
        make_app_builtin "%maybeDirectEval" [L.expr_id "%this"; L.expr_id "%context"; args_obj; L.expr_id "#strict"]
    | L.expr_get_field (L.expr_id "%context") _ _ =>
        L.expr_let "%fun" e (appexpr_check (L.expr_id "%fun")
            (L.expr_app (L.expr_id "%fun") [L.expr_undefined; args_obj]))
    | L.expr_get_field obj fld _ =>
        L.expr_let "%obj" obj (L.expr_let "%fun" (make_get_field (to_object (L.expr_id "%obj")) fld) 
            (L.expr_app (L.expr_id "%fun") [to_object (L.expr_id "%obj"); args_obj]))
    | _ => (* TODO get rid of the copy-paste *)
        L.expr_let "%fun" e (appexpr_check (L.expr_id "%fun")
            (L.expr_app (L.expr_id "%fun") [L.expr_undefined; args_obj]))
    end.

(* TODO move to utils *)
Fixpoint remove_dupes' `{c : Comparable A} (l : list A) (met : list A) :=
    match l with
    | nil => nil
    | a :: l' => ifb Mem a met then remove_dupes' l' met else a :: remove_dupes' l' (a :: met)
    end.

Definition remove_dupes `{c : Comparable A} (l : list A) := remove_dupes' l nil.

Fixpoint assocs {B : Type} `{c : Comparable A} (a : A) (l : list (A*B)) := 
    match l with
    | nil => nil
    | (b, v) :: l' => ifb a = b then v :: assocs a l' else assocs a l'
    end.

Definition combine_two_props (p1 p2 : L.property) :=
    match p1, p2 with (* TODO error handling? 11.1.5 *)
    | L.property_data d, L.property_data _ => p1
    | L.property_accessor (L.accessor_intro g L.expr_undefined e c), L.property_accessor (L.accessor_intro L.expr_undefined s _ _) =>
        L.property_accessor (L.accessor_intro g s e c)
    | L.property_accessor (L.accessor_intro L.expr_undefined s e c), L.property_accessor (L.accessor_intro g L.expr_undefined _ _) =>
        L.property_accessor (L.accessor_intro g s e c)
    | _, _ => L.property_data (L.data_intro (syntax_error "Invalid object declaration") L.expr_true L.expr_true L.expr_true)
    end.

(* TODO: move *)
Global Instance property_inhab : Inhab L.property.
Proof.
    intros. apply (prove_Inhab (L.property_data (L.data_intro L.expr_undefined L.expr_undefined L.expr_undefined L.expr_undefined))).
Defined.

Definition combine_props ps :=
    match ps with
    | p :: ps' => fold_left combine_two_props p ps'
    | nil => arbitrary
    end.

Definition make_object ps :=    
    let gs_ids := remove_dupes (map fst ps) in
    let props := map (fun s => (s, combine_props (assocs s ps))) gs_ids in
    let oa := L.objattrs_intro (L.expr_string "Object") L.expr_true (make_builtin "%ObjectProto") L.expr_undefined L.expr_undefined in
    L.expr_object oa props.

Definition make_var_decl is e := (* TODO make it work well *)
    let mkvar i := (i, L.property_data (L.data_intro L.expr_undefined L.expr_true L.expr_false L.expr_false)) in
    derived_context_in (map mkvar is) e.

End DesugarUtils.

Import DesugarUtils.

(* Note: using List instead of LibList for fixpoint to be accepted *)
Fixpoint ejs_to_ljs (e : E.expr) : L.expr :=
    let map_ejs_to_ljs := List.map ejs_to_ljs in 
    let map_property_to_ljs := (fix f l := match l with nil => nil | (s, e) :: l' => (s, property_to_ljs e) :: f l' end) in
    match e with
    | E.expr_true => L.expr_true
    | E.expr_false => L.expr_false
    | E.expr_undefined => L.expr_undefined
    | E.expr_null => L.expr_null
    | E.expr_number n => L.expr_number n
    | E.expr_string s => L.expr_string s
(*    | E.expr_id i => L.expr_id i *)
    | E.expr_var_id i => make_get_field context (L.expr_string i)
    | E.expr_var_decl is e => make_var_decl is (ejs_to_ljs e) (* TODO variables!!! *)
    | E.expr_var_set i e => make_var_set i (ejs_to_ljs e)
    | E.expr_this => make_builtin "%this"
    | E.expr_object ps => make_object (map_property_to_ljs ps) 
    | E.expr_array es => make_array (map_ejs_to_ljs es)
    | E.expr_func is e => make_fobj is (ejs_to_ljs e) context 
    | E.expr_app e es => make_app (ejs_to_ljs e) (map_ejs_to_ljs es)
    | E.expr_func_stmt i is e => make_func_stmt i is (ejs_to_ljs e)
    | E.expr_seq e1 e2 => L.expr_seq (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_if e e1 e2 => make_if (ejs_to_ljs e) (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_op1 op e => make_op1 op (ejs_to_ljs e)
    | E.expr_op2 op e1 e2 => make_op2 op (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_set_field e1 e2 e3 => make_set_field (ejs_to_ljs e1) (ejs_to_ljs e2) (ejs_to_ljs e3)
    | E.expr_get_field e1 e2 => make_get_field (prop_accessor_check (ejs_to_ljs e1)) (ejs_to_ljs e2)
    | E.expr_for_in s e1 e2 => make_for_in s (ejs_to_ljs e1) (ejs_to_ljs e2) 
    | E.expr_while e1 e2 e3 => make_while (ejs_to_ljs e1) (ejs_to_ljs e2) (ejs_to_ljs e3) 
    | E.expr_label s e => L.expr_label s (ejs_to_ljs e)
    | E.expr_break s e => L.expr_break s (ejs_to_ljs e)
    | E.expr_throw e => make_throw (ejs_to_ljs e)
    | E.expr_try_catch e1 i e2 => make_try_catch (ejs_to_ljs e1) i (ejs_to_ljs e2)
    | E.expr_try_finally e1 e2 => L.expr_try_finally (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_with e1 e2 => make_with (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_strict e => L.expr_let "#strict" L.expr_true (ejs_to_ljs e)
    | E.expr_nonstrict e => L.expr_let "#strict" L.expr_false (ejs_to_ljs e)
    | E.expr_syntaxerror => syntax_error "Syntax error"
    | _ => L.expr_dump
    end
with property_to_ljs p :=
    match p with
    | E.property_data d => 
        L.property_data (L.data_intro (ejs_to_ljs d) L.expr_true L.expr_true L.expr_true)
    | E.property_getter d => 
        L.property_accessor (L.accessor_intro (ejs_to_ljs d) L.expr_undefined L.expr_false L.expr_false)
    | E.property_setter d =>
        L.property_accessor (L.accessor_intro L.expr_undefined (ejs_to_ljs d) L.expr_false L.expr_false)
    end.

Definition ejs_prog_to_ljs ep :=
    let '(strict, inner) := 
        match ep with
        | E.expr_strict e => (true, ep)
        | _ => (false, E.expr_nonstrict ep)
        end in
    L.expr_let "%context" (L.expr_id (if strict then "%strictContext" else "%nonstrictContext")) 
        (ejs_to_ljs inner). (* TODO: global variable handling *)
