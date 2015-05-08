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

Module Import EjsToLjsHelper.
Module L := LjsSyntax.
Module E := EjsSyntax.
Module J := JsSyntax.
End EjsToLjsHelper.

Definition make_builtin s := L.expr_id s.

Definition context := make_builtin "$context".

Definition eq e1 e2 := L.expr_op2 L.binary_op_stx_eq e1 e2.

Definition undef_test e := eq e L.expr_undefined.

Definition null_test e := eq e L.expr_null.

Definition type_test e s := eq (L.expr_op1 L.unary_op_typeof e) (L.expr_string s).

Definition make_not e := L.expr_op1 L.unary_op_not e.

Definition make_app_builtin s es := L.expr_app (make_builtin s) es.

Definition is_object_type e := L.expr_op1 L.unary_op_is_object e. 

Definition to_object e := make_app_builtin "%ToObject" [e].

Definition to_string e :=
    match e with
    | L.expr_string s => e
    | _ => make_app_builtin "%ToString" [e]
    end.

Definition to_bool e := make_app_builtin "%ToBoolean" [e].

Definition with_error_dispatch e :=
    L.expr_try_catch e (make_builtin "%ErrorDispatch").

Definition make_seq e1 e2 := L.expr_jseq e1 e2.

Definition make_get_field obj fld :=
    make_app_builtin "%GetField" [obj; fld].

Definition make_set_field_naked obj fld v :=
    L.expr_set_field obj (to_string fld) v.

Definition make_set_field obj fld v :=
    with_error_dispatch (make_app_builtin "%set-property" [to_object obj; to_string fld; v]).

Definition make_var_set fld v :=
    make_app_builtin "%EnvCheckAssign" [L.expr_id "$context"; L.expr_string fld; v; L.expr_id "$strict"].

Definition make_var_id i :=    
    make_app_builtin "%EnvGet" [L.expr_id "$context"; L.expr_string i; L.expr_id "$strict"].

Definition make_getter e := make_app_builtin "%MakeGetter" [e].

Definition make_setter e := make_app_builtin "%MakeSetter" [e].

Definition while_body (tst bdy after : L.expr) := 
    (L.expr_if (to_bool tst) 
        (L.expr_jseq bdy (L.expr_seq after (L.expr_app (L.expr_id "#while_loop") [])))
        L.expr_empty).

Definition make_while (tst bdy after : L.expr) := 
    L.expr_recc "#while_loop" 
        (L.expr_lambda [] (while_body tst bdy after))
        (L.expr_app (L.expr_id "#while_loop") []).

Definition make_do_while (bdy tst : L.expr) :=
    L.expr_recc "%do_while_loop" 
        (L.expr_lambda []
            (L.expr_jseq bdy 
                (L.expr_if (to_bool tst) 
                    (L.expr_app (L.expr_id "%do_while_loop") [])
                     L.expr_empty)))
        (L.expr_app (L.expr_id "%do_while_loop") []).
    
Definition make_for_in (s:string) (robj bdy:L.expr) := L.expr_undefined.
(* TODO
    let sv := L.expr_string s in
    let tst := L.expr_op1 L.unary_op_not (undef_test (L.expr_get_field context sv)) in
    let after := make_set_field context sv (L.expr_app (L.expr_id "%prop_itr") []) in
    L.expr_let "%do_loop"
        (L.expr_lambda nil
            (L.expr_recc "%get_itr" (make_builtin "%PropItr")
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
*)

Definition make_if e e1 e2 := L.expr_if (to_bool e) e1 e2.

Definition make_throw e :=
    L.expr_throw (make_app_builtin "%JSError" [e]).

Definition new_context_in ctx e :=
    L.expr_let "$context" ctx e.

Definition make_with e1 e2 := 
    new_context_in (make_app_builtin "%newObjEnvRec" [context; to_object e1; L.expr_true]) e2.

Definition if_strict e1 e2 := L.expr_if (L.expr_id "$strict") e1 e2.

Definition syntax_error s := make_app_builtin "%SyntaxError" [L.expr_string s].

Definition make_var_decl is e := 
    let flds := List.map (fun ip => 
        let '(i, e) := ip in 
        make_app_builtin "%DeclEnvAddMutableBinding" [context; L.expr_string i; e; L.expr_false]) is in
    new_context_in (make_app_builtin "%newDeclEnvRec" [context]) (
    L.expr_seq (L.expr_seqs flds) e).

Definition make_strictness b e := 
    L.expr_let "$strict" (L.expr_bool b) e.

Definition make_resolve_this e :=
    make_app_builtin "%resolveThis" [L.expr_id "$strict"; e].

Definition make_lambda f (is : list string) p := 
    let 'E.prog_intro str vis e := p in 
    let args_obj := L.expr_id "%args" in
    let argdecls := 
        map (fun p => let '(vnum, vid) := p in (vid, L.expr_get_field (L.expr_id "%args") (L.expr_string vnum))) 
            (zipl_stream (id_stream_from 0) is) in
    let vdecls := map (fun i => (i, L.expr_undefined)) vis in
    L.expr_lambda ["$this"; "%args"] (
    L.expr_label "%ret" (
    L.expr_let "$this" (make_resolve_this (L.expr_id "$this")) (
    make_var_decl (vdecls ++ ("arguments", make_app_builtin "%mkArgsObj" [args_obj]) :: argdecls) (
    make_strictness str (
    L.expr_seq (f e) L.expr_undefined))))).

Definition make_fobj f is p (ctx : L.expr) :=
    ifb Exists (fun nm => nm = "arguments" \/ nm = "eval") is \/ Has_dupes is then 
        if_strict (syntax_error "Illegal function definition") L.expr_undefined else
    make_app_builtin "%MakeFunctionObject" 
        [make_lambda f is p; L.expr_number (length is); L.expr_id "$strict"].

Definition make_rec_fobj f i is p ctx :=
    let fobj := make_fobj f is p ctx in
    make_var_decl [(i, L.expr_undefined)] (make_var_set i fobj).

Definition make_func_stmt f i is p :=
    let fobj := make_fobj f is p context in
    make_app_builtin "%defineFunction" [context; L.expr_string i; fobj].

Definition make_try_catch body i catch :=
    L.expr_try_catch body (L.expr_lambda ["exc"] (
        make_var_decl [(i, L.expr_get_field (L.expr_id "exc") (L.expr_string "%js-exn"))] catch)).

Definition make_xfix s f e :=
    match e with
    | E.expr_var_id fld => make_app_builtin s [context; L.expr_string fld]
    | E.expr_get_field obj fld => make_app_builtin s [f obj; f fld]
    | _ => syntax_error "Illegal use of an prefix/postfix operator"
    end.

Definition make_typeof f e :=
    match e with
    | E.expr_var_id fldexpr => 
        make_app_builtin "%EnvTypeof" [context; L.expr_string fldexpr]
    | _ => make_app_builtin "%Typeof" [f e]
    end.

Definition make_delete f e :=
    match e with
    | E.expr_get_field obj fldexpr =>
        make_app_builtin "%Delete" [f obj; f fldexpr; L.expr_id "$strict"]
    | E.expr_var_id fldexpr => 
        make_app_builtin "%EnvDelete" [context; L.expr_string fldexpr; L.expr_id "$strict"]
    | _ => L.expr_true
    end.

Definition make_op1 f op e :=
    match op with
    | J.unary_op_delete => make_delete f e
    | J.unary_op_post_incr => make_xfix "%PostIncrement" f e
    | J.unary_op_post_decr => make_xfix "%PostDecrement" f e
    | J.unary_op_pre_incr => make_xfix "%PrefixIncrement" f e
    | J.unary_op_pre_decr => make_xfix "%PrefixDecrement" f e
    | J.unary_op_neg => make_app_builtin "%UnaryNeg" [f e]
    | J.unary_op_add => make_app_builtin "%UnaryPlus" [f e]
    | J.unary_op_bitwise_not => make_app_builtin "%BitwiseNot" [f e]
    | J.unary_op_not => make_app_builtin "%UnaryNot" [f e]
    | J.unary_op_typeof => make_typeof f e
    | J.unary_op_void => make_app_builtin "%Void" [f e]
    end.

Definition op2_func op := L.expr_lambda ["x1";"x2"] (L.expr_op2 op (L.expr_id "x1") (L.expr_id "x2")).

Definition make_and e1 e2 := L.expr_let "e" e1 (L.expr_if (to_bool e1) e2 (L.expr_id "e")).

Definition make_or e1 e2 := L.expr_let "e" e1 (L.expr_if (to_bool e1) (L.expr_id "e") e2).

Definition make_op2 op e1 e2 :=
    match op with
    | J.binary_op_coma => L.expr_seq e1 e2
    | J.binary_op_sub => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_sub] 
    | J.binary_op_mult => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_mul]
    | J.binary_op_div => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_div]
    | J.binary_op_mod => make_app_builtin "%PrimMultOp" [e1; e2; op2_func L.binary_op_mod]
    | J.binary_op_bitwise_and => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_band]
    | J.binary_op_bitwise_or => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_bor]
    | J.binary_op_bitwise_xor => make_app_builtin "%BitwiseInfix" [e1; e2; op2_func L.binary_op_bxor]
    | J.binary_op_and => make_and e1 e2
    | J.binary_op_or => make_or e1 e2
    | J.binary_op_add => make_app_builtin "%PrimAdd" [e1; e2] 
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
    | J.binary_op_strict_equal => make_app_builtin "%StxEq" [e1; e2] 
    | J.binary_op_disequal => L.expr_op1 L.unary_op_not (make_app_builtin "%EqEq" [e1; e2])
    | J.binary_op_strict_disequal => L.expr_op1 L.unary_op_not (make_app_builtin "%StxEq" [e1; e2])
    end.

Definition make_array es :=
    let mkprop e := L.property_data (L.data_intro e L.expr_true L.expr_true L.expr_true) in
    let exp_props := number_list_from 0 (map mkprop es) in
    let l_prop := L.property_data (L.data_intro (L.expr_number (length exp_props)) L.expr_true L.expr_false L.expr_false) in
    let attrs := L.objattrs_intro (L.expr_string "Array") L.expr_true (make_builtin "%ArrayProto") L.expr_null in 
    L.expr_object attrs nil (("length", l_prop) :: exp_props).

Definition make_args_obj (es : list L.expr) := 
    let mkprop e := L.property_data (L.data_intro e L.expr_true L.expr_true L.expr_true) in
    let props := zipl_stream (id_stream_from 0) (map mkprop es) in
    L.expr_object L.default_objattrs nil props.

Definition throw_typ_error msg := make_app_builtin "%TypeError" [L.expr_string msg].

Definition appexpr_check e1 e2 e3 := make_app_builtin "%AppExprCheck" [e1; e2; e3].

Definition make_app f (e : E.expr) es := 
    let args_obj := make_args_obj es in 
    match e with
    | E.expr_var_id "eval" =>
        make_app_builtin "%maybeDirectEval" [L.expr_id "$this"; L.expr_id "$context"; args_obj; L.expr_id "$strict"]
    | E.expr_get_field obj fld =>
        make_app_builtin "%AppMethod" [f obj; f fld; args_obj]
    | _ => 
        make_app_builtin "%AppExprCheck" [f e; L.expr_undefined; args_obj]
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
    let oa := L.objattrs_intro (L.expr_string "Object") L.expr_true (make_builtin "%ObjectProto") L.expr_undefined in
    L.expr_object oa nil props.

Definition make_new e es := make_app_builtin "%PrimNew" [e; make_args_obj es].

Definition make_case (tb : L.expr * L.expr) cont found := let (test, body) := tb in
    L.expr_let "found" (make_or (eq (L.expr_id "disc") test) (L.expr_id found))
        (L.expr_seq
            (L.expr_if (L.expr_id "found") body L.expr_undefined)
            (cont "found")).

Definition make_cases cls last := fold_right make_case last cls.

Definition make_switch_nodefault e cls :=
    L.expr_let "disc" e (
    L.expr_let "found" L.expr_false (
    make_cases cls (fun _ => L.expr_empty) "found")).

Definition make_switch_withdefault e acls def bcls :=
    let last_case found := L.expr_if (L.expr_id found) L.expr_empty (L.expr_app (L.expr_id "deflt") []) in
    let deflt_case cont found := 
        L.expr_seq (L.expr_if (L.expr_id found) (L.expr_app (L.expr_id "deflt") []) L.expr_empty)
                   (cont found) in
    L.expr_let "disc" e (
    L.expr_let "deflt" (L.expr_lambda [] def) (
    L.expr_let "found" L.expr_false (
    make_cases acls (deflt_case (make_cases bcls last_case)) "found"))).

(* Note: using List instead of LibList for fixpoint to be accepted *)
Fixpoint ejs_to_ljs (e : E.expr) : L.expr :=
    match e with
    | E.expr_noop e => L.expr_hint "" (ejs_to_ljs e) (* just to make induction easier *)
    | E.expr_empty => L.expr_empty
    | E.expr_true => L.expr_true
    | E.expr_false => L.expr_false
    | E.expr_undefined => L.expr_undefined
    | E.expr_null => L.expr_null
    | E.expr_number n => L.expr_number n
    | E.expr_string s => L.expr_string s
(*    | E.expr_id i => L.expr_id i *)
    | E.expr_var_id i => make_var_id i
(*    | E.expr_var_decl is e => make_var_decl is (ejs_to_ljs e) *)
    | E.expr_var_set i e => make_var_set i (ejs_to_ljs e)
    | E.expr_this => make_builtin "$this"
    | E.expr_object ps => make_object (List.map (fun (p : string * E.property) => let (a,b) := p in (a, property_to_ljs b)) ps) 
    | E.expr_array es => make_array (List.map ejs_to_ljs es)
    | E.expr_app e es => make_app ejs_to_ljs e (List.map ejs_to_ljs es)
    | E.expr_func None is p => make_fobj ejs_to_ljs is p context
    | E.expr_func (Some i) is p => make_rec_fobj ejs_to_ljs i is p context 
    | E.expr_func_stmt i is p => make_func_stmt ejs_to_ljs i is p
    | E.expr_fseq e1 e2 => L.expr_seq (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_seq e1 e2 => make_seq (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_if e e1 e2 => make_if (ejs_to_ljs e) (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_op1 op e => make_op1 ejs_to_ljs op e
    | E.expr_op2 op e1 e2 => make_op2 op (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_set_field e1 e2 e3 => make_set_field (ejs_to_ljs e1) (ejs_to_ljs e2) (ejs_to_ljs e3)
    | E.expr_get_field e1 e2 => make_get_field (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_for_in s e1 e2 => make_for_in s (ejs_to_ljs e1) (ejs_to_ljs e2) 
    | E.expr_while e1 e2 e3 => make_while (ejs_to_ljs e1) (ejs_to_ljs e2) (ejs_to_ljs e3) 
    | E.expr_do_while e1 e2 => make_do_while (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_label s e => L.expr_label s (ejs_to_ljs e)
    | E.expr_break s e => L.expr_break s (ejs_to_ljs e)
    | E.expr_throw e => make_throw (ejs_to_ljs e)
    | E.expr_try_catch e1 i e2 => make_try_catch (ejs_to_ljs e1) i (ejs_to_ljs e2)
    | E.expr_try_finally e1 e2 => L.expr_try_finally (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_with e1 e2 => make_with (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_new e es => make_new (ejs_to_ljs e) (List.map ejs_to_ljs es)
    | E.expr_syntaxerror => syntax_error "Syntax error"
    | E.expr_switch e (E.switchbody_nodefault cls) => 
        make_switch_nodefault (ejs_to_ljs e) (List.map (fun (p : E.expr * E.expr) => let (a, b) := p in (ejs_to_ljs a, ejs_to_ljs b)) cls) 
    | E.expr_switch e (E.switchbody_withdefault acls def bcls) => 
        make_switch_withdefault (ejs_to_ljs e) 
            (List.map (fun (p : E.expr * E.expr) => let (a, b) := p in (ejs_to_ljs a, ejs_to_ljs b)) acls) 
            (ejs_to_ljs def)
            (List.map (fun (p : E.expr * E.expr) => let (a, b) := p in (ejs_to_ljs a, ejs_to_ljs b)) bcls) 
    end
with property_to_ljs (p : E.property) : L.property :=
    match p with
    | E.property_data d => 
        L.property_data (L.data_intro (ejs_to_ljs d) L.expr_true L.expr_true L.expr_true)
    | E.property_getter d => 
        L.property_accessor (L.accessor_intro (make_getter (ejs_to_ljs d)) L.expr_undefined L.expr_false L.expr_false)
    | E.property_setter d =>
        L.property_accessor (L.accessor_intro L.expr_undefined (make_setter (ejs_to_ljs d)) L.expr_false L.expr_false)
    end.

Definition init_global i :=
    make_app_builtin "%defineGlobalVar" [context; L.expr_string i].

Definition ejs_prog_to_ljs ep :=
    let 'E.prog_intro strict is inner := ep in
    L.expr_let "$context" (L.expr_id (if strict then "%strictContext" else "%nonstrictContext")) 
        (L.expr_let "$this" (L.expr_id "$context") 
            (L.expr_seq (L.expr_seqs (List.map init_global is)) (make_strictness strict (ejs_to_ljs inner)))). 
