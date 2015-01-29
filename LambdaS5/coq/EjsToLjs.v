Require Import LjsShared.
Require Import JsNumber.
Require LjsSyntax.
Require EjsSyntax.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Local Coercion JsNumber.of_int : Z >-> JsNumber.number.

Module L := LjsSyntax.
Module E := EjsSyntax.

Module DesugarUtils.

Definition make_builtin s := L.expr_id s.

Definition context := make_builtin "%context".

Definition eq e1 e2 := L.expr_op2 L.binary_op_stx_eq e1 e2.

Definition undef_test e := eq e L.expr_undefined.

Definition null_test e := eq e L.expr_null.

Definition type_test e s := eq (L.expr_op1 L.unary_op_typeof e) (L.expr_string s).

Definition make_app_builtin s es := L.expr_app (make_builtin s) es.

Definition is_object_type e := make_app_builtin "%IsObject" e. 

Definition to_object e :=
    match e with
    | L.expr_id "%context" => e
    | _ => make_app_builtin "%ToObject" [e]
    end.

Definition to_string e :=
    match e with
    | L.expr_string s => e
    | _ => make_app_builtin "%ToString" [e]
    end.

Definition with_error_dispatch e :=
    L.expr_try_catch e (make_builtin "%ErrorDispatch").

Definition prop_accessor_check e :=
    match e with
    | L.expr_id "%context" => e
    | _ => make_app_builtin "%PropAccessorCheck" [e]
    end.

Definition make_get_field obj fld :=
    let argsobj := L.expr_object L.default_objattrs [] in
    L.expr_get_field obj fld argsobj.

Definition make_set_field obj fld v :=
    match obj with
    | L.expr_id "%context" => make_app_builtin "%EnvCheckAssign" [obj; fld; v; L.expr_id "#strict"]
    | _ => with_error_dispatch (make_app_builtin "%set-property" [obj; fld; v])
    end.

Definition get_while (tst bdy after : L.expr) := L.expr_undefined.

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
                    (get_while tst bdy after))))))
        (L.expr_if (undef_test robj) 
            L.expr_undefined
            (L.expr_if (null_test robj)
                L.expr_undefined
                (L.expr_app (L.expr_id "%do_loop") []))).

End DesugarUtils.

Import DesugarUtils.

Fixpoint ejs_to_ljs (e : E.expr) : L.expr :=
    match e with
    | E.expr_true => L.expr_true
    | E.expr_false => L.expr_false
    | E.expr_undefined => L.expr_undefined
    | E.expr_null => L.expr_null
    | E.expr_number n => L.expr_number n
    | E.expr_string s => L.expr_string s
    | E.expr_id i => L.expr_id i
    | E.expr_this => make_builtin "%this"
    | E.expr_seq e1 e2 => L.expr_seq (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_if e e1 e2 => 
        L.expr_if (make_app_builtin "%ToBoolean" [ejs_to_ljs e]) 
            (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_assign e1 e2 e3 => 
        make_set_field (to_object (ejs_to_ljs e1)) (to_string (ejs_to_ljs e2)) (ejs_to_ljs e3)
    | E.expr_bracket e1 e2 => make_get_field (prop_accessor_check (ejs_to_ljs e1)) (to_string (ejs_to_ljs e2))
    | E.expr_for_in s e1 e2 => make_for_in s (ejs_to_ljs e1) (ejs_to_ljs e2) 
    | E.expr_label s e => L.expr_label s (ejs_to_ljs e)
    | E.expr_break s e => L.expr_break s (ejs_to_ljs e)
    | E.expr_throw e =>
        L.expr_throw (L.expr_object L.default_objattrs 
            [("%js-exn", L.property_data (L.data_intro (ejs_to_ljs e) L.expr_false L.expr_false L.expr_false))])
    | E.expr_try_finally e1 e2 =>  
        L.expr_try_finally (ejs_to_ljs e1) (ejs_to_ljs e2)
    | E.expr_with e1 e2 =>
        L.expr_let "%context" 
            (make_app_builtin "%makeWithContext" [context; ejs_to_ljs e1]) 
            (ejs_to_ljs e2)
    | E.expr_strict e => L.expr_let "#strict" L.expr_true (ejs_to_ljs e)
    | E.expr_nonstrict e => L.expr_let "#strict" L.expr_false (ejs_to_ljs e)
    | _ => L.expr_dump
    end.
