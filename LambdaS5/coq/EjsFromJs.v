Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require LjsSyntax.
Require EjsSyntax.
Require JsSyntax JsSyntaxInfos.
Require JsPreliminary.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Local Coercion JsNumber.of_int : Z >-> JsNumber.number.

Module Import EjsFromJsHelper.
Module E := EjsSyntax.
Module J := JsSyntax.
Module JI := JsPreliminary.
End EjsFromJsHelper.

Fixpoint js_literal_to_ejs l := 
    match l with
    | J.literal_null => E.expr_null
    | J.literal_bool true => E.expr_true
    | J.literal_bool false => E.expr_false
    | J.literal_number n => E.expr_number n
    | J.literal_string s => E.expr_string s
    end.

Definition js_expr_assign_to_ejs e1 oop e2 :=
    let aop e := 
        match oop with
        | None => e
        | Some op => E.expr_op2 op e1 e
        end in
    match e1 with
    | E.expr_var_id s => E.expr_var_set s (aop e2)
    | E.expr_get_field e1' e1'' => E.expr_set_field e1' e1'' (aop e2)
    | _ => E.expr_syntaxerror
    end.

Definition is_strict es := 
    match es with
    | J.element_stat (J.stat_expr (J.expr_literal (J.literal_string "use strict"))) :: _ => true
    | _ => false
    end.

Definition is_element_stat e := match e with J.element_stat _ => true | _ => false end.
Definition is_element_func_decl e := match e with J.element_func_decl _ _ _ => true | _ => false end.

Definition js_label_to_ejs s l := s ++
    match l with
    | J.label_empty => ""
    | J.label_string s' => "_" ++ s'
    end.

Definition js_label_set_to_labels s (ls : J.label_set) e := 
    fold_right E.expr_label e (map (js_label_to_ejs s) ls).

Fixpoint js_expr_to_ejs (e : J.expr) : E.expr := 
    match e with
    | J.expr_this => E.expr_this
    | J.expr_identifier i => E.expr_var_id i
    | J.expr_literal l => js_literal_to_ejs l
    | J.expr_member e s => E.expr_get_field (js_expr_to_ejs e) (E.expr_string s) 
    | J.expr_access e1 e2 => E.expr_get_field (js_expr_to_ejs e1) (js_expr_to_ejs e2)
    | J.expr_unary_op o e => E.expr_op1 o (js_expr_to_ejs e) 
    | J.expr_binary_op e1 o e2 => E.expr_op2 o (js_expr_to_ejs e1) (js_expr_to_ejs e2)
    | J.expr_conditional e1 e2 e3 => E.expr_if (js_expr_to_ejs e1) (js_expr_to_ejs e2) (js_expr_to_ejs e3)
    | J.expr_assign e1 oo e2 => js_expr_assign_to_ejs (js_expr_to_ejs e1) oo (js_expr_to_ejs e2)
    | J.expr_new e es => E.expr_new (js_expr_to_ejs e) (List.map js_expr_to_ejs es)
    | J.expr_call e es => E.expr_app (js_expr_to_ejs e) (List.map js_expr_to_ejs es)
    | J.expr_function onm xs (J.funcbody_intro p _) => E.expr_func onm xs (js_prog_to_ejs p)
    | J.expr_object ps => 
        E.expr_object (List.map (fun (pp : J.propname * J.propbody) => let (pn, p) := pp in (JI.string_of_propname pn, js_prop_to_ejs p)) ps) 
    end
with js_prop_to_ejs p :=
    match p with
    | J.propbody_val e => E.property_data (js_expr_to_ejs e)
    | J.propbody_get (J.funcbody_intro p _) => E.property_getter (E.expr_func None nil (js_prog_to_ejs p))
    | J.propbody_set is (J.funcbody_intro p _) => E.property_setter (E.expr_func None is (js_prog_to_ejs p))
    end
with js_stat_to_ejs (e : J.stat) : E.expr := 
    let js_vardecl_to_ejs vd := 
        let '(s, oe) := vd in 
        match oe with
        | None => E.expr_undefined
        | Some e => E.expr_var_set s (js_expr_to_ejs e)
        end in
    match e with
    | J.stat_expr e => E.expr_noop (js_expr_to_ejs e)
    | J.stat_label s st => E.expr_label (js_label_to_ejs "%break" (J.label_string s)) (js_stat_to_ejs st)
    | J.stat_block sts => E.expr_seqs (List.map js_stat_to_ejs sts)
    | J.stat_var_decl l => E.expr_fseq (E.expr_seqs (List.map js_vardecl_to_ejs l)) E.expr_empty
    | J.stat_if e st None => E.expr_if (js_expr_to_ejs e) (js_stat_to_ejs st) E.expr_empty
    | J.stat_if e st (Some st') => E.expr_if (js_expr_to_ejs e) (js_stat_to_ejs st) (js_stat_to_ejs st')
    | J.stat_do_while ls st e => 
        js_label_set_to_labels "%break" ls
            (E.expr_do_while (js_label_set_to_labels "%continue" ls (js_stat_to_ejs st)) (js_expr_to_ejs e)) 
    | J.stat_while ls e st => 
        js_label_set_to_labels "%break" ls
            (E.expr_while (js_expr_to_ejs e)
                (js_label_set_to_labels "%continue" ls (js_stat_to_ejs st)) E.expr_undefined)
    | J.stat_with e st => E.expr_with (js_expr_to_ejs e) (js_stat_to_ejs st)
    | J.stat_throw e => E.expr_throw (js_expr_to_ejs e)
    | J.stat_return oe =>
        let e := match oe with
        | None => E.expr_undefined
        | Some e => js_expr_to_ejs e
        end in 
        E.expr_break "%ret" e 
    | J.stat_break lbl =>
        E.expr_break (js_label_to_ejs "%break" lbl) E.expr_empty
    | J.stat_continue lbl =>
        E.expr_break (js_label_to_ejs "%continue" lbl) E.expr_empty
    | J.stat_try st None None => E.expr_noop (js_stat_to_ejs st)
    | J.stat_try st (Some (s, st1)) None => E.expr_try_catch (js_stat_to_ejs st) s (js_stat_to_ejs st1)
    | J.stat_try st None (Some st2) => E.expr_try_finally (js_stat_to_ejs st) (js_stat_to_ejs st2)
    | J.stat_try st (Some (s, st1)) (Some st2) => 
        E.expr_try_finally (E.expr_try_catch (js_stat_to_ejs st) s (js_stat_to_ejs st1)) (js_stat_to_ejs st2)
    | J.stat_for ls oe1 oe2 oe3 st => 
        let e1 := match oe1 with
        | None => E.expr_undefined
        | Some e => js_expr_to_ejs e
        end in
        let e2 := match oe2 with
        | None => E.expr_true
        | Some e => js_expr_to_ejs e
        end in 
        let e3 := match oe3 with
        | None => E.expr_undefined
        | Some e => js_expr_to_ejs e
        end in 
        E.expr_seq e1 (js_label_set_to_labels "%break" ls 
            (E.expr_while e2 (js_label_set_to_labels "%continue" ls (js_stat_to_ejs st)) e3))
    | J.stat_for_var ls le1 oe2 oe3 st =>
        let e2 := match oe2 with
        | None => E.expr_true
        | Some e => js_expr_to_ejs e
        end in 
        let e3 := match oe3 with
        | None => E.expr_undefined
        | Some e => js_expr_to_ejs e
        end in
        E.expr_seq (E.expr_seqs (List.map js_vardecl_to_ejs le1)) 
            (js_label_set_to_labels "%break" ls 
                (E.expr_while e2 (js_label_set_to_labels "%continue" ls (js_stat_to_ejs st)) e3))
(* TODO for-in
    | J.stat_for_in nil lval e st => 
        E.expr_label "%break" (E.expr_for_in s (js_expr_to_ejs e) (js_stat_to_ejs st))
*)
    | J.stat_switch ls e (J.switchbody_nodefault cl) => 
        js_label_set_to_labels "%break" ls (
        E.expr_switch (js_expr_to_ejs e) (E.switchbody_nodefault (List.map js_switchclause_to_ejs cl)))
    | J.stat_switch ls e (J.switchbody_withdefault cl1 sts cl2) =>
        js_label_set_to_labels "%break" ls ( 
        E.expr_switch (js_expr_to_ejs e) (E.switchbody_withdefault
            (List.map js_switchclause_to_ejs cl1)
            (E.expr_seqs (List.map js_stat_to_ejs sts))
            (List.map js_switchclause_to_ejs cl2)))
    | J.stat_debugger => E.expr_empty
    | _ => E.expr_syntaxerror
    end
with js_switchclause_to_ejs c := 
    match c with
    | J.switchclause_intro e sts => (js_expr_to_ejs e, E.expr_seqs (List.map js_stat_to_ejs sts))
    end 
with js_element_to_ejs (e : J.element) : E.expr := 
    match e with
    | J.element_stat st => js_stat_to_ejs st
    | J.element_func_decl s ps (J.funcbody_intro p _) => 
(* TODO reconsider implementation strategy *)
        E.expr_func_stmt s ps (js_prog_to_ejs p)
    end
with js_prog_to_ejs p : E.prog :=
    let js_elements_to_ejs (es : list J.element) : E.expr :=
        let filtmap_js_element_to_ejs p := fix f l :=
            match l with nil => nil | e :: es => if p e then js_element_to_ejs e :: f es else f es end in
        E.expr_seqs (filtmap_js_element_to_ejs is_element_func_decl es ++ 
            filtmap_js_element_to_ejs is_element_stat es) in
    match p with
    | J.prog_intro _ sts => E.prog_intro (is_strict sts) (JI.prog_vardecl p) (js_elements_to_ejs sts)
    end.

Require EjsToLjs.

Parameter parse_js_expr : string -> option JsSyntax.prog.
Definition desugar_expr s := LibOption.map (fun e => EjsToLjs.ejs_prog_to_ljs (js_prog_to_ejs 
    (JsSyntaxInfos.add_infos_prog J.strictness_false e))) (parse_js_expr s).

