#!/usr/bin/env runhaskell

import Data.List
import Control.Monad
import Control.Arrow
import Text.Regex.Posix

prefix = "Generalizable All Variables.\n\
         \Set Implicit Arguments.\n\
         \Require Import Utils.\n\
         \Require Import LjsShared.\n\
         \Require Import LjsSyntax. \n\
         \Require Import LjsPrettyInterm.\n\
         \Require Import LjsPrettyRulesIndexed.\n\
         \Ltac red_exprh_hnf e := \n\
         \    match eval hnf in e with\n\
         \    | expr_basic ?e1 =>\n\
         \        let e1' := eval hnf in e1 in\n\
         \        constr:(expr_basic e1')\n\
         \    | ?e1 => constr:e1\n\
         \    end.\n"

predicate_name = "red_exprh"
patterns = [
    ("empty", "expr_empty"), 
    ("null", "expr_null"),
    ("undefined", "expr_undefined"),
    ("string", "expr_string ?s"),
    ("bool", "expr_bool ?b"),
    ("number", "expr_number ?n"),
    ("id", "expr_id ?i"),
    ("lambda", "expr_lambda ?args ?body"),
{-
    ("many_1_nil", "expr_eval_many_1 nil ?vs ?E"),
    ("many_1_cons", "expr_eval_many_1 (cons ?e ?es) ?vs ?E"),
-}
    ("many_1", "expr_eval_many_1 ?es ?vs ?E"),
    ("many_2", "expr_eval_many_2 ?es ?o ?vs ?E"),
    ("object", "expr_object ?oa ?ia ?a"),
    ("object_1", "expr_object_1 ?a ?ia ?oal"),
{-
    ("object_2_nil", "expr_object_2 ?obj nil"),
    ("object_2_cons", "expr_object_2 ?obj (cons ?oa ?oal)"),
-}
    ("object_2", "expr_object_2 ?a ?ia ?obj"),
    ("object_data_1", "expr_object_data_1 ?obj ?s ?E ?vs"),
    ("object_accessor_1", "expr_object_accessor_1 ?obj ?s ?E ?vs"),
    ("object_internal_1", "expr_object_internal_1 ?obj ?s ?E ?vs"),
    ("get_attr", "expr_get_attr ?pa ?e1 ?e2"),
    ("get_attr_1", "expr_get_attr_1 ?pa ?vs"),
    ("set_attr", "expr_set_attr ?pa ?e1 ?e2 ?e3"),
    ("set_attr_1", "expr_set_attr_1 ?pa ?vs"),
    ("get_obj_attr", "expr_get_obj_attr ?pa ?e1"),
    ("get_obj_attr_1", "expr_get_obj_attr_1 ?pa ?vs"),
    ("set_obj_attr", "expr_set_obj_attr ?pa ?e1 ?e2"),
    ("set_obj_attr_1", "expr_set_obj_attr_1 ?pa ?vs"),
    ("get_internal", "expr_get_internal ?s ?e1"),
    ("get_internal_1", "expr_get_internal_1 ?s ?vs"),
    ("set_internal", "expr_set_internal ?s ?e1 ?e2"),
    ("set_internal_1", "expr_set_internal_1 ?s ?vs"),
    ("get_field", "expr_get_field ?e1 ?e2"),
    ("get_field_1", "expr_get_field_1 ?vs"),
    ("get_field_2", "expr_get_field_2 ?ptr ?oattr"),
    ("set_field", "expr_set_field ?e1 ?e2 ?e3"),
    ("set_field_1", "expr_set_field_1 ?vs"),
    ("set_field_2", "expr_set_field_2 ?ptr ?obj ?oattr ?s ?v3"),
    ("delete_field", "expr_delete_field ?e1 ?e2"),
    ("delete_field_1", "expr_delete_field_1 ?vs"),
    ("delete_field_2", "expr_delete_field_2 ?ptr ?obj ?oattr ?s"),
    ("own_field_names", "expr_own_field_names ?e"),
    ("own_field_names_1", "expr_own_field_names_1 ?o"),
    ("op1", "expr_op1 ?op ?e"),
    ("op1_1", "expr_op1_1 ?op ?o"),
    ("op2", "expr_op2 ?op ?e1 ?e2"),
    ("op2_1", "expr_op2_1 ?op ?o ?e2"),
    ("op2_2", "expr_op2_2 ?op ?v1 ?o"),
    ("if", "expr_if ?e ?e1 ?e2"),
    ("if_1", "expr_if_1 ?o ?e1 ?e2"),
    ("app", "expr_app ?e ?el"),
    ("app_1", "expr_app_1 ?o ?el"),
    ("app_2", "expr_app_2 ?v ?vl"),
    ("seq", "expr_seq ?e1 ?e2"),
    ("seq_1", "expr_seq_1 ?o ?e2"),
    ("jseq", "expr_jseq ?e1 ?e2"),
    ("jseq_1", "expr_jseq_1 ?o ?e2"),
    ("jseq_2", "expr_jseq_2 ?v1 ?o"),
    ("let", "expr_let ?i ?e1 ?e2"),
    ("let_1", "expr_let_1 ?i ?o ?e2"),
    ("rec", "expr_recc ?i ?e1 ?e2"),
    ("label", "expr_label ?i ?e"),
    ("label_1", "expr_label_1 ?i ?o"),
    ("break", "expr_break ?i ?e"),
    ("break_1", "expr_break_1 ?i ?o"),
    ("try_catch", "expr_try_catch ?e1 ?e2"),
    ("try_catch_1", "expr_try_catch_1 ?o ?e2"),
    ("try_catch_2", "expr_try_catch_2 ?v1 ?o"),
    ("try_finally", "expr_try_finally ?e1 ?e2"),
    ("try_finally_1", "expr_try_finally_1 ?o ?e2"),
    ("try_finally_2", "expr_try_finally_2 ?r' ?o"),
    ("throw", "expr_throw ?e"),
    ("throw_1", "expr_throw_1 ?o"),
    ("eval", "expr_eval ?e1 ?e2"),
    ("eval_1", "expr_eval_1 ?vs"),
    ("hint", "expr_hint ?s ?e"),
    ("fail", "expr_fail ?s"),
    ("dump", "expr_dump")]

is_basic :: String -> Bool
is_basic s = not (s =~ "_[0-9]+$")

add_basic :: String -> String
add_basic s | is_basic (s =~ "^[a-z0-9_]+") = "expr_basic (" ++ s ++ ")"
            | otherwise  = s

vars_of :: String -> [String]
vars_of s = map (tail . head) $ s =~ "\\?[a-zA-Z0-9_']+"

no_qmarks :: String -> String
no_qmarks = filter (/= '?')

inv_hyp_name n = "inv_" ++ predicate_name ++ "_" ++ n

make_concl s = "red_exprh ?k ?c ?st (" ++ s ++ ") ?oo"

make_inversion (n, p) = "Derive Inversion " ++ inv_hyp_name n ++ " with (forall " ++ intercalate " " (vars_of c) ++ ",\n    " ++ no_qmarks c ++ ") Sort Prop.\n" 
    where c = make_concl p

make_case (n, p) = "    | " ++ add_basic p ++ " =>\n        inversion H using " ++ inv_hyp_name n ++ "\n"

add_text = "\
         \    let eh := red_exprh_hnf e in\n\
         \    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); \n\
         \    match eh with\n"

main = do
    putStr prefix
    putStr $ concat $ map make_inversion patterns
    putStr $ "Tactic Notation \"invert\" \"keep\" \"" ++ predicate_name ++ "\" hyp(H) := \n    match type of H with\n    | " ++ make_concl "?e" ++ " => \n" ++ add_text
    putStr $ concat $ map make_case patterns
    putStr $ "    end end; tryfalse; clear H; intro H.\n"
    putStr $ "Tactic Notation \"inverts\" \"keep\" \"" ++ predicate_name ++ "\" hyp(H) := \n    inverts_tactic_general ltac:(fun H => invert keep " ++ predicate_name ++ " H) H; tryfalse.\n"
    putStr $ "Tactic Notation \"inverts\" \"" ++ predicate_name ++ "\" hyp(H) := \n    inverts keep " ++ predicate_name ++ " H; clear H.\n"

