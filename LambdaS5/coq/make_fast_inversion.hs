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
{- TODO?
    ("many_1_nil", "expr_eval_many_1 nil ?vs ?E"),
    ("many_1_cons", "expr_eval_many_1 (cons ?e ?es) ?vs ?E"),
-}
    ("many_1", "expr_eval_many_1 ?es ?vs ?E"),
    ("many_2", "expr_eval_many_2 ?es ?o ?vs ?E"),
    ("object", "expr_object ?oa ?a"),
    ("object_1", "expr_object_1 ?a ?oal"),
    ("object_2", "expr_object_2 ?obj ?a"),
    ("object_data_1", "expr_object_data_1 ?obj ?a ?s ?vs"),
    ("object_accessor_1", "expr_object_accessor_1 ?obj ?a ?s ?vs"),
    ("op1", "expr_op1 ?op ?e"),
    ("op1_1", "expr_op1_1 ?op ?o"),
    ("op2", "expr_op2 ?op ?e1 ?e2"),
    ("op2_1", "expr_op2 ?op ?o ?e2"),
    ("op2_2", "expr_op2 ?op ?v1 ?o"),
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
    ("throw_1", "expr_throw_1 ?o")]

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

main = do
    putStr prefix
    putStr $ concat $ map make_inversion patterns
    putStr $ "Tactic Notation \"invert\" \"keep\" \"" ++ predicate_name ++ "\" hyp(H) := \n    match type of H with\n    | " ++ make_concl "?e" ++ " => match red_exprh_hnf e with\n"
    putStr $ concat $ map make_case patterns
    putStr $ "    end end; clear H; intro H.\n"
    putStr $ "Tactic Notation \"inverts\" \"keep\" \"" ++ predicate_name ++ "\" hyp(H) := \n    inverts_tactic_general ltac:(fun H => invert keep " ++ predicate_name ++ " H) H.\n"
    putStr $ "Tactic Notation \"inverts\" \"" ++ predicate_name ++ "\" hyp(H) := \n    inverts keep " ++ predicate_name ++ " H; clear H.\n"

