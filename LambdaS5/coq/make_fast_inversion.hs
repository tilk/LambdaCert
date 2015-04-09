#!/usr/bin/env runhaskell

import Data.List
import Control.Monad
import Control.Arrow
import Text.Regex.Posix

prefix = "Generalizable All Variables.\n\
         \Set Implicit Arguments.\n\
         \Require Import LjsShared.\n\
         \Require Import LjsSyntax. \n\
         \Require Import LjsPrettyInterm.\n\
         \Require Import LjsPrettyRulesIndexed.\n"

predicate_name = "red_exprh"
patterns = [
    ("empty", "expr_empty"), 
    ("null", "expr_null"),
    ("undefined", "expr_undefined"),
    ("string", "expr_string ?s"),
    ("bool", "expr_bool ?b"),
    ("number", "expr_number ?n"),
    ("many_1_nil", "expr_eval_many_1 nil ?vs ?E"),
    ("many_1_cons", "expr_eval_many_1 (cons ?e ?es) ?vs ?E"),
    ("many_2", "expr_eval_many_2 ?es ?o ?vs ?E"),
    ("op1", "expr_op1 ?op ?e"),
    ("op1_1", "expr_op1_1 ?op ?o"),
    ("op2", "expr_op2 ?op ?e1 ?e2")]

is_basic :: String -> Bool
is_basic s = not (s =~ "_[0-9]+(_abort)?$")

add_basic :: String -> String
add_basic s | is_basic (s =~ "^[a-z0-9_]+") = "expr_basic (" ++ s ++ ")"
            | otherwise  = s

vars_of :: String -> [String]
vars_of s = map (tail . head) $ s =~ "\\?[a-zA-Z0-9_']+"

no_qmarks :: String -> String
no_qmarks = filter (/= '?')

inv_hyp_name n = "inv_" ++ predicate_name ++ "_" ++ n

make_concl s = "red_exprh ?k ?c ?st (" ++ s ++ ") (out_ter ?st' ?r)"

make_inversion (n, p) = "Derive Inversion_clear " ++ inv_hyp_name n ++ " with (forall " ++ intercalate " " (vars_of c) ++ ",\n    " ++ no_qmarks c ++ ") Sort Prop.\n" 
    where c = make_concl p

make_case (n, p) = "    | " ++ c ++ " =>\n        inversion H using " ++ inv_hyp_name n ++ "\n"
    where c = make_concl (add_basic p)

main = do
    putStr prefix
    putStr $ concat $ map make_inversion patterns
    putStr $ "Tactic Notation \"invert\" \"keep\" \"" ++ predicate_name ++ "\" hyp(H) := \n    match type of H with\n"
    putStr $ concat $ map make_case patterns
    putStr $ "    end.\n"

