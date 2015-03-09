Generalizable All Variables.
Set Implicit Arguments.
Require Import LjsShared.
Require Import JsNumber.
Require Import Utils.
Require Import LjsSyntax.
Require Import LjsPrettyInterm LjsPrettyRules LjsPrettyRulesIndexed.
Require Import LjsCompleteness.

Implicit Type A B : Type.
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
