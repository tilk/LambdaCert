Require Import String.
Require Import Values.
Require Import Store.
Require Import Context.

Implicit Type runs : Context.runs_type.
Implicit Type st : Store.store.
Implicit Type e : Syntax.expr.
Implicit Type loc : value_loc.

(*
* The monadic constructors, which mostly take a store, some
* data, and a continuation; performing a test on the data; and calling
* the continuation in one case, and doing something else in other cases
* (either calling the continuation with a default, or returning a default,
* or returning the data verbatim).
*)

(* Evaluate an expression, and calls the continuation with
* the new store and the Context.result of the evaluation. *)
Definition eval_cont {A : Type} runs st e (cont : result -> resultof A) : resultof A :=
  cont (Context.runs_type_eval runs st e).

(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate runs st e : result :=
  eval_cont runs st e (fun res => res)
.

(* Calls the continuation if the variable is a value.
* Returns the variable and the store verbatim otherwise. *)
Definition if_result_some {A B : Type} (var : resultof A) (cont : A -> resultof B) : resultof B :=
  match var with
  | result_some v => cont v
  | result_fail s => result_fail s
  | result_impossible s => result_impossible s
  | result_bottom st => result_bottom st
  end
.

Definition if_out_ter {A : Type} (var : result) (cont : store -> res -> resultof A) : resultof A :=
  if_result_some var (fun o => 
    match o with
    | out_ter st r => cont st r 
    | _ => result_impossible "out_div found in interpreter"
    end)
.

Definition if_pout_ter {A : Type} (var : resultof pout) (cont : attributes -> resultof A) : resultof A :=
  if_result_some var (fun o => 
    match o with
    | pout_ter r => cont r 
    | _ => result_impossible "out_div found in interpreter"
    end)
.

Definition if_value  (var : result) (cont : store -> value_loc -> result) : result :=
  if_out_ter var (fun st r =>
    match r with
    | res_value v => cont st v
    | _ => result_some (out_ter st r)
    end)
.

(* Evaluates an expression, and calls the continuation if
* the evaluation finished successfully.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_ter {A : Type} runs st e (cont : store -> res -> resultof A) : resultof A :=
  eval_cont runs st e (fun res => if_out_ter res cont)
.

(* Evaluates an expression, and calls the continuation if
* the evaluation returned a value.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_return runs st e (cont : store -> value_loc -> result) : result :=
  eval_cont runs st e (fun res => if_value res cont)
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation with the default
* value if the expression is None. *)
Definition if_some_eval_else_default runs st (oe : option Syntax.expr) (default : value_loc) (cont : store -> value_loc -> result) : result :=
  match oe with
  | Some e => if_eval_return runs st e cont
  | None => cont st default
  end
.

(* Same as if_some_and_eval_value, but returns an option as the Context.result, and
* None is used as the default value passed to the continuation. *)
Definition if_some_eval_return_else_none runs st (oe : option Syntax.expr) (cont : store -> option value_loc -> result) : result :=
  match oe with
  | Some e => if_eval_return runs st e (fun ctx res => cont ctx (Some res))
  | None => cont st None
  end
.

(* Calls the continuation with the referenced value. Fails if the reference
* points to a non-existing object (never actually happens). *)
Definition assert_deref {A : Type} st (loc : value_loc) (cont : value -> resultof A) : resultof A :=
  match (Store.get_value st loc) with
  | Some val => cont val
  | None => result_impossible "Location of non-existing value."
  end
.

(* Calls the continuation if the value is a location to a value (always!), and passes the value to the continuation.
* Fails otherwise. *)
(* TODO erase *)
Definition assert_get {A : Type} st (loc : value_loc) (cont : value -> resultof A) : resultof A :=
  assert_deref st loc cont.

(* Calls the continuation if the value is an object pointer, and passes the pointer to the continuation.
* Fails otherwise. *)
Definition assert_get_object_ptr {A : Type} store (loc : value_loc) (cont : object_ptr -> resultof A) : resultof A :=
  match (Store.get_value store loc) with
  | Some (Values.Object ptr) => cont ptr
  | Some _ => result_fail "Expected an object pointer."
  | None => result_impossible "Location of non-existing value."
  end
.

Definition assert_get_object_from_ptr {A : Type} store (ptr : object_ptr) (cont : object -> resultof A) : resultof A :=
  match (Store.get_object store ptr) with
  | Some obj => cont obj
  | None => result_impossible "Pointer to a non-existing object."
  end
.

(* Calls the continuation if the value is an object pointer, and passes the object to the continuation *)
Definition assert_get_object {A : Type} store (loc : Values.value_loc) (cont : object -> resultof A) : resultof A :=
  assert_get_object_ptr store loc (fun ptr =>
    assert_get_object_from_ptr store ptr cont
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {A : Type} store (loc : value_loc) (cont : string -> resultof A) : resultof A :=
  match (Store.get_value store loc) with
  | Some (Values.String s) => cont s
  | Some _ => result_fail "Expected String but did not get one."
  | None => result_impossible "Location of non-existing value."
  end
.

(* Calls the continuation if the value is a boolean.
* Fails otherwise. *)
Definition assert_get_bool {A : Type} store (loc : value_loc) (cont : bool -> resultof A) : resultof A :=
  match (Store.get_value store loc) with
  | Some Values.True => cont true
  | Some Values.False => cont false
  | Some _ => result_fail "Expected True or False but got none of them."
  | None => result_fail "Location of non-existing value."
  end
.
