Require Import LjsShared.
Require Import LjsValues.
Require Import LjsSyntax.
Require Import LjsStore.

Open Scope container_scope.

Implicit Type st : store.
Implicit Type c : ctx.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type i : id.

(*
* The monadic constructors, which mostly take a store, some
* data, and a continuation; performing a test on the data; and calling
* the continuation in one case, and doing something else in other cases
* (either calling the continuation with a default, or returning a default,
* or returning the data verbatim).
*)

(* Calls the continuation if the variable is a value.
* Returns the variable and the store verbatim otherwise. *)
Definition if_result_some {A B : Type} (var : resultof A) (cont : A -> resultof B) : resultof B :=
  match var with
  | result_some v => cont v
  | result_fail s => result_fail s
  | result_impossible s => result_impossible s
  | result_bottom => result_bottom
  | result_dump c st => result_dump c st
  end
.

Definition if_out_ter (var : result) (cont : store -> res -> result) : result :=
  if_result_some var (fun o => 
    match o with
    | out_ter st r => cont st r 
    | out_div => result_some out_div
    end)
.

Definition if_value  (var : result) (cont : store -> value -> result) : result :=
  if_out_ter var (fun st r =>
    match r with
    | res_value v => cont st v
    | _ => result_some (out_ter st r)
    end)
.

Definition assert_deref {A : Type} c i (cont : value -> resultof A) : resultof A :=
  match c \(i?) with
  | Some v => cont v
  | None => result_fail ("ReferenceError: " ++ i)
  end
.

Definition assert_some {A B : Type} (x : option A) (cont : A -> resultof B) : resultof B :=
  match x with 
  | Some a => cont a
  | None => result_fail "Expected Some."
  end
.

(* Calls the continuation if the value is an object pointer, and passes the pointer to the continuation.
* Fails otherwise. *)
Definition assert_get_object_ptr {A : Type} v (cont : object_ptr -> resultof A) : resultof A :=
  match v with
  | value_object ptr => cont ptr
  | _ => result_fail "Expected an object pointer."
  end
.

Definition assert_get_object_from_ptr {A : Type} store (ptr : object_ptr) (cont : object -> resultof A) : resultof A :=
  match store \(ptr?) with
  | Some obj => cont obj
  | None => result_impossible "Pointer to a non-existing object."
  end
.

(* Calls the continuation if the value is an object pointer, and passes the object to the continuation *)
Definition assert_get_object {A : Type} store (loc : value) (cont : object -> resultof A) : resultof A :=
  assert_get_object_ptr loc (fun ptr =>
    assert_get_object_from_ptr store ptr cont
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {A : Type} (loc : value) (cont : string -> resultof A) : resultof A :=
  match loc with
  | value_string s => cont s
  | _ => result_fail "Expected String but did not get one."
  end
.

(* Calls the continuation if the value is a boolean.
* Fails otherwise. *)
Definition assert_get_bool {A : Type} (loc : value) (cont : bool -> resultof A) : resultof A :=
  match loc with
  | value_bool b => cont b
  | _ => result_fail "Expected True or False but got none of them."
  end
.
