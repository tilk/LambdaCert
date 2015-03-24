Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntaxAux.
Require Import String.
Require Import LibStream.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

(* LambdaJS environment storage. *)
Definition add_object st obj : (store * value) := 
  let ptr := fresh st in (st \(fresh st := obj), value_object ptr).

Definition add_closure c recid args body : value :=
  let si := match recid with 
    | Some i => expr_fv (expr_lambda args body) \-- i
    | None => expr_fv (expr_lambda args body) 
    end in
  value_closure (closure_intro (to_list (c \| si)) recid args body)
.

(* Adds function arguments to the lexical environment *)

Definition add_parameters (closure_env : ctx) (args_name : list id) (args : list value) : resultof ctx :=
  match Utils.zip args_name args with
  | Some args_heap => result_some (from_list args_heap \u closure_env)
  | None => result_fail "Arity mismatch"
  end
.

Definition closure_ctx clo args :=
  let 'closure_intro c rid args_name _ := clo in
  let c' := match rid with
    | Some i => from_list c \( i := value_closure clo)
    | None => from_list c
    end in
  add_parameters c' args_name args.

Definition ctx_of_obj_aux (o : option ctx) (p : string * attributes) : option ctx  :=
  match o with
  | Some c => 
    let (s, a) := p in
    match a with
    | attributes_data_of data => Some (c \(s := attributes_data_value data))
    | attributes_accessor_of _ => None
    end
  | None => None
  end 
.

Definition ctx_of_obj obj : option ctx :=
  List.fold_left ctx_of_obj_aux (to_list (object_properties obj)) (Some create_ctx)
.
