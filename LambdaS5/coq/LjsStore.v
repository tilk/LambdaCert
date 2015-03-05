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
Definition narrow_ctx c s := 
  List.fold_left (fun cc (i : string) => cc \( i := c \( i ))) (LibFinset.to_list s) \{}.

Definition add_object st obj : (store * value) :=
  match st with
  | store_intro obj_heap (ptr ::: stream) =>
    ((store_intro
      (obj_heap \( ptr := obj))
      stream
    ), (value_object ptr))
  end
.
Definition add_closure c recid args body : value :=
  let si := match recid with 
    | Some i => expr_fv (expr_lambda args body) \-- i
    | None => expr_fv (expr_lambda args body) 
    end in
  value_closure (closure_intro (FinmapImpl.to_list (narrow_ctx c si)) recid args body)
.

(* Adds function arguments to the lexical environment *)

Definition add_parameters (closure_env : ctx) (args_name : list id) (args : list value) : resultof ctx :=
  match Utils.zip_left args_name args with
  | Some args_heap => result_some (Utils.concat_list_heap args_heap closure_env)
  | None => result_fail "Arity mismatch"
  end
.

Definition closure_ctx clo args :=
  let 'closure_intro c rid args_name _ := clo in
  let c' := fold_left (fun (p : string * value) h => let (s, v) := p in h \( s := v )) \{} c in
  let c'' := match rid with
    | Some i => c' \( i := value_closure clo)
    | None => c'
    end in
  add_parameters c'' args_name args.

Definition update_object st ptr obj : store :=
  (* TODO: Remove the old object from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap stream => (store_intro (obj_heap \( ptr := obj)) stream)
  end
.

Definition get_object st ptr : option object :=
  object_heap st \( ptr ?)
.

Definition num_objects st : nat :=
  List.length (FinmapImpl.to_list (object_heap st)).

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
  List.fold_left ctx_of_obj_aux (FinmapImpl.to_list (object_properties obj)) (Some create_ctx)
.

(* predicates for store lookup *)

Definition object_binds st ptr obj :=
    binds (object_heap st) ptr obj.

Definition object_indom st ptr :=
    ptr \in object_heap st.

