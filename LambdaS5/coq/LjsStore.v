Require Import LjsSyntax.
Require Import String.
Require Import LibStream.

Implicit Type st : store.
Implicit Type e : expr.
Implicit Type v : value.
Implicit Type loc : value_loc.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

(* LambdaJS environment storage. *)

Definition add_value st v : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap (loc ::: stream) =>
    (store_intro obj_heap (Heap.write val_heap loc v) stream, loc)
  end
.
Fixpoint add_values st (vals : list value) : store * list value_loc :=
  match vals with
  | nil => (st, nil)
  | val :: vals => 
    match add_value st val with
    | (st', loc) => 
      match add_values st' vals with
      | (st'', locs) => (st'', loc :: locs)
      end
    end
  end
.
Definition add_object st obj : (store * value) :=
  match st with
  | store_intro obj_heap val_heap (ptr ::: stream) =>
    ((store_intro
      (Heap.write obj_heap ptr obj)
      val_heap
      stream
    ), (value_object ptr))
  end
.
Definition add_closure c st args body : (store * value) :=
  match st with
  | store_intro obj_heap val_heap (id ::: stream) =>
    (store_intro obj_heap val_heap stream, value_closure id c args body)
  end
.
Definition add_value_at_location st loc v : store :=
  (* TODO: Remove the old value from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap stream => (store_intro obj_heap (Heap.write val_heap loc v) stream)
  end
.
Definition add_named_location c i loc : ctx :=
  match c with
  | ctx_intro loc_heap =>
    ctx_intro (Heap.write loc_heap i loc) 
  end
.
Definition add_named_value_loc c st i v : (ctx * store * value_loc) :=
  match c, st with
  | ctx_intro loc_heap, store_intro obj_heap val_heap (loc ::: stream) => 
    (ctx_intro (Heap.write loc_heap i loc), store_intro obj_heap (Heap.write val_heap loc v) stream, loc)
  end
.
Definition add_named_value c st i v : ctx * store := 
  match add_named_value_loc c st i v with (c', st', _) => (c', st') end
.
Definition update_object st ptr obj : store :=
  (* TODO: Remove the old object from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap stream => (store_intro (Heap.write obj_heap ptr obj) val_heap stream)
  end
.

Definition add_option_value st (oval : option value) : (store * option value_loc) :=
  match oval with
  | Some val => let (st, loc) := add_value st val in (st, Some loc)
  | None => (st, None)
  end
.
Definition add_bool st (b : bool) : (store * value_loc) :=
  add_value st (if b then value_true else value_false)
.
Definition get_object st ptr : option object :=
  Heap.read_option (object_heap st) ptr
.
Definition get_value st loc : option value :=
  Heap.read_option (value_heap st) loc
.
Definition get_loc c i : option value_loc :=
  Heap.read_option (loc_heap c) i
.
Definition object_binds st ptr obj :=
  Heap.binds (object_heap st) ptr obj
.
Definition value_binds st loc v :=
  Heap.binds (value_heap st) loc v
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name c store (name : id) : option value :=
  match get_loc c name with
  | Some loc => get_value store loc
  | None => None
  end
.

Definition num_objects st : nat :=
  List.length (Heap.to_list (object_heap st)).

Definition num_values st : nat :=
  List.length (Heap.to_list (value_heap st)).

Definition envstore_of_obj_aux (o : option (ctx * store)) (p : string * attributes) : option (ctx * store) :=
  match o with
  | Some (c, st) => 
    let (s, a) := p in
    match a with
    | attributes_data_of data => Some (add_named_value c st s (attributes_data_value data))
    | attributes_accessor_of _ => None
    end
  | None => None
  end 
.

Definition envstore_of_obj st obj : option (ctx * store) :=
  List.fold_left envstore_of_obj_aux (Heap.to_list (object_properties_ obj)) (Some (create_ctx, st))
.
