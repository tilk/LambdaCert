Require Import Values.
Require Import LibStream.

Module Heap := HeapUtils.Heap.

(* LambdaJS environment storage. *)

(* (The initial definitions of this file come from JSCert.) *)

Definition value_heap_type := Heap.heap value_loc value.
Definition object_heap_type := Heap.heap object_ptr object.

Record store := store_intro {
  object_heap : object_heap_type; (* simulates mutability of objects *)
  value_heap : value_heap_type; (* maps locations to values *)
  fresh_locations : stream nat 
}.

CoFixpoint all_locations (k:nat) : stream nat :=
  LibStream.stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat.

Definition object_heap_initial : Heap.heap object_ptr object :=
  Heap.empty.
Definition value_heap_initial : Heap.heap value_loc value :=
  Heap.empty.
Definition loc_heap_initial : Heap.heap id value_loc :=
  Heap.empty.

Definition create_store :=
  {| object_heap := object_heap_initial;
     value_heap := value_heap_initial;
     fresh_locations := dummy_fresh_locations |}.

Definition create_ctx :=
  {| loc_heap := loc_heap_initial |}.

Definition add_value (st : store) (val : value) : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap (loc ::: stream) =>
    (store_intro obj_heap (Heap.write val_heap loc val) stream, loc)
  end
.
Fixpoint add_values (st : store) (vals : list value) : store * list value_loc :=
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
Definition add_object (st : store) (obj : object) : (store * value) :=
  match st with
  | store_intro obj_heap val_heap (ptr ::: stream) =>
    ((store_intro
      (Heap.write obj_heap ptr obj)
      val_heap
      stream
    ), (value_object ptr))
  end
.
Definition add_closure (c : ctx) (st : store) args body : (store * value) :=
  match st with
  | store_intro obj_heap val_heap (id ::: stream) =>
    (store_intro obj_heap val_heap stream, value_closure id c args body)
  end
.
Definition add_value_at_location (st : store) (loc : value_loc) (val : value) : store :=
  (* TODO: Remove the old value from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap stream => (store_intro obj_heap (Heap.write val_heap loc val) stream)
  end
.
Definition add_named_location (c : ctx) (name : id) (loc : value_loc) : ctx :=
  match c with
  | ctx_intro loc_heap =>
    ctx_intro (Heap.write loc_heap name loc) 
  end
.
Definition add_named_value_loc (c : ctx) (st : store) (name : id) (val : value) : (ctx * store * value_loc) :=
  match c, st with
  | ctx_intro loc_heap, store_intro obj_heap val_heap (loc ::: stream) => 
    (ctx_intro (Heap.write loc_heap name loc), store_intro obj_heap (Heap.write val_heap loc val) stream, loc)
  end
.
Definition add_named_value (c : ctx) (st : store) (name : id) (val : value) : ctx * store := 
  match add_named_value_loc c st name val with (c', st', _) => (c', st') end
.
Definition update_object (st : store) (ptr : object_ptr) (new_obj : object) : store :=
  (* TODO: Remove the old object from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap stream => (store_intro (Heap.write obj_heap ptr new_obj) val_heap stream)
  end
.

Definition add_option_value st (oval : option value) : (store * option Values.value_loc) :=
  match oval with
  | Some val => let (st, loc) := add_value st val in (st, Some loc)
  | None => (st, None)
  end
.
Definition add_bool st (b : bool) : (store * Values.value_loc) :=
  add_value st (if b then value_true else value_false)
.
Definition get_object (st : store) (ptr : object_ptr) : option object :=
  Heap.read_option (object_heap st) ptr
.
Definition get_value (st : store) (loc : value_loc) : option value :=
  Heap.read_option (value_heap st) loc
.
Definition get_loc  (c : ctx) (name : id) : option value_loc :=
  Heap.read_option (loc_heap c) name
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name c store (name : Values.id) : option Values.value :=
  match get_loc c name with
  | Some loc => get_value store loc
  | None => None
  end
.

Definition num_objects (st : store) : nat :=
  length (Heap.to_list (object_heap st)).

Definition num_values (st : store) : nat :=
  length (Heap.to_list (value_heap st)).
