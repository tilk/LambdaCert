Set Implicit Arguments.
Require Import Utils.
Require Import String.
Require Import Values.
Require Import Store.

(* Utilities for the Interpreter. *)

Inductive res := 
| res_value : value -> res
| res_exception : value -> res
| res_break : string -> value -> res
.

Inductive out :=
| out_div : out
| out_ter : store -> res -> out.

Inductive pout :=
| pout_div : pout
| pout_ter : attributes -> pout.

(* Used for passing data through continuations/return values.
* It is mostly used for returning a Javascript value, either as
* Return or Exception, but sometimes we want to return another kind
* of result, which is the reason why this type is parametered by
* value_type. *)
Inductive resultof (T : Type) : Type :=
| result_some : T -> resultof T
| result_fail : string -> resultof T
| result_impossible : string -> resultof T
| result_bottom : store -> resultof T
.
Implicit Arguments result_some [[T]].
Implicit Arguments result_fail [[T]].
Implicit Arguments result_impossible [[T]].
Implicit Arguments result_bottom [[T]].

Definition result := resultof out.

Record runs_type : Type := runs_type_intro {
    runs_type_eval : Store.store -> Syntax.expr -> result;
    runs_type_get_closure : Store.store -> Values.value -> result;
    runs_type_get_property : Store.store -> (Values.value * Values.prop_name) -> resultof (option Values.attributes)
}.

Definition result_value st (v : value) : result := result_some (out_ter st (res_value v)).
Definition result_exception st (v : value) : result := result_some (out_ter st (res_exception v)).
Definition result_break st (l : string) (v : value) : result := result_some (out_ter st (res_break l v)).

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception store (name : string) : result :=
  match (Store.add_object store (Values.object_intro Undefined name true None Heap.empty None)) with
  | (new_st, loc) => result_exception new_st loc
  end
.

(* Unpacks a store to get an object, calls the predicate with this
* object, and updates the object to the returned value. *)
Definition update_object_cont (st : store) (ptr : Values.object_ptr) (cont : Values.object -> (store -> object -> value -> result) -> result) : result :=
  match (Store.get_object st ptr) with
  | Some obj =>
      cont obj (fun st new_obj ret =>
        result_some (out_ter (Store.update_object st ptr new_obj) (res_value ret))
      )
  | None => result_impossible "Pointer to a non-existing object."
  end
.

Definition update_object (st : store) (ptr : Values.object_ptr) (pred : Values.object -> (store * object * value)) : result :=
  update_object_cont st ptr (fun obj cont => match pred obj with (st, new_obj, ret) => cont st new_obj ret end)
.

(* Fetches the object pointed by the ptr, gets the property associated
* with the name and passes it to the predicate (as an option).
* If the predicate returns None as the now property, the property is
* destroyed; otherwise it is updated/created with the one returned by
* the predicate. *)
Definition update_object_property_cont st (ptr : Values.object_ptr) (name : Values.prop_name) (cont : option Values.attributes -> (store -> option attributes -> value -> result) -> result) : result :=
  update_object_cont st ptr (fun obj cont1 =>
    match obj with (Values.object_intro prot cl ext prim props code) =>
      cont (Values.get_object_property obj name) (fun st oprop res => match oprop with
        | Some prop =>
          let new_props := (Heap.write props name prop) in
          cont1 st (Values.object_intro prot cl ext prim new_props code) res
        | None =>
          let new_props := props in
          (* TODO: Remove property *)
          cont1 st (Values.object_intro prot cl ext prim new_props code) res
      end)
    end
  )
.

Definition update_object_property st (ptr : Values.object_ptr) (name : Values.prop_name) (pred : option Values.attributes -> (store * option attributes * value)) : result :=
  update_object_property_cont st ptr name (fun attrs cont => match pred attrs with (st, oattrs, ret) => cont st oattrs ret end)
.

Definition return_bool store (b : bool) :=
  result_value store (if b then Values.True else Values.False)
.
