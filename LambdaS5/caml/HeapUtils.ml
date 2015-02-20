open LibHeap
open LibReflect
open Batteries

module type MyHeapSpec = 
 sig 
  type ('x0, 'x) heap 
  
  val empty : ('a1, 'a2) heap
  
  val write : ('a1, 'a2) heap -> 'a1 -> 'a2 -> ('a1, 'a2) heap
  
  val to_list : ('a1, 'a2) heap -> ('a1 * 'a2) list
  
  val read : 'a1 coq_Comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2
  
  val read_option :
    'a1 coq_Comparable -> ('a1, 'a2) heap -> 'a1 -> 'a2 option
  
  val rem : 'a1 coq_Comparable -> ('a1, 'a2) heap -> 'a1 -> ('a1, 'a2) heap
  
  val indom_decidable :
    'a1 coq_Comparable -> ('a1, 'a2) heap -> 'a1 -> coq_Decidable
  
  val of_list : ('a1 * 'a2) list -> ('a1, 'a2) heap
 end


module Heap = 
    struct
        type ('k, 'v) heap = ('k, 'v) Map.t

        let empty = Map.empty

        let to_list m = Map.bindings m

        let of_list l = Map.of_enum (List.enum l)
        
        let read _ m k = Map.find k m

        let read_option _ m k = try Some (Map.find k m) with Not_found -> None

        let write m k v = Map.add k v m

        let rem _ m k = Map.remove k m

        let indom_decidable _ m k = Map.mem k m
    end
