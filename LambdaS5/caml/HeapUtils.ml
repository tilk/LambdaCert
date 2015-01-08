open LibHeap
open LibReflect
open Batteries

module Heap = 
    struct
        type ('k, 'v) heap = ('k, 'v) Map.t

        let empty = Map.empty

        let to_list m = Map.bindings m
        
        let read _ m k = Map.find k m

        let read_option _ m k = try Some (Map.find k m) with Not_found -> None

        let write m k v = Map.add k v m

        let rem _ m k = Map.remove k m

        let indom_decidable _ m k = Map.mem k m
    end
