open Batteries
open LjsSyntax

module StringSet = Set.Make(String)

let rec string_of_value depth st = function
| Coq_value_empty -> "empty"
| Coq_value_null -> "null"
| Coq_value_undefined -> "undefined"
| Coq_value_number f -> String.of_list (JsNumber.to_string f)
| Coq_value_string s -> "\"" ^ (String.of_list s) ^ "\""
| Coq_value_bool true -> "true"
| Coq_value_bool false -> "false"
| Coq_value_object ptr -> string_of_object_ptr depth st ptr
| Coq_value_closure (Coq_closure_intro (loc_heap, _, args, body)) ->
    Printf.sprintf "<closure func (%s) { %s }>"
      (String.concat ", " (List.map String.of_list args))
      (string_of_expression depth body)
and string_of_value_option depth st = function
| Some v -> string_of_value depth st v
| None -> "<unset val>"

and string_of_object_ptr depth st ptr =
  if depth = 0 then "<cut>" else
  match LibFinmap.read_option_inst st ptr with
    | None -> "<reference to non-existing object>"
    | Some obj -> string_of_object (depth-1) st obj
and string_of_object depth (st : store) obj =
  Printf.sprintf "{[#proto: %s, #class: %s, #extensible: %B, #code: %s%s] %s}"
  (string_of_value depth st (object_proto obj)) (String.of_list (object_class obj))
  (object_extensible obj) (string_of_value depth st (object_code obj))
  (string_of_internal_list depth st (LibFinmap.FinmapImpl.to_list_impl (object_internal obj)))
  (string_of_prop_list depth st (LibFinmap.FinmapImpl.to_list_impl (object_properties obj)) [])
and string_of_internal_list depth st l =
  let string_of_internal = function (name, v) ->
    Printf.sprintf ", %s: %s" (String.of_list name) (string_of_value depth st v)
  in String.concat "" (List.map string_of_internal l)
and string_of_prop_list depth st l skip =
  let string_of_prop = function (name, attr) ->
    Printf.sprintf "'%s': %s" (String.of_list name) (string_of_attr depth st attr)
  in String.concat ", " (List.map string_of_prop l)

and string_of_expression depth e =
  "<expr>"
and string_of_expression_option depth = function
| Some e -> string_of_expression depth e
| None -> "<unset expr>"

and string_of_attr depth st = function
| Coq_attributes_data_of d -> attributes_data_rect (fun v w e c -> Printf.sprintf "{#value %s, #writable %B, #configurable %B, #enumerable %B}" (string_of_value depth st v) w c e) d
| Coq_attributes_accessor_of d -> attributes_accessor_rect (fun g s e c -> Printf.sprintf "{#getter %s, #setter %s, #configurable %B, #enumerable %B}" (string_of_value depth st g) (string_of_value depth st s) c e) d (* enumerable and configurable ignored *)

let string_of_store depth c st =
  let locs = LibFinmap.FinmapImpl.to_list_impl c in
  let pred = string_of_value depth st in
  String.concat "" (List.map (fun (k, v) -> Printf.sprintf "let (%s = %s) \n" (String.of_list k) (pred v)) locs)

