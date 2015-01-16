open Batteries

module StringSet = Set.Make(String)

let rec string_of_value_loc depth st loc =
  if (depth = 0) then
    "<cut>"
  else
    match (Store.get_value st loc) with
      | None -> "<reference to non-existing value>"
      | Some v -> string_of_value (depth-1) st v
and string_of_value depth st = function
| Values.Coq_value_null -> "null"
| Values.Coq_value_undefined -> "undefined"
| Values.Coq_value_number f -> String.of_list (JsNumber.to_string f)
| Values.Coq_value_string s -> "\"" ^ (String.of_list s) ^ "\""
| Values.Coq_value_true -> "true"
| Values.Coq_value_false -> "false"
| Values.Coq_value_object ptr -> string_of_object_ptr depth st ptr
| Values.Coq_value_closure (_, loc_heap, args, body) ->
    Printf.sprintf "<closure func (%s) { %s }>"
      (String.concat ", " (List.map String.of_list args))
      (string_of_expression depth body)
and string_of_value_option depth st = function
| Some v -> string_of_value depth st v
| None -> "<unset val>"
and string_of_value_loc_option depth st = function
| Some v -> string_of_value_loc depth st v
| None -> "<unset val>"

and string_of_object_ptr depth st ptr =
  match (Store.get_object st ptr) with
    | None -> "<reference to non-existing object>"
    | Some obj -> string_of_object depth st obj
and string_of_object depth st obj =
  Printf.sprintf "{[#proto: %s, #class: %s, #extensible: %B, #primval: %s, #code: %s] %s}"
  (string_of_value depth st obj.Values.object_proto) (String.of_list obj.Values.object_class)
  (obj.Values.object_extensible) (string_of_value depth st obj.Values.object_prim_value)
  (string_of_value depth st obj.Values.object_code)
  (string_of_prop_list depth st (Values.Heap.to_list obj.Values.object_properties_) [])
and string_of_prop_list depth st l skip =
  let string_of_prop = function (name, attr) ->
    Printf.sprintf "'%s': %s" (String.of_list name) (string_of_attr depth st attr)
  in let rec string_of_prop_list_aux props skip acc =
    match props with
    | [] -> acc
    | (name, value) :: tl ->
        if StringSet.mem (String.of_list name) skip then
          string_of_prop_list_aux tl skip acc
        else
          string_of_prop_list_aux tl (StringSet.add (String.of_list name) skip) (acc ^ ", " ^ (string_of_prop (name, value)))
  in match l with
  | [] -> ""
  | (name, value) :: tl ->
      let skip0 = (StringSet.singleton (String.of_list name)) in
      let skip1 = (List.fold_left (fun set elem -> StringSet.add (String.of_list elem) set) skip0 skip) in
      string_of_prop_list_aux tl skip1 (string_of_prop (name, value))

and string_of_expression depth e =
  "<expr>"
and string_of_expression_option depth = function
| Some e -> string_of_expression depth e
| None -> "<unset expr>"

and string_of_attr depth st = function
| Values.Coq_attributes_data_of d -> Values.attributes_data_rect (fun v w c e -> Printf.sprintf "{#value %s, #writable %B, #configurable %B, #enumerable %B}" (string_of_value depth st v) w c e) d
| Values.Coq_attributes_accessor_of d -> Values.attributes_accessor_rect (fun g s e c -> Printf.sprintf "{#getter %s, #setter %s}" (string_of_value depth st g) (string_of_value depth st s)) d (* enumerable and configurable ignored *)

let string_of_store depth c st =
  let locs = Utils.Heap.to_list c in
  let pred = string_of_value_loc depth st in
  String.concat "" (List.map (fun (k, v) -> Printf.sprintf "let (%s = %s) \n" (String.of_list k) (pred v)) locs)

