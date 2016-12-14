
open Batteries
open LjsSyntax
open LjsCommon

let eval_ast (c, st) ast =
  LjsInterpreter.lazy_eval max_int c st ast

let rec js_value_to_string ptrs st v =
  match v with
  | Coq_value_null -> "null"
  | Coq_value_empty -> "undefined"
  | Coq_value_undefined -> "undefined"
  | Coq_value_string s -> String.quote (String.of_list s) 
  | Coq_value_number f -> String.of_list (JsNumber.to_string f)
  | Coq_value_bool true -> "true"
  | Coq_value_bool false -> "false"
  | Coq_value_closure _ -> "ljs function (*UNEXPECTED*)"
  | Coq_value_object ptr -> 
    match LibFinmap.read_option_inst st ptr with
    | Some obj -> if BatSet.mem ptr ptrs then "(*CYCLIC*)" else js_object_to_string (BatSet.add ptr ptrs) st obj
    | None -> "invalid object pointer (*BUG*)"
and js_object_to_string ptrs st obj =
  match String.of_list (object_class obj) with
  | "Boolean" ->
    begin match LibFinmap.read_option_inst (object_internal obj) (String.to_list "primval") with
    | Some (Coq_value_bool b) -> "new Boolean(" ^ (if b then "true" else "false") ^ ")"
    | _ -> "invalid boolean object (*BUG*)"
    end
  | "String" ->
    begin match LibFinmap.read_option_inst (object_internal obj) (String.to_list "primval") with
    | Some (Coq_value_string f) -> "new String(" ^ String.quote (String.of_list f) ^ ")"
    | _ -> "invalid string object (*BUG*)"
    end
  | "Number" ->
    begin match LibFinmap.read_option_inst (object_internal obj) (String.to_list "primval") with
    | Some (Coq_value_number f) -> "new Number(" ^ string_of_float f ^ ")"
    | _ -> "invalid number object (*BUG*)"
    end
  | "Function" -> "Function"
  | "Object" -> "{" ^ List.fold_left (^) "" (List.map (js_property_to_string ptrs st) (LibFinmap.to_list_inst (object_properties obj))) ^ "}" 
  | "Array" -> 
    begin match LibFinmap.read_option_inst (object_properties obj) (String.to_list "length") with
    | Some (Coq_attributes_data_of {attributes_data_value=Coq_value_number f}) -> 
      if int_of_float f == 0 then "[]" else
      "[" ^ List.fold_left (^) "" (List.map (js_array_elem_to_string ptrs st obj) (List.range 0 `To (int_of_float f - 1))) ^ "]"
    | _ -> "invalid array object (*BUG*)"
    end
  | c ->
    "object of class " ^ c
and js_property_to_string ptrs st prop =
  match prop with
  | (s, Coq_attributes_data_of d) -> String.of_list s ^ ":" ^ js_value_to_string ptrs st d.attributes_data_value ^ ", "
  | (s, Coq_attributes_accessor_of a) -> "accessor, "
and js_array_elem_to_string ptrs st obj k =
  match LibFinmap.read_option_inst (object_properties obj) (String.to_list (string_of_int k)) with
  | Some (Coq_attributes_data_of d) -> js_value_to_string ptrs st d.attributes_data_value ^ ", "
  | _ -> ", "

let exception_to_string st v =
  try
    let Coq_value_object ptr = v in
    let Some obj = LibFinmap.read_option_inst st ptr in
    let Some (Coq_attributes_data_of { attributes_data_value = Coq_value_object ptr' }) = LibFinmap.read_option_inst (object_properties obj) (String.to_list "%js-exn") in
    let Some obj' = LibFinmap.read_option_inst st ptr' in
    let Coq_result_some (Some (Coq_attributes_data_of { attributes_data_value = Coq_value_string s_name })) = get_property st obj' (String.to_list "name") in
    let Coq_result_some (Some (Coq_attributes_data_of { attributes_data_value = Coq_value_string s_msg })) = get_property st obj' (String.to_list "message") in
    "Uncaught exception: " ^ String.of_list s_name ^ ": " ^ String.of_list s_msg
  with Match_failure _ -> "Uncaught exception: " ^ js_value_to_string BatSet.empty st v 

let result_to_string_as b result =
  match result with
  | Coq_result_bottom -> "Interpreter timed out"
  | Coq_result_fail f -> "Fail: " ^ String.of_list f
  | Coq_result_impossible f -> "The impossible happened: " ^ String.of_list f
  | Coq_result_dump (_, _) -> "The interpreter dumped state"
  | Coq_result_some o -> match o with
    | Coq_out_div -> "Interpreter produced out_div, should not happen!"
    | Coq_out_ter (store, res) -> match res with
      | Coq_res_value v -> if b then PrettyPrint.string_of_value 5 store v else js_value_to_string BatSet.empty store v
      | Coq_res_exception e -> 
        if b then "Uncaught exception: " ^ PrettyPrint.string_of_value 5 store e
        else exception_to_string store e
      | Coq_res_break (l, v) -> Printf.sprintf "Uncaught break %s: %s" (String.of_list l) (PrettyPrint.string_of_value 5 store v)
  
let result_to_string result = result_to_string_as false result

let print_result_as b result = print_string (result_to_string_as b result); print_string "\n"

let print_result result = print_result_as false result

let result_fail result = 
  match result with
  | Coq_result_some (Coq_out_ter (_, Coq_res_exception _)) 
  | Coq_result_some (Coq_out_ter (_, Coq_res_break (_, _))) -> true
  | _ -> false

let result_abort result =
  match result with
  | Coq_result_bottom
  | Coq_result_fail _ 
  | Coq_result_impossible _
  | Coq_result_dump (_, _)
  | Coq_result_some Coq_out_div -> true
  | _ -> false

let result_store result =
  match result with
  | Coq_result_some (Coq_out_ter (st, _)) -> st

