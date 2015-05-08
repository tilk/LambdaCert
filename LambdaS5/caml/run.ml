
open Batteries
open LjsSyntax
open LjsCommon

let eval_ast (c, st) ast =
  LjsInterpreter.runs_eval max_int c st ast

let js_value_to_string st v =
  match v with
  | Coq_value_null -> "null"
  | Coq_value_empty -> "undefined"
  | Coq_value_undefined -> "undefined"
  | Coq_value_string s -> "\"" ^ (String.of_list s) ^ "\""
  | Coq_value_number f -> String.of_list (JsNumber.to_string f)
  | Coq_value_bool true -> "true"
  | Coq_value_bool false -> "false"
  | Coq_value_closure _ -> "ljs function (*UNEXPECTED*)"
  | Coq_value_object ptr -> "object (* TODO *)"

let exception_to_string st v =
  try
    let Coq_value_object ptr = v in
    let Some obj = LibFinmap.read_option_inst st ptr in
    let Some (Coq_attributes_data_of { attributes_data_value = Coq_value_object ptr' }) = LibFinmap.read_option_inst (object_properties obj) (String.to_list "%js-exn") in
    let Some obj' = LibFinmap.read_option_inst st ptr' in
    let Coq_result_some (Some (Coq_attributes_data_of { attributes_data_value = Coq_value_string s_name })) = get_property st obj' (String.to_list "name") in
    let Coq_result_some (Some (Coq_attributes_data_of { attributes_data_value = Coq_value_string s_msg })) = get_property st obj' (String.to_list "message") in
    "Uncaught exception: " ^ String.of_list s_name ^ ": " ^ String.of_list s_msg
  with Match_failure _ -> "Uncaught exception: " ^ js_value_to_string st v 

let result_to_string_as b result =
  match result with
  | Coq_result_bottom -> "Interpreter timed out"
  | Coq_result_fail f -> "Fail: " ^ String.of_list f
  | Coq_result_impossible f -> "The impossible happened: " ^ String.of_list f
  | Coq_result_dump (_, _) -> "The interpreter dumped state"
  | Coq_result_some o -> match o with
    | Coq_out_div -> "Interpreter produced out_div, should not happen!"
    | Coq_out_ter (store, res) -> match res with
      | Coq_res_value v -> if b then PrettyPrint.string_of_value 5 store v else js_value_to_string store v
      | Coq_res_exception e -> 
        if b then "Uncaught exception: " ^ PrettyPrint.string_of_value 5 store e
        else exception_to_string store e
      | Coq_res_break (l, v) -> Printf.sprintf "Uncaught break %s: %s" (String.of_list l) (PrettyPrint.string_of_value 5 store v)
  
let result_to_string result = result_to_string_as true result

let print_result_as b result = print_string (result_to_string_as b result); print_string "\n"

let print_result result = print_result_as true result

