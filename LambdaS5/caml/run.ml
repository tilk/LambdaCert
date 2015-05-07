
open Batteries
open LjsSyntax

let eval_ast (c, st) ast =
  LjsInterpreter.runs_eval max_int c st ast

let js_value_to_string v =
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

let result_to_string_as b result =
  match result with
  | Coq_result_bottom -> "Interpreter timed out"
  | Coq_result_fail f -> "Fail: " ^ String.of_list f
  | Coq_result_impossible f -> "The impossible happened: " ^ String.of_list f
  | Coq_result_dump (_, _) -> "The interpreter dumped state"
  | Coq_result_some o -> match o with
    | Coq_out_div -> "Interpreter produced out_div, should not happen!"
    | Coq_out_ter (store, res) -> match res with
      | Coq_res_value v -> if b then PrettyPrint.string_of_value 5 store v else js_value_to_string v
      | Coq_res_exception e -> 
        if b then "Uncaught exception: " ^ PrettyPrint.string_of_value 5 store e
        else "exception caught (* TODO *)"
      | Coq_res_break (l, v) -> Printf.sprintf "Uncaught break %s: %s" (String.of_list l) (PrettyPrint.string_of_value 5 store v)
  
let result_to_string result = result_to_string_as true result

let print_result_as b result = print_string (result_to_string_as b result); print_string "\n"

let print_result result = print_result_as true result

