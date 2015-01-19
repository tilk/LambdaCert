
open Batteries

let eval_ast (c, st) ast =
  Interpreter.runs_eval max_int c st ast

let result_to_string result =
  match result with
  | Context.Coq_result_bottom -> "Interpreter timed out"
  | Context.Coq_result_fail f -> "Fail: " ^ String.of_list f
  | Context.Coq_result_impossible f -> "The impossible happened: " ^ String.of_list f
  | Context.Coq_result_dump (_, _) -> "The interpreter dumped state"
  | Context.Coq_result_some o -> match o with
    | Context.Coq_out_div -> "Interpreter produced out_div, should not happen!"
    | Context.Coq_out_ter (store, res) -> match res with
      | Context.Coq_res_value v -> PrettyPrint.string_of_value 5 store v
      | Context.Coq_res_exception e -> "Uncaught exception: " ^ PrettyPrint.string_of_value 5 store e
      | Context.Coq_res_break (l, v) -> Printf.sprintf "Uncaught break %s: %s" (String.of_list l) (PrettyPrint.string_of_value 5 store v)
  

let print_result result = print_string (result_to_string result); print_string "\n"

