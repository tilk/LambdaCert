
open Batteries

let parse_es5 cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      Ljs_parser.prog Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith "lexical error"
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | _ -> failwith (Printf.sprintf "parse error; unexpected token %s"
                       (Lexing.lexeme lexbuf))

let parse_es5_env cin name =
  let lexbuf = Lexing.from_channel cin in
    try
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      Ljs_parser.env Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith "lexical error"
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | _ -> failwith (Printf.sprintf "parse error; unexpected token %s"
                       (Lexing.lexeme lexbuf))


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

