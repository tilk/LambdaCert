
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


let eval_ast store ast =
  Interpreter.runs_eval max_int store ast

let print_result result =
  (match result with
  | Context.Coq_result_fail f -> print_string "Fail: "; print_string (CoqUtils.implode f)
  | Context.Coq_result_impossible f -> print_string "The impossible happened: "; print_string (CoqUtils.implode f)
  | Context.Coq_result_some o -> match o with
    | Context.Coq_out_div -> print_string "Interpreter produced out_div, should not happen!"
    | Context.Coq_out_ter (store, res) -> match res with
      | Context.Coq_res_value v -> print_string (PrettyPrint.string_of_value_loc 5 store v)
      | Context.Coq_res_exception e -> print_string "Uncaught exception: "; print_string (PrettyPrint.string_of_value_loc 5 store e)
      | Context.Coq_res_break (l, v) -> Printf.printf "Uncaught break %s: %s" (CoqUtils.implode l) (PrettyPrint.string_of_value_loc 5 store v)
  );
  print_string "\n"

