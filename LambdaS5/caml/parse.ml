open Batteries

open Ljs_syntax

let sprintf_pos p = Printf.sprintf "row %d col %d" p.Lexing.pos_lnum p.Lexing.pos_bol

let rec check_var_scope vs e =
  match e with
  | Fail (_, _)
  | Dump
  | Empty _
  | Null _
  | Undefined _
  | String _
  | Num _
  | Int _
  | True _
  | False _ -> ()
  | Id ((p1, p2, _), i) -> if Set.mem i vs then () else failwith (Printf.sprintf "Parse error: undefined id %s at %s" i (sprintf_pos p1))
  | Object (_, _, l, _) -> List.iter (fun (_, e) -> check_var_scope vs e) l
  | GetAttr (_, _, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | SetAttr (_, _, e1, e2, e3) -> check_var_scope vs e1; check_var_scope vs e2; check_var_scope vs e3
  | GetObjAttr (_, _, e1) -> check_var_scope vs e1
  | SetObjAttr (_, _, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | DeleteField (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | GetInternal (_, _, e1) -> check_var_scope vs e1
  | SetInternal (_, _, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | OwnFieldNames (_, e1) -> check_var_scope vs e1
  | Op1 (_, _, e1) -> check_var_scope vs e1
  | Op2 (_, _, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | If (_, e1, e2, e3) -> check_var_scope vs e1; check_var_scope vs e2; check_var_scope vs e3
  | App (_, e1, es) -> check_var_scope vs e1; List.iter (check_var_scope vs) es
  | Seq (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | JSeq (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | Let (_, s, e1, e2) -> check_var_scope vs e1; check_var_scope (Set.add s vs) e2
  | Rec (_, s, e1, e2) -> check_var_scope (Set.add s vs) e1; check_var_scope (Set.add s vs) e2
  | Label (_, _, e1) -> check_var_scope vs e1
  | Break (_, _, e1) -> check_var_scope vs e1
  | TryCatch (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | TryFinally (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | Throw (_, e1) -> check_var_scope vs e1
  | Lambda (_, is, e) -> check_var_scope (Set.union (Set.of_list is) vs) e
  | Eval (_, e1, e2) -> check_var_scope vs e1; check_var_scope vs e2
  | Hint (_, _, e1) -> check_var_scope vs e1

let parse_es5 cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      let v = Ljs_parser.prog Ljs_lexer.token lexbuf in
      check_var_scope Set.empty v; v
    with
      |  Failure "lexing: empty token" ->
           failwith (Printf.sprintf "lexical error at %s, %s" (sprintf_pos(Lexing.lexeme_start_p lexbuf)) (sprintf_pos(Lexing.lexeme_end_p lexbuf)))
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | Parsing.Parse_error -> failwith (Printf.sprintf "parse error; unexpected token %s at %s"
                       (Lexing.lexeme lexbuf) (sprintf_pos (Lexing.lexeme_start_p lexbuf)))

let parse_es5_env cin name =
  let lexbuf = Lexing.from_channel cin in
    try
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      let v = Ljs_parser.env Ljs_lexer.token lexbuf in
      check_var_scope Set.empty (v Dump); v
    with
      |  Failure "lexing: empty token" ->
           failwith "lexical error"
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | Parsing.Parse_error -> failwith (Printf.sprintf "parse error; unexpected token %s at %s"
                       (Lexing.lexeme lexbuf) (sprintf_pos (Lexing.lexeme_start_p lexbuf)))



