
open Batteries
open LjsSyntax

let desugar_file jsfile =
    let data = File.with_file_in jsfile (fun ch -> IO.read_all ch) in
    match EjsFromJs.desugar_expr false (String.to_list data) with
    | Some e -> e 
    | None -> Coq_expr_app (Coq_expr_id (String.to_list "%SyntaxError"), [Coq_expr_string (String.to_list "Unknown parser error TODO")])

let desugar s =
    let filename = File.with_temporary_out (fun o fn -> String.print o s; fn) in
    desugar_file filename

