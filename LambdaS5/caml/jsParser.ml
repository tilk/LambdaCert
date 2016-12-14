
open Batteries
open SpiderMonkey

let parsecmd = ref ""

let set_parsecmd s = parsecmd := s

let parse_file filename = 
    try Some (Translate_syntax.coq_syntax_from_file filename)
    with e -> None

let parse s = 
    let filename = File.with_temporary_out (fun o fn -> String.print o s; fn) in
    parse_file filename

