
open Batteries

let js_parser = ref None 

let get_js_parser () = !js_parser

let s5_js_parser filename jsfile = 
    let s5out = Unix.open_process_in (filename ^ " -desugar " ^ Filename.quote jsfile ^ " -print-src") in
    let s5ret = Parse.parse_es5 s5out jsfile in
    match Unix.close_process_in s5out with
        | Unix.WEXITED 0 -> Translate.translate_expr s5ret
        | _ -> failwith "S5 desugar failure"

let set_js_parser_s5 filename = js_parser := Some (s5_js_parser filename)

let desugar_file s = 
    match get_js_parser () with
    | Some p -> p s
    | None -> failwith "No Javascript parser available" 

let desugar s =
    let filename = File.with_temporary_out (fun o fn -> String.print o s; fn) in
    desugar_file filename

