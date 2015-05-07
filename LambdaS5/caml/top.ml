
open LjsSyntax

class environment c st = 
object
    val ctx : ctx = c
    val init_store : store = st
    val mutable store : store = st
    val mutable ljsprint : bool = false
    method ljsprint b = ljsprint <- b
    method eval s =
        try
            let ast = Desugar.desugar s in
            let result = Run.eval_ast (ctx, store) ast in
            if ljsprint then begin print_string (Ljs_pretty.exp_to_string ast); print_string "\n" end;
            Run.print_result_as ljsprint result;
            match result with
            | Coq_result_some (Coq_out_ter (st', r)) -> 
                store <- st'
            | _ -> ()
        with e ->
            Printf.printf "Some error happened!\n"
    method reset = store <- init_store
end

let command_help =
"
List of commands:
#help: print this list of commands
#quit: quit the top-level
#reset: reset the state to the initial state
#ljsprint: show the desugared code and LambdaJS results
#jsprint: show only JS results
"

let rec read env = 
    Printf.printf "> "; 
    let l = (try read_line() with End_of_file -> print_string "\n"; exit 0) in
    scan env l 

and scan env = function
    | "" -> read env
    | s -> 
        begin match s.[0] with
        | '#' -> command env s
        | _ -> 
            env#eval s; read env
        end

and command env str = Scanf.sscanf str "# %s %s " (fun s s' -> match s with
  | "help" -> Printf.printf "%s" command_help; read env
  | "quit" -> print_newline ()
  | "reset" -> print_string "State reinitialised to the initial state."; env#reset; read env
  | "ljsprint" -> env#ljsprint true; read env
  | "jsprint" -> env#ljsprint false; read env
  | _ -> Printf.printf "Unknown command %s\n%s\n< " str command_help; read env) ;;

let toplevel (ctx, store) =
    command (new environment ctx store) "#help"

