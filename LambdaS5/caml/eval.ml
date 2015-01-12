
open Batteries

let usage_msg = "Usage: "

let store = ref None

let js_parser = ref None 

let get_store () = if Option.is_none !store then store := Some Store.create_store; Option.get !store

let get_channel filename =
    if filename = "stdin" then stdin else open_in filename

let handle_parameter filename = 
    let ast = match !js_parser with
        | Some jp -> (* assuming inputs to be JS files *)
            jp filename
        | None -> (* assuming inputs to be LJS files *)
            let ch = get_channel filename in
            let ret = Run.parse_es5 ch filename in
            close_in ch; ret in
    Run.print_result (Run.eval_ast (get_store ()) (Translate.translate_expr ast))

let load_store filename = 
    File.with_file_in filename (fun ch -> store := Some (Marshal.from_channel (open_in filename)))

let save_store filename = 
    File.with_file_out filename (fun ch -> Marshal.to_channel ch (get_store ()) [Marshal.Closures])

let load_env filename = 
    let ch = get_channel filename in 
    (match Run.eval_ast (get_store ()) (Translate.translate_expr (Run.parse_es5_env ch filename (Ljs_syntax.String (Ljs_syntax.Pos.dummy, "dumped")))) with
        | Context.Coq_result_some (Context.Coq_out_ter (st, (Context.Coq_res_value _))) ->
            store := Some st;
        | _ -> failwith "Unexpected result when loading an environment");
    close_in ch

let s5_js_parser filename jsfile = 
    let s5out = Unix.open_process_in (filename ^ " -desugar " ^ Filename.quote jsfile ^ " -print-src") in
    let s5ret = Run.parse_es5 s5out jsfile in
    match Unix.close_process_in s5out with
        | Unix.WEXITED 0 -> s5ret
        | _ -> failwith "S5 desugar failure"

let desugar_s5 filename = js_parser := Some (s5_js_parser filename)

let _ =
    Arg.parse 
        ["-load",
         Arg.String load_store,
         "path to saved environment";
         "-save",
         Arg.String save_store,
         "save the environment in a file";
         "-env",
         Arg.String load_env,
         "environment to parse";
         "-desugarS5",
         Arg.String desugar_s5,
         "path to LambdaS5 (for desugaring js)"
        ] 
        handle_parameter
        usage_msg

