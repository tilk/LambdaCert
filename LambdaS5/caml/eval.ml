
open Batteries

open Syntax

let usage_msg = "Usage: "

let store = ref None

let get_store () = if Option.is_none !store then store := Some (create_ctx, create_store); Option.get !store

let get_channel filename =
    if filename = "stdin" then stdin else open_in filename

let handle_parameter filename = 
    let ast = match Desugar.get_js_parser () with
        | Some jp -> (* assuming inputs to be JS files *)
            jp filename
        | None -> (* assuming inputs to be LJS files *)
            let ch = get_channel filename in
            let ret = Parse.parse_es5 ch filename in
            close_in ch; Translate.translate_expr ret in
    try
        Run.print_result (Run.eval_ast (get_store ()) ast)
    with e -> 
        Printexc.print_backtrace stderr;
        raise e

let load_store filename = 
    File.with_file_in filename (fun ch -> store := Some (Marshal.from_channel (open_in filename)))

let save_store filename = 
    File.with_file_out filename (fun ch -> Marshal.to_channel ch (get_store ()) [Marshal.Closures])

let mk_env_vars () =
    let props = List.map (function (s, _) -> (s, Syntax.Coq_property_data (Syntax.Coq_data_intro (Syntax.Coq_expr_id s, Syntax.Coq_expr_true, Syntax.Coq_expr_false, Syntax.Coq_expr_false)))) (HeapUtils.Heap.to_list (loc_heap (fst (get_store ())))) in
    match Run.eval_ast (get_store ()) (Syntax.Coq_expr_seq (Syntax.Coq_expr_set_bang (String.to_list "%makeGlobalEnv", Syntax.Coq_expr_lambda ([], Syntax.Coq_expr_object (Translate.translate_attrs Ljs_syntax.d_attrs, props))), Syntax.Coq_expr_dump)) with
        | Context.Coq_result_dump (c, st) -> 
            store := Some (c, st)
        | r -> failwith "Internal error"

let load_env filename = 
    let ch = get_channel filename in 
    (match Run.eval_ast (get_store ()) (Translate.translate_expr (Parse.parse_es5_env ch filename (Ljs_syntax.Dump))) with
        | Context.Coq_result_dump (c, st) ->
            store := Some (c, st);
            mk_env_vars ()
        | r -> failwith ("Unexpected result when loading an environment: " ^ Run.result_to_string r));
    close_in ch

let desugar_s5 filename = Desugar.set_js_parser_s5 filename

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

