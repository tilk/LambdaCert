
open Batteries

open LjsSyntax

let usage_msg = "Usage: "

let fformat = ref false

let store = ref None

let fprint = ref false

let top_run = ref false

let had_files = ref false

let get_store () = if Option.is_none !store then store := Some (create_ctx, create_store); Option.get !store

let get_channel filename =
    if filename = "stdin" then stdin else open_in filename

let handle_parameter filename = 
    had_files := true;
    let ast = 
        if !fformat then
            let Some jp = Desugar.get_js_parser () in
            jp filename
        else
            let ch = get_channel filename in
            let ret = Parse.parse_es5 ch filename in
            close_in ch; Translate.translate_expr ret in
    try
        if !fprint then (print_string (Ljs_pretty.exp_to_string ast); print_string "\n")
        else Run.print_result (Run.eval_ast (get_store ()) ast)
    with e -> 
        Printexc.print_backtrace stderr;
        raise e

let load_store filename = 
    File.with_file_in filename (fun ch -> store := Some (Marshal.from_channel (open_in filename)))

let save_store filename = 
    File.with_file_out filename (fun ch -> Marshal.to_channel ch (get_store ()) [Marshal.Closures])

let mk_env_vars () =
    let props = List.map (function (s, _) -> (s, Coq_property_data (Coq_data_intro (Coq_expr_id s, Coq_expr_bool true, Coq_expr_bool false, Coq_expr_bool false)))) (LibFinmap.FinmapImpl.to_list_impl (fst (get_store ()))) in
    match Run.eval_ast (get_store ()) (Coq_expr_seq (Coq_expr_set_attr (Coq_pattr_getter, Coq_expr_id (String.to_list "%makeGlobalEnv"), Coq_expr_string (String.to_list "make"), Coq_expr_lambda ([String.to_list "%"], Coq_expr_object (Translate.translate_attrs Ljs_syntax.d_attrs, [], props))), Coq_expr_dump)) with
        | Coq_result_dump (c, st) -> 
            store := Some (c, st)
        | r -> failwith "Internal error"

let load_env filename = 
    let ch = get_channel filename in 
    (match Run.eval_ast (get_store ()) (Translate.translate_expr (Parse.parse_es5_env ch filename (Ljs_syntax.Dump))) with
        | Coq_result_dump (c, st) ->
            store := Some (c, st);
            mk_env_vars ()
        | r -> failwith ("Unexpected result when loading an environment: " ^ Run.result_to_string r));
    close_in ch

let coq_save_store filename = 
    had_files := true;
    let (c, st) = get_store () in
    File.with_file_out filename (fun ch -> 
        try PrettyPrintCoq.ctx_store_to_output ch c st
        with e -> 
            Printexc.print_backtrace stderr;
            raise e)

let desugar_s5 filename = Desugar.set_js_parser_s5 filename 

let desugar_builtin filename = Desugar.set_js_parser_builtin filename

let format_js () = fformat := true

let format_ljs () = fformat := false

let print_not_eval () = fprint := true

let run_toplevel () = top_run := true

let _ =
    Arg.parse 
        ["-load",
         Arg.String load_store,
         "path to saved environment";
         "-save",
         Arg.String save_store,
         "save the environment in a file";
         "-coq-save",
         Arg.String coq_save_store,
         "export the environment to Coq";
         "-env",
         Arg.String load_env,
         "environment to parse";
         "-desugarBuiltin",
         Arg.String desugar_builtin,
         "path to the external Javascript-to-JSON parser";
         "-desugarS5",
         Arg.String desugar_s5,
         "path to LambdaS5 (for desugaring js)";
         "-js",
         Arg.Unit format_js,
         "parse inputs as Javascript";
         "-ljs",
         Arg.Unit format_ljs,
         "parse inputs as S5";
         "-print",
         Arg.Unit print_not_eval,
         "print S5 code instead of interpreting";
         "-top",
         Arg.Unit run_toplevel,
         "run the toplevel";
        ] 
        handle_parameter
        usage_msg;
    if !top_run then Top.toplevel (get_store()) else
    if not !had_files then print_string "Use -help to get information on usage\n"

