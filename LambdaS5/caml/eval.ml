
open Batteries

let usage_msg = "Usage: "

let store = ref None

let get_store () = if Option.is_none !store then store := Some Store.create_store; Option.get !store

let get_channel filename =
    if filename = "stdin" then stdin else open_in filename

let handle_parameter filename = 
    let ch = get_channel filename in
    Run.print_result (Run.eval_ast (get_store ()) (Run.parse_es5 ch filename)); 
    close_in ch

let load_store filename = 
    let ch = open_in filename in 
    store := Some (Marshal.from_channel (open_in filename)); 
    close_in ch

let save_store filename = 
    let ch = open_out filename in 
    Marshal.to_channel ch (get_store ()) [Marshal.Closures]; 
    close_out ch

let load_env filename = 
    let ch = get_channel filename in 
    let (st, _res) = Run.eval_ast (get_store ()) (Run.parse_es5_env ch filename (Syntax.String (CoqUtils.explode "dumped"))) in
    store := Some st;
    close_in ch

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
         "environment to parse"
        ] 
        handle_parameter
        usage_msg

