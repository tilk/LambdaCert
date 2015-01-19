
val get_js_parser : unit -> (string -> Syntax.expr) option

val set_js_parser_s5 : string -> unit

val desugar_file : string -> Syntax.expr

val desugar : string -> Syntax.expr

