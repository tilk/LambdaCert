
val get_js_parser : unit -> (string -> LjsSyntax.expr) option

val set_js_parser_s5 : string -> unit

val desugar_file : string -> LjsSyntax.expr

val desugar : string -> LjsSyntax.expr

