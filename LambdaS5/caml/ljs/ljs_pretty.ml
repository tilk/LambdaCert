open Batteries
open LjsSyntax

open Format
open FormatExt 

let string_of_attr attr = match attr with
  | Coq_pattr_value -> "#value"
  | Coq_pattr_getter -> "#getter"
  | Coq_pattr_setter -> "#setter"
  | Coq_pattr_config -> "#configurable"
  | Coq_pattr_writable -> "#writable"
  | Coq_pattr_enum -> "#enumerable"

let string_of_oattr oattr = match oattr with
  | Coq_oattr_proto -> "#proto"
  | Coq_oattr_class -> "#class"
  | Coq_oattr_extensible -> "#extensible"
  | Coq_oattr_primval -> "#primval"
  | Coq_oattr_code -> "#code"

let string_of_unary_op s = match s with
    | Coq_unary_op_typeof -> "typeof"
    | Coq_unary_op_is_closure -> "closure?"
    | Coq_unary_op_is_primitive -> "primitive?"
    | Coq_unary_op_prim_to_str -> "prim->str"
    | Coq_unary_op_prim_to_num -> "prim->num"
    | Coq_unary_op_prim_to_bool -> "prim->bool"
    | Coq_unary_op_print -> "print"
    | Coq_unary_op_pretty -> "pretty"
    | Coq_unary_op_object_to_string -> "object-to-string"
    | Coq_unary_op_strlen -> "strlen"
    | Coq_unary_op_is_array -> "is-array"
    | Coq_unary_op_to_int32 -> "to-int32"
    | Coq_unary_op_not -> "!"
    | Coq_unary_op_void -> "void"
    | Coq_unary_op_floor -> "floor"
    | Coq_unary_op_ceil -> "ceil"
    | Coq_unary_op_abs -> "abs"
    | Coq_unary_op_log -> "log"
    | Coq_unary_op_ascii_ntoc -> "ascii_ntoc"
    | Coq_unary_op_ascii_cton -> "ascii_cton"
    | Coq_unary_op_to_lower -> "to-lower"
    | Coq_unary_op_to_upper -> "to-upper"
    | Coq_unary_op_bnot -> "~"
    | Coq_unary_op_sin -> "sin"
    | Coq_unary_op_numstr_to_num -> "numstr->num"
    | Coq_unary_op_current_utc_millis -> "current-utc-millis"
    | _ -> failwith "operator not implemented"

let string_of_binary_op s = match s with
    | Coq_binary_op_seq -> ";"
    | Coq_binary_op_add -> "+"
    | Coq_binary_op_sub -> "-"
    | Coq_binary_op_div -> "/"
    | Coq_binary_op_mul -> "*"
    | Coq_binary_op_mod -> "%"
    | Coq_binary_op_band -> "&"
    | Coq_binary_op_bor -> "|"
    | Coq_binary_op_bxor -> "^"
    | Coq_binary_op_shiftl -> "<<"
    | Coq_binary_op_shiftr -> ">>"
    | Coq_binary_op_zfshiftr -> ">>>"
    | Coq_binary_op_lt -> "<"
    | Coq_binary_op_le -> "<="
    | Coq_binary_op_gt -> ">"
    | Coq_binary_op_ge -> ">="
    | Coq_binary_op_stx_eq -> "stx="
    | Coq_binary_op_abs_eq -> "abs="
    | Coq_binary_op_same_value -> "sameValue"
    | Coq_binary_op_has_property -> "hasProperty"
    | Coq_binary_op_has_own_property -> "hasOwnProperty"
    | Coq_binary_op_string_plus -> "string+"
    | Coq_binary_op_string_lt -> "string<"
    | Coq_binary_op_base -> "base"
    | Coq_binary_op_char_at -> "char-at"
    | Coq_binary_op_locale_compare -> "locale-compare"
    | Coq_binary_op_pow -> "pow"
    | Coq_binary_op_to_fixed -> "to-fixed"
    | Coq_binary_op_is_accessor -> "isAccessor"
    | _ -> failwith "operator not implemented"


(* Takes a function exprec to use for all recursive calls. This allows us to create the
 * standard recursive printer, defined below as exp, but also to override the printer for
 * certain cases, like so:
 * let rec myexp e = match e with
 * | Num _ -> text (string_of_int 42)
 * | If (_, c, t, _) -> horz [text "if"; myexp c; text "then"; myexp t]
 * | _ -> exp_helper myexp e
 * For a real example, check out ljs_sym_trace.ml.
 *)
let rec exp_helper exprec e = match e with
  | Coq_expr_empty -> text "empty"
  | Coq_expr_null _ -> text "null"
  | Coq_expr_undefined _ -> text "undefined"
  | Coq_expr_number n -> text (string_of_float n)
  | Coq_expr_string s -> text ("\"" ^ (String.escaped (String.of_list s)) ^ "\"")
  | Coq_expr_true _ -> text "true"
  | Coq_expr_false _-> text "false"
  | Coq_expr_id x -> text (String.of_list x)
  | Coq_expr_object (avs, props) -> begin
    match props with
    | [] -> braces (attrsv exprec avs)
    | _ -> braces (vert [attrsv exprec avs; vert (vert_intersperse (text ",") (List.map (prop exprec) props))])
  end
  | Coq_expr_set_field (o, f, v) ->
    squish [exprec o; brackets (horzOrVert [exprec f; text "="; exprec v])]
  | Coq_expr_get_field (o, f) ->
    squish [exprec o; brackets (exprec f)]
  | Coq_expr_delete_field (o, f) ->
    squish [exprec o; brackets (horz [text "delete"; exprec f])]
  | Coq_expr_get_attr (a, o, f) ->
    squish [exprec o;
            brackets (horz [exprec f; angles (horz [text (string_of_attr a)])])]
  | Coq_expr_set_attr (a, o, f, v) ->
    squish [exprec o;
            brackets (squish [exprec f; angles (horz [text (string_of_attr a)]);
                              text "="; exprec v])]
  | Coq_expr_get_obj_attr (a, o) ->
    squish [exprec o;
            brackets (angles (horz [text (string_of_oattr a)]))]
  | Coq_expr_set_obj_attr (a, o, v) ->
    squish [exprec o;
            brackets (squish [angles (horz [text (string_of_oattr a)]);
                              text "="; exprec v])]
  | Coq_expr_own_field_names (o) ->
    squish [text "get-own-field-names"; parens (exprec o)]
  | Coq_expr_op1 (op, e) -> 
    squish [text "prim"; parens (horz [text ("\"" ^ string_of_unary_op op ^ "\","); exprec e])]
  | Coq_expr_op2 (op, e1, e2) ->
    squish [text "prim"; parens (horz [text ("\"" ^ string_of_binary_op op ^ "\","); exprec e1; text ","; exprec e2])]
  | Coq_expr_if (c, t, e) -> 
    horz [text "if"; vert [parens (horz [exprec c]);
                           braces (exprec t);
                           text "else";
			   (match e with
			   | Coq_expr_if _ -> (exprec e)
			   | _ -> braces (exprec e))]]
  | Coq_expr_app (f, args) ->
    squish [exprec f; parens (vert (vert_intersperse (text ",") (List.map exprec args)))]
  | Coq_expr_seq (e1, e2) ->
    vert [squish [exprec e1; text ";"]; exprec e2]
  | Coq_expr_let (x, e, body) ->
    braces (horz [text "let"; vert [parens (horz [text (String.of_list x); text "="; exprec e]);
                                    opt_braces exprec body]])
  | Coq_expr_recc (x, e, body) -> 
    horz [text "rec"; vert [parens (horz [text (String.of_list x); text "="; exprec e]);
                            opt_braces exprec body]]
  | Coq_expr_label (l, e) ->
    vert [horz [text "label"; text (String.of_list l); text ":"]; braces (exprec e)]
  | Coq_expr_break (l, e) ->
    horz [text "break"; text (String.of_list l); exprec e]
  | Coq_expr_try_catch (body, catch) ->
    vert [text "try"; braces (exprec body); text "catch"; braces (exprec catch)]
  | Coq_expr_try_finally (body, fin) ->
    vert [text "try"; braces (exprec body); text "finally"; braces (exprec fin)]
  | Coq_expr_throw (e) ->
    horz [text "throw"; exprec e]
  | Coq_expr_lambda (xs, e) ->
    vert [squish [text "func"; parens (horz (intersperse (text ",") (List.map text (List.map String.of_list xs))))];
          braces (exprec e)]
  | Coq_expr_eval (s, obj) -> 
      squish [text "@eval"; parens (horz [exprec s; text ","; exprec obj])]
  | Coq_expr_hint (hint, e) ->
      parens (vert [squish [text "/*: "; text (String.of_list hint); text "*/"];
	                 exprec e])
  | Coq_expr_dump -> text "DUMP"

and opt_braces exprec expr = match expr with
  | Coq_expr_seq _ -> braces (exprec expr)
  | _ -> exprec expr

and attrsv exprec (Coq_objattrs_intro (k, b, p, c, _)) =
  brackets (horzOrVert (List.map (fun x -> squish [x; (text ",")])
                             [horz [text "#proto:"; exprec p]; 
                              horz [text "#code:"; exprec c]; 
                              horz [text "#class:"; exprec k]; 
                              horz [text "#extensible:"; exprec b]]))
              
(* TODO: print and parse enum and config *)
and prop exprec (f, prop) = match prop with
  | Coq_property_data (Coq_data_intro (v, w, enum, config)) ->
    horz [text ("'" ^ String.of_list f ^ "'"); text ":"; 
          braces (horzOrVert [horz [text "#value"; parens (exprec v); text ","]; 
                              horz [text "#writable"; exprec w; text ","];
                              horz [text "#configurable"; exprec config]])]
  | Coq_property_accessor (Coq_accessor_intro (g, s, enum, config)) ->
    horz [text ("'" ^ String.of_list f ^ "'"); text ":"; braces (vert [horz [text "#getter";
                                          exprec g; text ","];
                                          horz[text "#setter";
                                               exprec s]])]

let rec exp e = exp_helper exp e

let exp_to_string e = to_string exp e


