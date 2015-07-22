(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Batteries
open Yojson.Basic
open JsSyntax
open Printf
open Format
open FormatExt

let file_path_hint = ref ""

let is_null (v : json) : bool = v = `Null

let is_array (v : json) : bool = 
  match v with
  | `List _ -> true
  | _ -> false

let string (v : json) : string = 
  match v with
  | `String s -> s
  | _ -> failwith "JS parse error"

let int (v : json) : int = 
  match v with
  | `Int i -> i
  | _ -> failwith "JS parse error"

let list (v : json) = 
  match v with
  | `List l -> l
  | _ -> failwith "JS parse error"

let bool v = match v with
  | `Bool b -> b
  | _ -> failwith "expected boolean"

let rec get key (v : json) = match v with
  | `Assoc pairs ->
    begin try List.assoc key pairs
      with Not_found ->
        failwith ("expected a " ^ key ^ " field in " ^
                              (FormatExt.to_string (fun i -> (braces (horz (List.map text i)))) (List.map fst pairs)) ^ (string (get "type" v)))
    end
  | _ -> failwith (sprintf "expected a JSON object for key '%s' in get" key)

let try_get key v = match v with
  | `Assoc pairs ->
    begin try Some (List.assoc key pairs)
      with Not_found -> None
    end
  | _ -> failwith (sprintf "expected a JSON object for key '%s' in try_get" key)

let maybe (f : json -> 'a) (v : json) : 'a option =
  match is_null v with 
  | true -> None
  | false -> Some (f v)

let identifier (v : json) : string = match string (get "type" v) with
  | "Identifier" -> string (get "name" v)
  | typ -> failwith (sprintf "expected Identifier, got %s as type" typ)

let literal (v : json) : literal = match string (get "type" v) with
  | "Literal" -> begin match get "value" v with
      | `Null -> Coq_literal_null
      | `Bool b -> Coq_literal_bool b
      | `Float f -> Coq_literal_number f
      | `Int n -> Coq_literal_number (float_of_int n)
      | `String s -> Coq_literal_string (String.to_list s)
(*      | `Assoc [("re_lit", `String re_val)] -> Regexp re_val *)
      | `List _ -> failwith "Bad/unexpected array literal"
      | `Assoc _ -> failwith "Bad/unexpected object literal"
  end
  | typ -> failwith (sprintf "expected Literal, got %s as type" typ)

let propName (v : json) : propname = match string (get "type" v) with
  | "Identifier" -> Coq_propname_identifier (String.to_list (string (get "name" v)))
  | "Literal" -> begin match literal v with
      | Coq_literal_number n -> Coq_propname_number n
      | Coq_literal_string s -> Coq_propname_string s
      | _ -> failwith (sprintf "illegal literal used as property name")
  end
  | typ -> 
    failwith (sprintf "expected Literal or Identifier as prop-name, got %s" typ)

let label (v : json) : label = match maybe identifier v with
  | Some s -> Coq_label_string (String.to_list s)
  | None -> Coq_label_empty

let unary_op (v : json) : unary_op = match string (get "operator" v) with
  | "delete" -> Coq_unary_op_delete
  | "void" -> Coq_unary_op_void
  | "typeof" -> Coq_unary_op_typeof
  | "++" -> if bool (get "prefix" v) then Coq_unary_op_pre_incr else Coq_unary_op_post_incr
  | "--" -> if bool (get "prefix" v) then Coq_unary_op_pre_decr else Coq_unary_op_post_decr
  | "+" -> Coq_unary_op_add
  | "-" -> Coq_unary_op_neg
  | "~" -> Coq_unary_op_bitwise_not
  | "!" -> Coq_unary_op_not
  | x -> failwith ("Unknown unary op: " ^ x)

let binary_op (v : json) : binary_op = match string (get "operator" v) with
  | "*" -> Coq_binary_op_mult
  | "/" -> Coq_binary_op_div
  | "%" -> Coq_binary_op_mod
  | "+" -> Coq_binary_op_add
  | "-" -> Coq_binary_op_sub
  | "<<" -> Coq_binary_op_left_shift
  | ">>" -> Coq_binary_op_right_shift
  | ">>>" -> Coq_binary_op_unsigned_right_shift
  | "<" -> Coq_binary_op_lt
  | ">" -> Coq_binary_op_gt
  | "<=" -> Coq_binary_op_le
  | ">=" -> Coq_binary_op_ge
  | "instanceof" -> Coq_binary_op_instanceof
  | "in" -> Coq_binary_op_in
  | "==" -> Coq_binary_op_equal
  | "!=" -> Coq_binary_op_disequal
  | "===" -> Coq_binary_op_strict_equal
  | "!==" -> Coq_binary_op_strict_disequal
  | "&" -> Coq_binary_op_bitwise_and
  | "|" -> Coq_binary_op_bitwise_or
  | "^" -> Coq_binary_op_bitwise_xor
  | "&&" -> Coq_binary_op_and
  | "||" -> Coq_binary_op_or
  | x -> failwith ("Unknown binary op: " ^ x)

let assign_op (v : json) : binary_op option = match string (get "operator" v) with
  | "=" -> None
  | x -> Some (binary_op (`Assoc ["operator", `String (String.rchop x)]))

let rec directive_prologue (vl : json list) : string list =
  match vl with
  | v :: vl' -> 
    begin match string (get "type" v) with
    | "ExpressionStatement" -> 
      let ev = get "expression" v in
      begin match string (get "type" ev) with
      | "Literal" ->
        begin match get "value" ev with
        | `String _ -> 
          string (get "raw" ev) :: directive_prologue vl'
        | _ -> []
        end
      | _ -> []
      end
    | _ -> []
    end
  | _ -> []

let is_strict (v : json) : bool = 
  let dp = directive_prologue (list v) in
  List.mem "\"use strict\"" dp || List.mem "'use strict'" dp (* 14.1 *)

let rec stmt (v : json) : stat = 
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Statement, then drop the prefix. *)
    if String.length x > 9 && (String.sub x (String.length x - 9) 9 = "Statement") then
      String.sub x 0 (String.length x - 9) 
    else
      x (* could be a VariableDeclaration *) in
  match typ with
    | "VariableDeclaration" -> begin match string (get "kind" v) with
	| "var" -> Coq_stat_var_decl (List.map varDecl (list (get "declarations" v)))
	| kind -> failwith (sprintf "%s declarations are not valid ES5" kind)
    end
    | "Empty" -> Coq_stat_block []
    | "Block" -> Coq_stat_block (block (get "body" v))
    | "Expression" -> Coq_stat_expr (expr (get "expression" v))
    | "If" ->
      Coq_stat_if (expr (get "test" v),
	  stmt (get "consequent" v), 
	  maybe stmt (get "alternate" v))
    | "Labeled" -> Coq_stat_label (String.to_list (identifier (get "label" v)), stmt (get "body" v))
    | "Break" -> Coq_stat_break (label (get "label" v))
    | "Continue" -> Coq_stat_continue (label (get "label" v))
    | "With" -> Coq_stat_with (expr (get "object" v), stmt (get "body" v))
    | "Switch" ->
      Coq_stat_switch ([], expr (get "discriminant" v), switchbody (list (get "cases" v))) 
    | "Return" -> Coq_stat_return (maybe expr (get "argument" v))
    | "Throw" -> Coq_stat_throw (expr (get "argument" v))
    | "Try" -> Coq_stat_try (Coq_stat_block (block (get "block" v)),
      (* NOTE(jpolitz): We simply take the first handler --- multiple 
         handlers are Spidermonkey-specific.  JS only specifies one
         or zero catch blocks. *)
      (match (try_get "handlers" v) with
        | None -> catch (get "handler" v) (* New Spidermonkey *)
        | Some(handlers) ->
          (match (list handlers) with
            | [] -> None
            | [handler] -> catch handler (* Old Spidermonkey *)
            | _ -> failwith "More than one catch handler provided")),
      maybe (fun x -> Coq_stat_block (block x)) (get "finalizer" v))
    | "While" -> Coq_stat_while ([], expr (get "test" v), stmt (get "body" v))
    | "DoWhile" -> Coq_stat_do_while ([], stmt (get "body" v), expr (get "test" v))
    | "For" -> 
      let init = get "init" v in
      let test = maybe expr (get "test" v) in
      let update = maybe expr (get "update" v) in
      let body = stmt (get "body" v) in
      begin match init with
        | `Null -> Coq_stat_for ([], None, test, update, body)
        | _ ->
          begin match string (get "type" init) with
	    | "VariableDeclaration" -> 
	      Coq_stat_for_var ([], List.map varDecl (list (get "declarations" init)), 
                      test, update, body)
            | _ -> Coq_stat_for ([], Some (expr init), test, update, body)
          end
      end
    | "ForIn" -> 
      let left = get "left" v in
      let right = expr (get "right" v) in
      let body = stmt (get "body" v) in
      let each = bool (get "each" v) in
      if each then
        failwith "for-each statements are not valid ES5"
      else
        begin match string (get "type" left) with
          | "VariableDeclaration" ->
            let (name, value) = List.hd (List.map varDecl (list (get "declarations" left))) in
            Coq_stat_for_in_var ([], name, value, right, body) 
          | _ -> Coq_stat_for_in ([], expr left, right, body)
        end
    | "Debugger" -> Coq_stat_debugger 
    | "FunctionDeclaration" ->
      (* 12: Statements
       * NOTE Several widely used implementations of ECMAScript are known to 
       * support the use of FunctionDeclaration as a Statement. However there 
       * are significant and irreconcilable variations among the implementations 
       * in the semantics applied to such FunctionDeclarations. Because of these 
       * irreconcilable differences, the use of a FunctionDeclaration as a 
       * Statement results in code that is not reliably portable among 
       * implementations. It is recommended that ECMAScript implementations 
       * either disallow this usage of FunctionDeclaration or issue a warning 
       * when such a usage is encountered. Future editions of ECMAScript may 
       * define alternative portable means for declaring functions in a Statement 
       * context.
       *)
      failwith "Function Declarations not allowed as statements"
    | _ -> failwith (sprintf "unexpected %s statement" typ)

and varDecl (v : json) = 
    (String.to_list (identifier (get "id" v)), maybe expr (get "init" v))

and mem (v : json) : propname * propbody = 
    let name = propName (get "key" v) in
    let value = expr (get "value" v) in
    match string (get "kind" v) with
      | "init" -> (name, Coq_propbody_val value)
      | "get" -> begin match value with
	  | Coq_expr_function (None, [], body) -> (name, Coq_propbody_get body)
	  | _ -> failwith (sprintf "invalid body for getter")
      end
      | "set" -> begin match value with
	  | Coq_expr_function (None, xs, body) -> (name, Coq_propbody_set (xs, body))
	  | _ -> failwith (sprintf "invalid body for setter")
      end
      | kind -> failwith (sprintf "invalid kind of member: %s" kind)

and expr (v : json) : expr = 
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Expression, then drop the prefix. *)
    if String.length x < 10 || (String.sub x (String.length x - 10) 10 <> "Expression") then
      x (* perhaps a Literal, which isn't suffixed with Expression. *)
    else 
      String.sub x 0 (String.length x - 10) in  
  match typ with
    | "Literal" -> Coq_expr_literal (literal v)
    | "Identifier" -> Coq_expr_identifier (String.to_list (string (get "name" v)))
    | "This" -> Coq_expr_this 
    | "Array" ->
      let f = function 
        | `Null -> None
        | e -> Some (expr e) in
      Coq_expr_array (List.map f (list (get "elements" v))) 
    | ("Object" | "ObjectExpression") -> Coq_expr_object (List.map mem (list (get "properties" v)))
    | "Function" ->
      Coq_expr_function (maybe (fun x -> String.to_list (identifier x)) (get "id" v), 
	    List.map (fun x -> String.to_list (identifier x)) (list (get "params" v)),
	    (* Pull the body out of the BlockStatement *)
	    Coq_funcbody_intro (Coq_prog_intro (is_strict (get "body" (get "body" v)), srcElts (get "body" (get "body" v))), []))
    | "Unary" -> 
      if bool (get "prefix" v) then
        Coq_expr_unary_op (unary_op v, expr (get "argument" v))
      else
        failwith "unexpected POSTFIX unary operator"
    | "Binary"
    | "Logical" ->
      Coq_expr_binary_op (expr (get "left" v), binary_op v, expr (get "right" v))
    | "Assignment" -> 
      Coq_expr_assign (expr (get "left" v), assign_op v, expr (get "right" v))
    (* "UpdateOperator" disagrees with docs---operator is just a string *)
    | "Update" ->
      Coq_expr_unary_op (unary_op v, expr (get "argument" v)) 
    | "Conditional" ->
      Coq_expr_conditional (expr (get "test" v), expr (get "consequent" v),
	    expr (get "alternate" v)) 
    | "New" ->
      Coq_expr_new (expr (get "callee" v),
	   let args = get "arguments" v in
	   if is_null args then []
	   else List.map expr (list args))
    | "Call" ->
      Coq_expr_call (expr (get "callee" v), List.map expr (list (get "arguments" v)))
    | ("Member" | "MemberExpression") -> 
      if bool (get "computed" v) then
	Coq_expr_access (expr (get "object" v), expr (get "property" v))
      else
	Coq_expr_member (expr (get "object" v), String.to_list (identifier (get "property" v)))
    | "Sequence" ->
      List.reduce (fun x y -> Coq_expr_binary_op (x, Coq_binary_op_coma, y)) (List.map expr (list (get "expressions" v)))
    | typ -> failwith (sprintf "%s expressions are not in ES5" typ)

and case (v : json) =
  let e = get "test" v in
  let stmts = List.map stmt (list (get "consequent" v)) in
  match e with
    | `Null -> `Default stmts
    | _ -> `Case (Coq_switchclause_intro (expr e, stmts))

and switchbody (vs : json list) : switchbody =
  let allcases = List.map case vs in
  let from_Case x = match x with `Case c -> c | _ -> failwith "bug" in
  let deflts = List.filter_map (fun x -> match x with `Default stmts -> Some stmts | _ -> None) allcases in 
  match deflts with
  | [] -> Coq_switchbody_nodefault (List.map from_Case allcases)
  | [dstmts] -> 
    let [lcases; rcases] = List.nsplit (fun x -> match x with `Default _ -> true | _ -> false) allcases in
    Coq_switchbody_withdefault (List.map from_Case lcases, dstmts, List.map from_Case rcases)
  | _ -> failwith "Too many defaults in switch"

and catch (v : json) = 
    if is_array v then failwith "Multiple catches are spidermonky-only"
    else
      if is_null v then None
      else
        let param = match (get "type" (get "param" v)) with
	  `String s -> begin match s with
          | "Identifier" -> string (get "name" (get "param" v))
          | param -> (printf "param was %s" param; param)
	  end
        | _ -> failwith "Param wasn't a string" in
        let body = block (get "body" v) in Some (String.to_list param, Coq_stat_block body)

and block (v : json) = match is_array v with
  | true -> List.map stmt (list v)
  | false -> match string (get "type" v) with
      | "BlockStatement" -> List.map stmt (list (get "body" v))
      | _ -> failwith "expected array of statements or a BlockStatement"

and srcElt (v : json) : element = match string (get "type" v) with
  | "FunctionDeclaration" -> 
    Coq_element_func_decl (String.to_list (identifier (get "id" v)),
	      List.map (fun x -> String.to_list (identifier x)) (list (get "params" v)),
	      Coq_funcbody_intro (Coq_prog_intro (is_strict (get "body" (get "body" v)), (srcElts (get "body" (get "body" v)))), [])) 
  | _ -> Coq_element_stat (stmt v) 

and srcElts (v : json) : element list =
    List.map srcElt (list v)

let program (v : json) : prog option = 
  match string (get "type" v) with
    | "Program" -> Some (Coq_prog_intro (is_strict (get "body" v), srcElts (get "body" v)))
    | "ParseError" -> None (* TODO error message *)
    | typ -> failwith (sprintf "expected Program, got %s" typ)

let parse_spidermonkey (cin : in_channel) : prog option = 
    program (from_channel cin)

