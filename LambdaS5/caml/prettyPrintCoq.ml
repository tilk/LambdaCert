
open Batteries
open Format
open FormatExt
open LjsSyntax

let vals_store = ref Map.empty

let used_names = ref Set.empty

let in_ordered_vals = ref Set.empty

let ordered_vals = ref []

let named_exprs = ref Map.empty

let rfun c = match c with
    | '%' -> "priv" 
    | '$' -> "dol" 
    | '-' -> "_"
    | _ -> String.of_char c

let ident_for i =
    let ii = String.of_list i in 
    let ii' = String.replace_chars rfun ii in
    if not (Set.mem ii' !used_names)
    then (used_names := Set.add ii' !used_names; ii')
    else
    let rec f k i = 
        let i' = i ^ string_of_int k in
        if not (Set.mem i' !used_names)
        then (used_names := Set.add i' !used_names; i')
        else f (k+1) i
    in f 1 ii'

let reserve_named_val i v =
    let vst = !vals_store in
    if Map.mem v vst then ()
    else let ii = ident_for i in
    vals_store := Map.add v ii vst

let named_val i v = 
    let vst = !vals_store in
    if Map.mem v vst 
    then let ii = Map.find v vst in
    if Set.mem ii !in_ordered_vals
    then ()
    else begin ordered_vals := (ii,i,v) :: !ordered_vals; in_ordered_vals := Set.add ii !in_ordered_vals end; ii
    else let ii = ident_for i in 
    vals_store := Map.add v ii vst; 
    ordered_vals := (ii,i,v) :: !ordered_vals;
    in_ordered_vals := Set.add ii !in_ordered_vals;
    ii

let named_expr i e =
    let ii' = "ex_" ^ String.replace_chars rfun i in
    let est = !named_exprs in
    if not (Map.mem ii' est)
    then (named_exprs := Map.add ii' e est; ii')
    else
    let rec f k =
        let ii'' = ii' ^ string_of_int k in
        if not (Map.mem ii'' est)
        then (named_exprs := Map.add ii'' e est; ii'')
        else f (k+1)
    in f 1

let format_id i = text ("\"" ^ String.of_list i ^ "\"") (* TODO escaping *)

let format_list l = brackets (horzOrVert (vert_intersperse (text ";") l))

let format_id_list il = format_list (List.map format_id il)

let opt_parens b f = if b then parens f else f

let format_ptr = int

let coqrecord f = 
    let coqrecord_item (k, v) = horzOrVert [text (k ^ " :="); v] in 
    enclose "{|" "|}" (horzOrVert (vert_intersperse (text ";") (List.map coqrecord_item f)))

let coqconstr b s fs = opt_parens (not (List.is_empty fs) && b) (wrapBox (text s::fs))

let format_unary_op o = match o with
    | Coq_unary_op_print -> text "unary_op_print"
    | Coq_unary_op_pretty -> text "unary_op_pretty"
    | Coq_unary_op_strlen -> text "unary_op_strlen"
    | Coq_unary_op_typeof -> text "unary_op_typeof"
    | Coq_unary_op_is_primitive -> text "unary_op_is_primitive"
    | Coq_unary_op_is_closure -> text "unary_op_is_closure"
    | Coq_unary_op_is_object -> text "unary_op_is_object"
    | Coq_unary_op_abs -> text "unary_op_abs"
    | Coq_unary_op_floor -> text "unary_op_floor"
    | Coq_unary_op_neg -> text "unary_op_neg"
    | Coq_unary_op_sign -> text "unary_op_sign"
    | Coq_unary_op_prim_to_str -> text "unary_op_prim_to_str"
    | Coq_unary_op_prim_to_num -> text "unary_op_prim_to_num"
    | Coq_unary_op_prim_to_bool -> text "unary_op_prim_to_bool"
    | Coq_unary_op_prim_to_int -> text "unary_op_prim_to_int"
    | Coq_unary_op_not -> text "unary_op_not"
    | Coq_unary_op_bnot -> text "unary_op_bnot"
    | Coq_unary_op_ascii_ntoc -> text "unary_op_ascii_ntoc"
    | Coq_unary_op_ascii_cton -> text "unary_op_ascii_cton"
    | Coq_unary_op_object_to_string -> text "unary_op_object_to_string"
    | Coq_unary_op_ceil -> text "unary_op_ceil"
    | Coq_unary_op_log -> text "unary_op_log"
    | Coq_unary_op_to_lower -> text "unary_op_to_lower"
    | Coq_unary_op_to_upper -> text "unary_op_to_upper"
    | Coq_unary_op_sin -> text "unary_op_sin"
    | Coq_unary_op_current_utc_millis -> text "unary_op_current_utc_millis"

let format_binary_op o = match o with
    | Coq_binary_op_add -> text "binary_op_add"
    | Coq_binary_op_sub -> text "binary_op_sub"
    | Coq_binary_op_mul -> text "binary_op_mul"
    | Coq_binary_op_div -> text "binary_op_div"
    | Coq_binary_op_mod -> text "binary_op_mod"
    | Coq_binary_op_lt -> text "binary_op_lt"
    | Coq_binary_op_le -> text "binary_op_le"
    | Coq_binary_op_gt -> text "binary_op_gt"
    | Coq_binary_op_ge -> text "binary_op_ge"
    | Coq_binary_op_stx_eq -> text "binary_op_stx_eq"
    | Coq_binary_op_same_value -> text "binary_op_same_value"
    | Coq_binary_op_has_own_property -> text "binary_op_has_own_property"
    | Coq_binary_op_has_internal -> text "binary_op_has_internal"
    | Coq_binary_op_string_plus -> text "binary_op_string_plus"
    | Coq_binary_op_char_at -> text "binary_op_char_at"
    | Coq_binary_op_is_accessor -> text "binary_op_is_accessor"
    | Coq_binary_op_band -> text "binary_op_band"
    | Coq_binary_op_bor -> text "binary_op_bor"
    | Coq_binary_op_bxor -> text "binary_op_bxor"
    | Coq_binary_op_shiftl -> text "binary_op_shiftl"
    | Coq_binary_op_shiftr -> text "binary_op_shiftr"
    | Coq_binary_op_zfshiftr -> text "binary_op_zfshiftr"
    | Coq_binary_op_string_lt -> text "binary_op_string_lt"
    | Coq_binary_op_locale_compare -> text "binary_op_locale_compare"
    | Coq_binary_op_base -> text "binary_op_base"
    | Coq_binary_op_pow -> text "binary_op_pow"
    | Coq_binary_op_to_fixed -> text "binary_op_to_fixed"

let format_pattr a = match a with
    | Coq_pattr_value -> text "pattr_value"
    | Coq_pattr_getter -> text "pattr_getter"
    | Coq_pattr_setter -> text "pattr_setter"
    | Coq_pattr_config -> text "pattr_config"
    | Coq_pattr_writable -> text "pattr_writable"
    | Coq_pattr_enum -> text "pattr_enum"

let format_oattr a = match a with
    | Coq_oattr_proto -> text "oattr_proto"
    | Coq_oattr_class -> text "oattr_class"
    | Coq_oattr_extensible -> text "oattr_extensible"
    | Coq_oattr_code -> text "oattr_code"

let format_number n = 
    if n <> n then text "JsNumber.nan"
    else if n = infinity then text "JsNumber.infinity" 
    else if n = -.infinity then text "JsNumber.neg_infinity" 
    else parens (squish [text "JsNumber.of_int ("; int (Float.to_int n); text ")"])

(* TODO modify to give letrecs own identifiers! *)
let rec format_expr b e = match e with
    | Coq_expr_empty -> text "expr_empty"
    | Coq_expr_null -> text "expr_null"
    | Coq_expr_undefined -> text "expr_undefined"
    | Coq_expr_number n -> coqconstr b "expr_number" [format_number n]
    | Coq_expr_int n -> coqconstr b "expr_int" [int (Float.to_int n)]
    | Coq_expr_string s -> coqconstr b "expr_string" [format_id s]
    | Coq_expr_bool true -> text "expr_true"
    | Coq_expr_bool false -> text "expr_false"
    | Coq_expr_id s -> coqconstr b "expr_id" [format_id s]
    | Coq_expr_object (oa, ips, ps) -> coqconstr b "expr_object" [format_objattrs true oa; format_internal_list ips; format_property_list ps]
    | Coq_expr_get_attr (a, e1, e2) -> coqconstr b "expr_get_attr" [format_pattr a; format_expr true e1; format_expr true e2]
    | Coq_expr_set_attr (a, e1, e2, e3) -> coqconstr b "expr_set_attr" [format_pattr a; format_expr true e1; format_expr true e2; format_expr true e3]
    | Coq_expr_get_obj_attr (a, e1) -> coqconstr b "expr_get_obj_attr" [format_oattr a; format_expr true e1]
    | Coq_expr_set_obj_attr (a, e1, e2) -> coqconstr b "expr_set_obj_attr" [format_oattr a; format_expr true e1; format_expr true e2]
    | Coq_expr_delete_field (e1, e2) -> coqconstr b "expr_delete_field" [format_expr true e1; format_expr true e2]
    | Coq_expr_get_internal (a, e1) -> coqconstr b "expr_get_internal" [format_id a; format_expr true e1]
    | Coq_expr_set_internal (a, e1, e2) -> coqconstr b "expr_set_internal" [format_id a; format_expr true e1; format_expr true e2]
    | Coq_expr_own_field_names e -> coqconstr b "expr_own_field_names" [format_expr true e]
    | Coq_expr_op1 (o, e) -> coqconstr b "expr_op1" [format_unary_op o; format_expr true e]
    | Coq_expr_op2 (o, e1, e2) -> coqconstr b "expr_op2" [format_binary_op o; format_expr true e1; format_expr true e2]
    | Coq_expr_if (e1, e2, e3) -> coqconstr b "expr_if" [format_expr true e1; format_expr true e2; format_expr true e3]
    | Coq_expr_app (e, es) -> coqconstr b "expr_app" [format_expr true e; format_list (List.map (format_expr false) es)]
    | Coq_expr_seq (e1, e2) -> coqconstr b "expr_seq" [format_expr true e1; format_expr true e2]
    | Coq_expr_jseq (e1, e2) -> coqconstr b "expr_jseq" [format_expr true e1; format_expr true e2]
    | Coq_expr_let (i, e1, e2) -> coqconstr b "expr_let" [format_id i; format_expr true e1; format_expr true e2]
    | Coq_expr_recc (i, e1, e2) -> coqconstr b "expr_recc" [format_id i; format_expr true e1; format_expr true e2]
    | Coq_expr_label (i, e) -> coqconstr b "expr_label" [format_id i; format_expr true e]
    | Coq_expr_break (i, e) -> coqconstr b "expr_break" [format_id i; format_expr true e]
    | Coq_expr_try_catch (e1, e2) -> coqconstr b "expr_try_catch" [format_expr true e1; format_expr true e2]
    | Coq_expr_try_finally (e1, e2) -> coqconstr b "expr_try_finally" [format_expr true e1; format_expr true e2]
    | Coq_expr_throw e -> coqconstr b "expr_throw" [format_expr true e]
    | Coq_expr_lambda (il, e) -> coqconstr b "expr_lambda" [format_id_list il; format_expr true e]
    | Coq_expr_eval (e1, e2) -> coqconstr b "expr_eval" [format_expr true e1; format_expr true e2]
    | Coq_expr_hint (i, e) -> coqconstr b "expr_hint" [format_id i; format_expr true e]
    | Coq_expr_fail s -> coqconstr b "expr_fail" [format_id s]
    | _ -> text "expr_dump"

and format_objattrs b e = match e with
    | Coq_objattrs_intro (e1, e2, e3, e4) -> coqconstr b "objattrs_intro" (List.map (format_expr true) [e1; e2; e3; e4])

and format_internal_list ps = 
    let format_internal_item (i, e) = parens (squish [format_id i; text ", "; format_expr false e]) in
    format_list (List.map format_internal_item ps)

and format_property_list ps = 
    let format_property_item (i, p) = parens (squish [format_id i; text ", "; format_property false p]) in
    format_list (List.map format_property_item ps)

and format_property b p = match p with
    | Coq_property_data (Coq_data_intro (e1, e2, e3, e4)) -> 
        coqconstr b "property_data" [coqconstr true "data_intro" (List.map (format_expr true) [e1; e2; e3; e4])]
    | Coq_property_accessor (Coq_accessor_intro (e1, e2, e3, e4)) -> 
        coqconstr b "property_accessor" [coqconstr true "accessor_intro" (List.map (format_expr true) [e1; e2; e3; e4])]

let format_option b f o = match o with
    | Some x -> coqconstr b "Some" [f x]
    | None -> coqconstr b "None" []

let rec format_named_val i v = force_value v; text (named_val i v)

and force_value v = match v with
    | Coq_value_closure (Coq_closure_intro (c, rid, is, e)) -> 
        let is' = match rid with Some i -> i::is | None -> is in
        let fvs = expr_fv (Coq_expr_lambda (is', e)) in
        let c' = LibFinmap.FinmapImpl.to_list_impl (LibFinmap.FinmapImpl.restrict_impl (LibFinmap.FinmapImpl.from_list_impl c) fvs) in
        List.iter (fun (i, v) -> ignore (format_named_val i v)) c'
    | _ -> ()
    

let format_value i0 v = match v with
    | Coq_value_empty -> text "value_empty"
    | Coq_value_null -> text "value_null"
    | Coq_value_undefined -> text "value_undefined"
    | Coq_value_number n -> coqconstr false "value_number" [format_number n]
    | Coq_value_string s -> coqconstr false "value_string" [format_id s]
    | Coq_value_bool true -> text "value_true"
    | Coq_value_bool false -> text "value_false"
    | Coq_value_object n -> coqconstr false "value_object" [int n]
    | Coq_value_closure (Coq_closure_intro (c, rid, is, e)) -> 
        let is' = match rid with Some i -> i::is | None -> is in
        let fvs = expr_fv (Coq_expr_lambda (is', e)) in
        let c' = LibFinmap.FinmapImpl.to_list_impl (LibFinmap.FinmapImpl.restrict_impl (LibFinmap.FinmapImpl.from_list_impl c) fvs) in
        let format_ctx_item (i, v) = parens (squish [format_id i; text ", "; format_named_val i v]) in
        coqconstr false "value_closure" [coqconstr true "closure_intro" [format_list (List.map format_ctx_item c'); format_option true format_id rid; format_id_list is; text (named_expr i0 e)]]

let format_attributes a = match a with
    | Coq_attributes_data_of d ->
        let l = [
            "attributes_data_value", format_value "dataval" d.attributes_data_value;
            "attributes_data_writable", bool d.attributes_data_writable;
            "attributes_data_enumerable", bool d.attributes_data_enumerable;
            "attributes_data_configurable", bool d.attributes_data_configurable
        ] in
        horz [text "attributes_data_of"; coqrecord l]
    | Coq_attributes_accessor_of d ->
        let l = [
            "attributes_accessor_get", format_value "getter" d.attributes_accessor_get;
            "attributes_accessor_set", format_value "setter" d.attributes_accessor_set;
            "attributes_accessor_enumerable", bool d.attributes_accessor_enumerable;
            "attributes_accessor_configurable", bool d.attributes_accessor_configurable
        ] in
        horz [text "attributes_accessor_of"; coqrecord l]

let format_object_properties vh = 
    let format_object_properties_item (i, a) = parens (horzOrVert [squish [format_id i; text ", "]; format_attributes a]) in
    horz [text "from_list"; format_list (List.map format_object_properties_item (LibFinmap.FinmapImpl.to_list_impl vh))] 

let format_object_internal vh = 
    let format_object_internal_item (i, v) = parens (horzOrVert [squish [format_id i; text ", "]; format_value "internal" v]) in
    horz [text "from_list"; format_list (List.map format_object_internal_item (LibFinmap.FinmapImpl.to_list_impl vh))] 

let format_object o = 
    let l1 = [
        "oattrs_proto", format_named_val (String.to_list "proto") (object_proto o);
        "oattrs_class", format_id (object_class o);
        "oattrs_extensible", bool (object_extensible o);
        "oattrs_code", format_named_val (String.to_list "objCode") (object_code o)
    ] in
    let l = [
        "object_attrs", coqrecord l1;
        "object_properties", format_object_properties (object_properties o);
        "object_internal", format_object_internal (object_internal o)
    ] in
    coqrecord l

let reserve_ctx_names (c : ctx) = 
    let f (i, v) = reserve_named_val i v in
    List.iter f (LibFinmap.FinmapImpl.to_list_impl c)

let format_ctx (c : ctx) = 
    let format_ctx_item (i, v) = parens (squish [text ("name_"); format_named_val i v; text ", "; format_named_val i v]) in
    format_list (List.map format_ctx_item (LibFinmap.FinmapImpl.to_list_impl c))

let format_ctx_def (c : ctx) = 
    vert [text "Definition ctx_items := "; format_ctx c; text "."]

let format_store (st : store) =
    let format_store_object_item (l, o) = parens (squish [format_ptr l; text ", "; format_object o]) in
    vert ([text "Definition store_items := ["] @ vert_intersperse (text ";") (List.map format_store_object_item (LibFinmap.FinmapImpl.to_list_impl st)) @ [text "]."])

let format_named_exprs () =
    let f (i, e) = horzOrVert [text ("Definition " ^ i ^ " := "); format_expr false e; text "."]
    in vert (List.map f (Map.bindings !named_exprs))

let format_named_vals () = 
    let f (ii, i, v) = vert [
        horzOrVert [text ("Definition " ^ ii ^ " := "); format_value ii v; text "."];
        horz [text ("Definition name_" ^ ii ^ " : id := "); format_id i ; text "."]]
    in vert (List.map f (List.rev !ordered_vals))

let format_object_nums () =
    let g (ii, i, v) = match v with Coq_value_object _ -> true | _ -> false
    and f (ii, i, Coq_value_object n) = horz [text ("Definition ptr_" ^ ii ^ " : object_ptr := "); int n; text "."]
    in vert (List.map f (List.filter g (List.rev !ordered_vals)))

let format_ctx_mems c =
    let format_ctx_mem (l, m) (i, v) = 
        let ii = Map.find v !vals_store in
        let f = squish [text ("Definition Mem_" ^ ii ^ " : Mem ("); text ("name_" ^ ii); text ", "; text ii; text ") ctx_items := "; m; text "."] in
        (f :: l, coqconstr true "Mem_next" [text "_"; m]) in
    vert (List.rev ((fst (List.fold_left format_ctx_mem ([], text "(Mem_here _ _)") (LibFinmap.FinmapImpl.to_list_impl c)))))

let format_ctx_red c = 
    let format_ctx_item (k, v) =
        let ii = Map.find v !vals_store in text ii in
    let stuff = List.map format_ctx_item (LibFinmap.FinmapImpl.to_list_impl c) in
    horzOrVert ([text ("Ltac ctx_compute := cbv beta iota zeta delta -[")] @ List.map format_ctx_item (LibFinmap.FinmapImpl.to_list_impl c) @ [text "].";
                 text ("Ltac ctx_compute_in H := cbv beta iota zeta delta -[from_list ")] @ List.map format_ctx_item (LibFinmap.FinmapImpl.to_list_impl c) @ [text "] in H."])

let header () = vert (List.map text [
    "Require Import Utils.";
    "Require Import LjsShared.";
    "Require Import LjsSyntax.";
    "Require Import String.";

    "Import ListNotations.";
    "Open Scope list_scope.";
    "Open Scope string_scope."])

let format_ctx_store (c, st) = 
    reserve_ctx_names c;
    let fst = format_store st in
    let fctx = format_ctx_def c in
    let fnv = format_named_vals () in
    vert [header(); format_object_nums(); format_named_exprs(); fnv; fctx; format_ctx_red c; (* format_ctx_mems c;*) fst; 
          text "Definition init_ctx : ctx := from_list ctx_items.\nDefinition init_store : store := from_list store_items."]

let ctx_store_to_output o c st = 
    Format.set_margin 200;
    Format.set_max_indent 50;
    to_output o format_ctx_store (c, st)

