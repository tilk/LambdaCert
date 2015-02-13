
open Batteries
open Format
open FormatExt
open HeapUtils
open LjsSyntax

let format_id i = text ("\"" ^ String.of_list i ^ "\"") (* TODO escaping *)

let format_list l = brackets (horzOrVert (vert_intersperse (text ";") l))

let format_id_list il = format_list (List.map format_id il)

let format_loc k = int k

let format_ctx (c : ctx) = 
    let format_ctx_item (i, l) = parens (squish [format_id i; text ", "; format_loc l]) in
    format_list (List.map format_ctx_item (Heap.to_list c))

let opt_parens b f = if b then parens f else f

let coqrecord f = 
    let coqrecord_item (k, v) = horz [text k; text ":="; v] in 
    enclose "{|" "|}" (horzOrVert (vert_intersperse (text ";") (List.map coqrecord_item f)))

let format_unary_op o = match o with
    | Coq_unary_op_print -> text "unary_op_print"
    | Coq_unary_op_pretty -> text "unary_op_pretty"
    | Coq_unary_op_strlen -> text "unary_op_strlen"
    | Coq_unary_op_typeof -> text "unary_op_typeof"
    | Coq_unary_op_is_primitive -> text "unary_op_is_primitive"
    | Coq_unary_op_is_closure -> text "unary_op_is_closure"
    | Coq_unary_op_is_array -> text "unary_op_is_array"
    | Coq_unary_op_abs -> text "unary_op_abs"
    | Coq_unary_op_void -> text "unary_op_void"
    | Coq_unary_op_floor -> text "unary_op_floor"
    | Coq_unary_op_prim_to_str -> text "unary_op_prim_to_str"
    | Coq_unary_op_prim_to_num -> text "unary_op_prim_to_num"
    | Coq_unary_op_prim_to_bool -> text "unary_op_prim_to_bool"
    | Coq_unary_op_not -> text "unary_op_not"
    | Coq_unary_op_bnot -> text "unary_op_bnot"
    | Coq_unary_op_numstr_to_num -> text "unary_op_numstr_to_num"
    | Coq_unary_op_to_int32 -> text "unary_op_to_int32"
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
    | Coq_binary_op_abs_eq -> text "binary_op_abs_eq"
    | Coq_binary_op_same_value -> text "binary_op_same_value"
    | Coq_binary_op_has_property -> text "binary_op_has_property"
    | Coq_binary_op_has_own_property -> text "binary_op_has_own_property"
    | Coq_binary_op_string_plus -> text "binary_op_string_plus"
    | Coq_binary_op_char_at -> text "binary_op_char_at"
    | Coq_binary_op_is_accessor -> text "binary_op_is_accessor"
    | Coq_binary_op_prop_to_obj -> text "binary_op_prop_to_obj"
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
    | Coq_oattr_primval -> text "oattr_primval"
    | Coq_oattr_code -> text "oattr_code"

let coqconstr b s fs = opt_parens (not (List.is_empty fs) && b) (wrapBox (text s::fs))

let rec format_expr b e = match e with
    | Coq_expr_null -> text "expr_null"
    | Coq_expr_undefined -> text "expr_undefined"
    | Coq_expr_number n -> coqconstr b "expr_number" [float n]
    | Coq_expr_string s -> coqconstr b "expr_string" [format_id s]
    | Coq_expr_true -> text "expr_true"
    | Coq_expr_false -> text "expr_false"
    | Coq_expr_id s -> coqconstr b "expr_id" [format_id s]
    | Coq_expr_object (oa, ps) -> coqconstr b "expr_object" [format_objattrs true oa; format_property_list ps]
    | Coq_expr_get_attr (a, e1, e2) -> coqconstr b "expr_get_attr" [format_pattr a; format_expr true e1; format_expr true e2]
    | Coq_expr_set_attr (a, e1, e2, e3) -> coqconstr b "expr_set_attr" [format_pattr a; format_expr true e1; format_expr true e2; format_expr true e3]
    | Coq_expr_get_obj_attr (a, e1) -> coqconstr b "expr_get_obj_attr" [format_oattr a; format_expr true e1]
    | Coq_expr_set_obj_attr (a, e1, e2) -> coqconstr b "expr_set_obj_attr" [format_oattr a; format_expr true e1; format_expr true e2]
    | Coq_expr_get_field (e1, e2, e3) -> coqconstr b "expr_get_field" [format_expr true e1; format_expr true e2; format_expr true e3]
    | Coq_expr_set_field (e1, e2, e3, e4) -> coqconstr b "expr_set_field" [format_expr true e1; format_expr true e2; format_expr true e3; format_expr true e4]
    | Coq_expr_delete_field (e1, e2) -> coqconstr b "expr_delete_field" [format_expr true e1; format_expr true e2]
    | Coq_expr_own_field_names e -> coqconstr b "expr_own_field_names" [format_expr true e]
    | Coq_expr_set_bang (i, e) -> coqconstr b "expr_set_bang" [format_id i; format_expr true e]
    | Coq_expr_op1 (o, e) -> coqconstr b "expr_op1" [format_unary_op o; format_expr true e]
    | Coq_expr_op2 (o, e1, e2) -> coqconstr b "expr_op2" [format_binary_op o; format_expr true e1; format_expr true e2]
    | Coq_expr_if (e1, e2, e3) -> coqconstr b "expr_if" [format_expr true e1; format_expr true e2; format_expr true e3]
    | Coq_expr_app (e, es) -> coqconstr b "expr_app" [format_expr true e; format_list (List.map (format_expr false) es)]
    | Coq_expr_seq (e1, e2) -> coqconstr b "expr_seq" [format_expr true e1; format_expr true e2]
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
    | _ -> text "expr_dump"

and format_objattrs b e = match e with
    | Coq_objattrs_intro (e1, e2, e3, e4, e5) -> coqconstr b "objattrs_intro" (List.map (format_expr true) [e1; e2; e3; e4; e5])

and format_property_list ps = 
    let format_property_item (i, p) = squish [format_id i; text ", "; format_property true p] in
    format_list (List.map format_property_item ps)

and format_property b p = match p with
    | Coq_property_data (Coq_data_intro (e1, e2, e3, e4)) -> 
        coqconstr b "property_data" [coqconstr true "data_intro" (List.map (format_expr true) [e1; e2; e3; e4])]
    | Coq_property_accessor (Coq_accessor_intro (e1, e2, e3, e4)) -> 
        coqconstr b "property_accessor" [coqconstr true "accessor_intro" (List.map (format_expr true) [e1; e2; e3; e4])]

let format_value v = match v with
    | Coq_value_null -> text "value_null"
    | Coq_value_undefined -> text "value_undefined"
    | Coq_value_number n -> coqconstr false "value_number" [float n]
    | Coq_value_string s -> coqconstr false "value_string" [format_id s]
    | Coq_value_true -> text "value_true"
    | Coq_value_false -> text "value_false"
    | Coq_value_object n -> coqconstr false "value_object" [int n]
    | Coq_value_closure (i, c, is, e) -> coqconstr false "value_closure" [int i; format_ctx c; format_id_list is; format_expr true e]

let format_value_heap vh = 
    let format_value_heap_item (l, v) = parens (squish [format_loc l; text ", "; format_value v]) in
    format_list (List.map format_value_heap_item (Heap.to_list vh))

let format_attributes a = match a with
    | Coq_attributes_data_of d ->
        let l = [
            "attributes_data_value", format_value d.attributes_data_value;
            "attributes_data_writable", bool d.attributes_data_writable;
            "attributes_data_enumerable", bool d.attributes_data_enumerable;
            "attributes_data_configurable", bool d.attributes_data_configurable
        ] in
        horz [text "attributes_data_of"; coqrecord l]
    | Coq_attributes_accessor_of d ->
        let l = [
            "attributes_accessor_get", format_value d.attributes_accessor_get;
            "attributes_accessor_set", format_value d.attributes_accessor_set;
            "attributes_accessor_enumerable", bool d.attributes_accessor_enumerable;
            "attributes_accessor_configurable", bool d.attributes_accessor_configurable
        ] in
        horz [text "attributes_accessor_of"; coqrecord l]

let format_object_properties vh = 
    let format_object_properties_item (i, a) = parens (squish [format_id i; text ", "; format_attributes a]) in
    horz [text "Heap.of_list"; format_list (List.map format_object_properties_item (Heap.to_list vh))] 

let format_object o = 
    let l = [
        "object_proto", format_value o.object_proto;
        "object_class", format_id o.object_class;
        "object_extensible", bool o.object_extensible;
        "object_prim_value", format_value o.object_prim_value;
        "object_properties_", format_object_properties o.object_properties_; 
        "object_code", format_value o.object_code
    ] in
    coqrecord l

let format_ctx_def (c : ctx) = 
    vert [text "Definition ctx_items := "; format_ctx c; text "."]

let format_store (st : store) =
    let format_store_object_item (l, o) = squish [parens (squish [format_loc l; text ", "; format_object o]); text ";"] in
    vert ([text "Definition store_value_items := "; format_value_heap st.value_heap; text "."; text "Definition store_object_items := ["] @ List.map format_store_object_item (Heap.to_list (st.object_heap)) @ [text "]."])

let format_ctx_store (c, st) = vert [format_ctx_def c; format_store st]

let ctx_store_to_output o c st = to_output o format_ctx_store (c, st)
