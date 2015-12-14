
open Batteries

module Ljs = Ljs_syntax
module Cs = LjsSyntax

let translate_oattr o = match o with
    | Ljs.Proto -> Cs.Coq_oattr_proto
    | Ljs.Klass -> Cs.Coq_oattr_class
    | Ljs.Extensible -> Cs.Coq_oattr_extensible
    | Ljs.Code -> Cs.Coq_oattr_code

let translate_pattr p = match p with
    | Ljs.Value -> Cs.Coq_pattr_value
    | Ljs.Getter -> Cs.Coq_pattr_getter
    | Ljs.Setter -> Cs.Coq_pattr_setter
    | Ljs.Config -> Cs.Coq_pattr_config
    | Ljs.Writable -> Cs.Coq_pattr_writable
    | Ljs.Enum -> Cs.Coq_pattr_enum

let translate_unary_op s = match s with
    | "typeof" -> Cs.Coq_unary_op_typeof
    | "closure?" -> Cs.Coq_unary_op_is_closure
    | "primitive?" -> Cs.Coq_unary_op_is_primitive
    | "object?" -> Cs.Coq_unary_op_is_object
    | "prim->str" -> Cs.Coq_unary_op_prim_to_str
    | "prim->num" -> Cs.Coq_unary_op_prim_to_num
    | "prim->bool" -> Cs.Coq_unary_op_prim_to_bool
    | "prim->int" -> Cs.Coq_unary_op_prim_to_int
    | "print" -> Cs.Coq_unary_op_print
    | "pretty" -> Cs.Coq_unary_op_pretty
    | "object-to-string" -> Cs.Coq_unary_op_object_to_string
    | "strlen" -> Cs.Coq_unary_op_strlen
    | "!" -> Cs.Coq_unary_op_not
    | "floor" -> Cs.Coq_unary_op_floor
    | "-" -> Cs.Coq_unary_op_neg
    | "ceil" -> Cs.Coq_unary_op_ceil
    | "abs" -> Cs.Coq_unary_op_abs
    | "sign" -> Cs.Coq_unary_op_sign
    | "log" -> Cs.Coq_unary_op_log
    | "ascii_ntoc" -> Cs.Coq_unary_op_ascii_ntoc
    | "ascii_cton" -> Cs.Coq_unary_op_ascii_cton
    | "to-lower" -> Cs.Coq_unary_op_to_lower
    | "to-upper" -> Cs.Coq_unary_op_to_upper
    | "~" -> Cs.Coq_unary_op_bnot
    | "sin" -> Cs.Coq_unary_op_sin
    | "current-utc-millis" -> Cs.Coq_unary_op_current_utc_millis
    | _ -> failwith "operator not implemented"

let translate_binary_op s = match s with
    | "+" -> Cs.Coq_binary_op_add
    | "-" -> Cs.Coq_binary_op_sub
    | "/" -> Cs.Coq_binary_op_div
    | "*" -> Cs.Coq_binary_op_mul
    | "%" -> Cs.Coq_binary_op_mod
    | "&" -> Cs.Coq_binary_op_band
    | "|" -> Cs.Coq_binary_op_bor
    | "^" -> Cs.Coq_binary_op_bxor
    | "<<" -> Cs.Coq_binary_op_shiftl
    | ">>" -> Cs.Coq_binary_op_shiftr
    | ">>>" -> Cs.Coq_binary_op_zfshiftr
    | "<" -> Cs.Coq_binary_op_lt
    | "<=" -> Cs.Coq_binary_op_le
    | ">" -> Cs.Coq_binary_op_gt
    | ">=" -> Cs.Coq_binary_op_ge
    | "stx=" -> Cs.Coq_binary_op_stx_eq
    | "sameValue" -> Cs.Coq_binary_op_same_value
    | "hasOwnProperty" -> Cs.Coq_binary_op_has_own_property
    | "hasInternal" -> Cs.Coq_binary_op_has_internal
    | "string+" -> Cs.Coq_binary_op_string_plus
    | "string<" -> Cs.Coq_binary_op_string_lt
    | "base" -> Cs.Coq_binary_op_base
    | "char-at" -> Cs.Coq_binary_op_char_at
    | "locale-compare" -> Cs.Coq_binary_op_locale_compare
    | "pow" -> Cs.Coq_binary_op_pow
    | "to-fixed" -> Cs.Coq_binary_op_to_fixed
    | "isAccessor" -> Cs.Coq_binary_op_is_accessor
    | _ -> failwith "operator not implemented"

let translate_bool b = Cs.Coq_expr_bool b 

let rec translate_expr e = match e with
    | Ljs.Empty _ -> Cs.Coq_expr_empty
    | Ljs.Null _ -> Cs.Coq_expr_null
    | Ljs.Undefined _ -> Cs.Coq_expr_undefined
    | Ljs.String (_, s) -> Cs.Coq_expr_string (String.to_list s)
    | Ljs.Num (_, n) -> Cs.Coq_expr_number n
    | Ljs.Int (_, n) -> Cs.Coq_expr_int (float_of_int n)
    | Ljs.True _ -> Cs.Coq_expr_bool true
    | Ljs.False _ -> Cs.Coq_expr_bool false
    | Ljs.Id (_, i) -> Cs.Coq_expr_id (String.to_list i)
    | Ljs.Object (_, a, l1, l2) -> Cs.Coq_expr_object (translate_attrs a, List.map (function (x, y) -> (String.to_list x, translate_expr y)) l1, 
        List.map (function (x, y) -> (String.to_list x, translate_prop y)) l2)
    | Ljs.GetAttr (_, p, e1, e2) -> Cs.Coq_expr_get_attr (translate_pattr p, translate_expr e1, translate_expr e2)
    | Ljs.SetAttr (_, p, e1, e2, e3) -> Cs.Coq_expr_set_attr (translate_pattr p, translate_expr e1, translate_expr e2, translate_expr e3)
    | Ljs.GetObjAttr (_, p, e) -> Cs.Coq_expr_get_obj_attr (translate_oattr p, translate_expr e)
    | Ljs.SetObjAttr (_, p, e1, e2) -> Cs.Coq_expr_set_obj_attr (translate_oattr p, translate_expr e1, translate_expr e2)
    | Ljs.DeleteField (_, e, e1) -> Cs.Coq_expr_delete_field (translate_expr e, translate_expr e1)
    | Ljs.GetInternal (_, s, e) -> Cs.Coq_expr_get_internal (String.to_list s, translate_expr e)
    | Ljs.SetInternal (_, s, e1, e2) -> Cs.Coq_expr_set_internal (String.to_list s, translate_expr e1, translate_expr e2)
    | Ljs.OwnFieldNames (_, e) -> Cs.Coq_expr_own_field_names (translate_expr e)
    | Ljs.Op1 (_, i, e) -> Cs.Coq_expr_op1 (translate_unary_op i, translate_expr e)
    | Ljs.Op2 (_, i, e1, e2) -> Cs.Coq_expr_op2 (translate_binary_op i, translate_expr e1, translate_expr e2)
    | Ljs.If (_, e, e1, e2) -> Cs.Coq_expr_if (translate_expr e, translate_expr e1, translate_expr e2)
    | Ljs.App (_, e, es) -> Cs.Coq_expr_app (translate_expr e, List.map translate_expr es)
    | Ljs.Seq (_, e1, e2) -> Cs.Coq_expr_seq (translate_expr e1, translate_expr e2)
    | Ljs.JSeq (_, e1, e2) -> Cs.Coq_expr_jseq (translate_expr e1, translate_expr e2)
    | Ljs.Let (_, i, e1, e2) -> Cs.Coq_expr_let (String.to_list i, translate_expr e1, translate_expr e2)
    | Ljs.Rec (_, i, e1, e2) -> Cs.Coq_expr_recc (String.to_list i, translate_expr e1, translate_expr e2)
    | Ljs.Label (_, i, e) -> Cs.Coq_expr_label (String.to_list i, translate_expr e)
    | Ljs.Break (_, i, e) -> Cs.Coq_expr_break (String.to_list i, translate_expr e)
    | Ljs.TryCatch (_, e1, e2) -> Cs.Coq_expr_try_catch (translate_expr e1, translate_expr e2)
    | Ljs.TryFinally (_, e1, e2) -> Cs.Coq_expr_try_finally (translate_expr e1, translate_expr e2)
    | Ljs.Throw (_, e) -> Cs.Coq_expr_throw (translate_expr e)
    | Ljs.Lambda (_, is, e) -> Cs.Coq_expr_lambda (List.map String.to_list is, translate_expr e)
    | Ljs.Eval (_, e1, e2) -> Cs.Coq_expr_eval (translate_expr e1, translate_expr e2)
    | Ljs.Hint (_, i, e) -> Cs.Coq_expr_hint (String.to_list i, translate_expr e)
    | Ljs.Fail (_, s) -> Cs.Coq_expr_fail (String.to_list s)
    | Ljs.Dump -> Cs.Coq_expr_dump
and translate_data d e c = Cs.Coq_data_intro (translate_expr d.Ljs.value, translate_bool d.Ljs.writable, translate_bool e, translate_bool c)
and translate_accessor a e c = Cs.Coq_accessor_intro (translate_expr a.Ljs.getter, translate_expr a.Ljs.setter, translate_bool e, translate_bool c)
and translate_prop p = match p with
    | Ljs.Data (d, e, c) -> Cs.Coq_property_data (translate_data d e c)
    | Ljs.Accessor (a, e, c) -> Cs.Coq_property_accessor (translate_accessor a e c)
and translate_attrs a = Cs.Coq_objattrs_intro 
    (Cs.Coq_expr_string (String.to_list a.Ljs.klass), 
     translate_bool a.Ljs.extensible,
     Option.map_default translate_expr (Cs.Coq_expr_null) a.Ljs.proto, 
     Option.map_default translate_expr (Cs.Coq_expr_undefined) a.Ljs.code
     )
