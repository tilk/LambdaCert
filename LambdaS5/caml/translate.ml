
open Batteries

module Ljs = Ljs_syntax
module Cs = Syntax

let translate_oattr o = match o with
    | Ljs.Proto -> Cs.Coq_oattr_proto
    | Ljs.Klass -> Cs.Coq_oattr_class
    | Ljs.Extensible -> Cs.Coq_oattr_extensible
    | Ljs.Primval -> Cs.Coq_oattr_primval
    | Ljs.Code -> Cs.Coq_oattr_code

let translate_pattr p = match p with
    | Ljs.Value -> Cs.Coq_pattr_value
    | Ljs.Getter -> Cs.Coq_pattr_getter
    | Ljs.Setter -> Cs.Coq_pattr_setter
    | Ljs.Config -> Cs.Coq_pattr_config
    | Ljs.Writable -> Cs.Coq_pattr_writable
    | Ljs.Enum -> Cs.Coq_pattr_enum

let rec translate_expr e = match e with
    | Ljs.Null _ -> Cs.Coq_expr_null
    | Ljs.Undefined _ -> Cs.Coq_expr_undefined
    | Ljs.String (_, s) -> Cs.Coq_expr_string (String.to_list s)
    | Ljs.Num (_, n) -> Cs.Coq_expr_number n
    | Ljs.True _ -> Cs.Coq_expr_true
    | Ljs.False _ -> Cs.Coq_expr_false
    | Ljs.Id (_, i) -> Cs.Coq_expr_id (String.to_list i)
    | Ljs.Object (_, a, l) -> Cs.Coq_expr_object (translate_attrs a, List.map (function (x, y) -> (String.to_list x, translate_prop y)) l)
    | Ljs.GetAttr (_, p, e1, e2) -> Cs.Coq_expr_get_attr (translate_pattr p, translate_expr e1, translate_expr e2)
    | Ljs.SetAttr (_, p, e1, e2, e3) -> Cs.Coq_expr_set_attr (translate_pattr p, translate_expr e1, translate_expr e2, translate_expr e3)
    | Ljs.GetObjAttr (_, p, e) -> Cs.Coq_expr_get_obj_attr (translate_oattr p, translate_expr e)
    | Ljs.SetObjAttr (_, p, e1, e2) -> Cs.Coq_expr_set_obj_attr (translate_oattr p, translate_expr e1, translate_expr e2)
    | Ljs.GetField (_, e, e1, e2) -> Cs.Coq_expr_get_field (translate_expr e, translate_expr e1, translate_expr e2)
    | Ljs.SetField (_, e, e1, e2, e3) -> Cs.Coq_expr_set_field (translate_expr e, translate_expr e1, translate_expr e2, translate_expr e3)
    | Ljs.DeleteField (_, e, e1) -> Cs.Coq_expr_delete_field (translate_expr e, translate_expr e1)
    | Ljs.OwnFieldNames (_, e) -> Cs.Coq_expr_own_field_names (translate_expr e)
    | Ljs.SetBang (_, i, e) -> Cs.Coq_expr_set_bang (String.to_list i, translate_expr e)
    | Ljs.Op1 (_, i, e) -> Cs.Coq_expr_op1 (String.to_list i, translate_expr e)
    | Ljs.Op2 (_, i, e1, e2) -> Cs.Coq_expr_op2 (String.to_list i, translate_expr e1, translate_expr e2)
    | Ljs.If (_, e, e1, e2) -> Cs.Coq_expr_if (translate_expr e, translate_expr e1, translate_expr e2)
    | Ljs.App (_, e, es) -> Cs.Coq_expr_app (translate_expr e, List.map translate_expr es)
    | Ljs.Seq (_, e1, e2) -> Cs.Coq_expr_seq (translate_expr e1, translate_expr e2)
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
and translate_data d = Cs.Coq_data_intro (translate_expr d.Ljs.value, d.Ljs.writable)
and translate_accessor a = Cs.Coq_accessor_intro (translate_expr a.Ljs.getter, translate_expr a.Ljs.setter)
and translate_prop p = match p with
    | Ljs.Data (d, e, c) -> Cs.Coq_property_data (translate_data d, e, c)
    | Ljs.Accessor (a, e, c) -> Cs.Coq_property_accessor (translate_accessor a, e, c)
and translate_attrs a = Cs.Coq_objattrs_intro 
    (Option.map translate_expr a.Ljs.primval, 
     Option.map translate_expr a.Ljs.code, 
     Option.map translate_expr a.Ljs.proto, 
     String.to_list a.Ljs.klass, 
     a.Ljs.extensible)

