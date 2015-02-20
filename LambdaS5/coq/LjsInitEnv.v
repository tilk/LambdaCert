Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import String.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Definition objCode :=  value_null .
Definition privJSError := 
value_closure
(closure_intro [] None ["err"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
   expr_undefined)
  [("%js-exn", property_data
               (data_intro (expr_id "err") expr_false expr_false expr_false))]))
.
Definition privTypeErrorProto :=  value_object 8 .
Definition privMakeTypeError := 
value_closure
(closure_intro [("%TypeErrorProto", privTypeErrorProto)] None ["msg"]
 (expr_let "msg"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "msg"))
    (expr_string "object")) (expr_string "object passed to ThrowTypeError")
   (expr_op1 unary_op_prim_to_str (expr_id "msg")))
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true
    (expr_id "%TypeErrorProto") expr_null expr_undefined)
   [("message", property_data
                (data_intro (expr_id "msg") expr_false expr_false expr_false))])))
.
Definition privThrowTypeErrorFun := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%MakeTypeError", privMakeTypeError)] None
 ["this"; "args"]
 (expr_let "msg" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_throw
   (expr_app (expr_id "%JSError")
    [expr_app (expr_id "%MakeTypeError") [expr_id "msg"]]))))
.
Definition privTypeError := 
value_closure
(closure_intro [("%ThrowTypeErrorFun", privThrowTypeErrorFun)] None ["msg"]
 (expr_app (expr_id "%ThrowTypeErrorFun")
  [expr_undefined;
   expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined)
   [("0", property_data
          (data_intro (expr_id "msg") expr_false expr_false expr_false))]]))
.
Definition privAppExprCheck := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["fun"; "this"; "args"]
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "fun"))
    (expr_string "function")) expr_false expr_true)
  (expr_app (expr_id "%TypeError") [expr_string "Not a function"])
  (expr_app (expr_id "fun") [expr_id "this"; expr_id "args"])))
.
Definition privArrayProto :=  value_object 59 .
Definition privRangeErrorProto :=  value_object 51 .
Definition privToPrimitiveNum := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"]
 (expr_let "check"
  (expr_lambda ["o"; "str"]
   (expr_let "valueOf" (expr_get_field (expr_id "o") (expr_id "str"))
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_typeof (expr_id "valueOf")) (expr_string "function"))
     (expr_let "str"
      (expr_app (expr_id "valueOf")
       [expr_id "o";
        expr_object
        (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
         expr_undefined) []])
      (expr_if (expr_op1 unary_op_is_primitive (expr_id "str"))
       (expr_id "str") expr_null)) expr_null)))
  (expr_let "r1"
   (expr_app (expr_id "check") [expr_id "obj"; expr_string "valueOf"])
   (expr_if
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "r1") expr_null) expr_false
     expr_true) (expr_id "r1")
    (expr_let "r2"
     (expr_app (expr_id "check") [expr_id "obj"; expr_string "toString"])
     (expr_if
      (expr_if (expr_op2 binary_op_stx_eq (expr_id "r2") expr_null)
       expr_false expr_true) (expr_id "r2")
      (expr_app (expr_id "%TypeError")
       [expr_string "valueOf and toString both absent in toPrimitiveNum"])))))))
.
Definition privToNumber := 
value_closure
(closure_intro [("%ToPrimitiveNum", privToPrimitiveNum)] None ["x"]
 (expr_recc "inner"
  (expr_lambda ["x"]
   (expr_label "ret"
    (expr_let "t" (expr_op1 unary_op_typeof (expr_id "x"))
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "number"))
       (expr_break "ret" (expr_id "x")) expr_undefined)
      (expr_seq
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
        (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_undefined)
       (expr_seq
        (expr_if
         (expr_let "%or" (expr_op2 binary_op_stx_eq (expr_id "x") expr_null)
          (expr_if (expr_id "%or") (expr_id "%or")
           (expr_op2 binary_op_stx_eq (expr_id "x") expr_false)))
         (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_undefined)
        (expr_seq
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") expr_true)
          (expr_break "ret" (expr_number (JsNumber.of_int 1))) expr_undefined)
         (expr_seq
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "string"))
           (expr_break "ret" (expr_op1 unary_op_numstr_to_num (expr_id "x")))
           expr_undefined)
          (expr_break "ret"
           (expr_app (expr_id "inner")
            [expr_app (expr_id "%ToPrimitiveNum") [expr_id "x"]]))))))))))
  (expr_app (expr_id "inner") [expr_id "x"])))
.
Definition privToUint := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["n"; "limit"]
 (expr_let "number" (expr_app (expr_id "%ToNumber") [expr_id "n"])
  (expr_if
   (expr_let "%or"
    (expr_let "%or"
     (expr_let "%or"
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "number") (expr_id "number"))
       expr_false expr_true)
      (expr_if (expr_id "%or") (expr_id "%or")
       (expr_op2 binary_op_stx_eq (expr_id "number")
        (expr_number (JsNumber.of_int 0)))))
     (expr_if (expr_id "%or") (expr_id "%or")
      (expr_op2 binary_op_stx_eq (expr_id "number")
       (expr_number (JsNumber.of_int 0)))))
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_stx_eq (expr_id "number")
      (expr_number (JsNumber.of_int 0))))) (expr_number (JsNumber.of_int 0))
   (expr_let "sign"
    (expr_if
     (expr_op2 binary_op_lt (expr_id "number")
      (expr_number (JsNumber.of_int 0)))
     (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
      (expr_number (JsNumber.of_int 1))) (expr_number (JsNumber.of_int 1)))
    (expr_let "posInt"
     (expr_op2 binary_op_mul (expr_id "sign")
      (expr_op1 unary_op_floor (expr_op1 unary_op_abs (expr_id "number"))))
     (expr_if
      (expr_op2 binary_op_lt (expr_id "sign")
       (expr_number (JsNumber.of_int 0)))
      (expr_let "close"
       (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))
       (expr_op2 binary_op_add (expr_id "close") (expr_id "limit")))
      (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))))))))
.
Definition privToUint32 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"]
 (expr_app (expr_id "%ToUint")
  [expr_id "n"; expr_number (JsNumber.of_int 4294967296)]))
.
Definition privMakeGetter := 
value_closure
(closure_intro [] None ["f"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_false expr_null
   (expr_lambda ["this"]
    (expr_app (expr_id "f")
     [expr_id "this";
      expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined) []])) expr_undefined)
  [("func", property_data
            (data_intro (expr_id "f") expr_false expr_false expr_false))]))
.
Definition privMakeSetter := 
value_closure
(closure_intro [] None ["f"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_false expr_null
   (expr_lambda ["this"; "arg"]
    (expr_app (expr_id "f")
     [expr_id "this";
      expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined)
      [("0", property_data
             (data_intro (expr_id "arg") expr_false expr_false expr_false))]]))
   expr_undefined)
  [("func", property_data
            (data_intro (expr_id "f") expr_false expr_false expr_false))]))
.
Definition privToBoolean := 
value_closure
(closure_intro [] None ["x"] (expr_op1 unary_op_prim_to_bool (expr_id "x")))
.
Definition privToPrimitiveStr := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"]
 (expr_label "ret"
  (expr_seq
   (expr_let "toString"
    (expr_get_field (expr_id "obj") (expr_string "toString"))
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_typeof (expr_id "toString"))
      (expr_string "function"))
     (expr_let "str"
      (expr_app (expr_id "toString")
       [expr_id "obj";
        expr_object
        (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
         expr_undefined) []])
      (expr_if (expr_op1 unary_op_is_primitive (expr_id "str"))
       (expr_break "ret" (expr_id "str")) expr_null)) expr_undefined))
   (expr_seq
    (expr_let "valueOf"
     (expr_get_field (expr_id "obj") (expr_string "valueOf"))
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_op1 unary_op_typeof (expr_id "valueOf"))
       (expr_string "function"))
      (expr_let "str"
       (expr_app (expr_id "valueOf")
        [expr_id "obj";
         expr_object
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined) []])
       (expr_if (expr_op1 unary_op_is_primitive (expr_id "str"))
        (expr_break "ret" (expr_id "str")) expr_null)) expr_undefined))
    (expr_app (expr_id "%TypeError")
     [expr_string "valueOf and toString both absent in toPrimitiveStr"])))))
.
Definition privToPrimitiveHint := 
value_closure
(closure_intro
 [("%ToPrimitiveNum", privToPrimitiveNum);
  ("%ToPrimitiveStr", privToPrimitiveStr)] None ["val"; "hint"]
 (expr_let "t" (expr_op1 unary_op_typeof (expr_id "val"))
  (expr_if
   (expr_let "%or"
    (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))))
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "hint") (expr_string "string"))
    (expr_app (expr_id "%ToPrimitiveStr") [expr_id "val"])
    (expr_app (expr_id "%ToPrimitiveNum") [expr_id "val"])) (expr_id "val"))))
.
Definition privToString := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 (expr_op1 unary_op_prim_to_str
  (expr_app (expr_id "%ToPrimitiveHint")
   [expr_id "val"; expr_string "string"])))
.
Definition copy_when_defined := 
value_closure
(closure_intro [] None ["obj1"; "obj2"; "s"]
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_get_field (expr_id "obj2") (expr_id "s"))
    expr_undefined) expr_false expr_true)
  (expr_let "$newVal" (expr_get_field (expr_id "obj2") (expr_id "s"))
   (expr_set_field (expr_id "obj1") (expr_id "s") (expr_id "$newVal")))
  expr_undefined))
.
Definition copy_access_desc := 
value_closure
(closure_intro [("copy-when-defined", copy_when_defined)] None
 ["obj1"; "obj2"]
 (expr_seq
  (expr_app (expr_id "copy-when-defined")
   [expr_id "obj1"; expr_id "obj2"; expr_string "configurable"])
  (expr_seq
   (expr_app (expr_id "copy-when-defined")
    [expr_id "obj1"; expr_id "obj2"; expr_string "enumerable"])
   (expr_seq
    (expr_app (expr_id "copy-when-defined")
     [expr_id "obj1"; expr_id "obj2"; expr_string "set"])
    (expr_seq
     (expr_app (expr_id "copy-when-defined")
      [expr_id "obj1"; expr_id "obj2"; expr_string "get"])
     (expr_seq (expr_delete_field (expr_id "obj1") (expr_string "value"))
      (expr_delete_field (expr_id "obj1") (expr_string "writable"))))))))
.
Definition copy_data_desc := 
value_closure
(closure_intro [("copy-when-defined", copy_when_defined)] None
 ["obj1"; "obj2"]
 (expr_seq
  (expr_app (expr_id "copy-when-defined")
   [expr_id "obj1"; expr_id "obj2"; expr_string "configurable"])
  (expr_seq
   (expr_app (expr_id "copy-when-defined")
    [expr_id "obj1"; expr_id "obj2"; expr_string "enumerable"])
   (expr_seq
    (expr_app (expr_id "copy-when-defined")
     [expr_id "obj1"; expr_id "obj2"; expr_string "writable"])
    (expr_seq
     (expr_app (expr_id "copy-when-defined")
      [expr_id "obj1"; expr_id "obj2"; expr_string "value"])
     (expr_seq (expr_delete_field (expr_id "obj1") (expr_string "get"))
      (expr_delete_field (expr_id "obj1") (expr_string "set"))))))))
.
Definition isAccessorDescriptor := 
value_closure
(closure_intro [] None ["attr-obj"]
 (expr_let "%or"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_op1 unary_op_typeof
     (expr_get_field (expr_id "attr-obj") (expr_string "set")))
    (expr_string "undefined")) expr_false expr_true)
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_op1 unary_op_typeof
      (expr_get_field (expr_id "attr-obj") (expr_string "get")))
     (expr_string "undefined")) expr_false expr_true))))
.
Definition isDataDescriptor := 
value_closure
(closure_intro [] None ["attr-obj"]
 (expr_let "%or"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_op1 unary_op_typeof
     (expr_get_field (expr_id "attr-obj") (expr_string "value")))
    (expr_string "undefined")) expr_false expr_true)
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_op1 unary_op_typeof
      (expr_get_field (expr_id "attr-obj") (expr_string "writable")))
     (expr_string "undefined")) expr_false expr_true))))
.
Definition privdefineOwnProperty := 
value_closure
(closure_intro
 [("%MakeGetter", privMakeGetter);
  ("%MakeSetter", privMakeSetter);
  ("%ToBoolean", privToBoolean);
  ("%ToString", privToString);
  ("%TypeError", privTypeError);
  ("copy-access-desc", copy_access_desc);
  ("copy-data-desc", copy_data_desc);
  ("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["obj"; "field"; "attr-obj"]
 (expr_seq
  (expr_let "t" (expr_op1 unary_op_typeof (expr_id "obj"))
   (expr_if
    (expr_if
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
      expr_false expr_true)
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
      expr_false expr_true) expr_false)
    (expr_throw (expr_string "defineOwnProperty didn't get object"))
    expr_undefined))
  (expr_let "fstr" (expr_app (expr_id "%ToString") [expr_id "field"])
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "fstr"))
     expr_false)
    (expr_if (expr_get_obj_attr oattr_extensible (expr_id "obj"))
     (expr_seq
      (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr") expr_true)
      (expr_seq
       (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
        expr_true)
       (expr_seq
        (expr_if (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"])
         (expr_seq
          (expr_set_attr pattr_value (expr_id "obj") (expr_id "fstr")
           (expr_get_field (expr_id "attr-obj") (expr_string "value")))
          (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
           (expr_app (expr_id "%ToBoolean")
            [expr_get_field (expr_id "attr-obj") (expr_string "writable")])))
         (expr_if
          (expr_app (expr_id "isAccessorDescriptor") [expr_id "attr-obj"])
          (expr_seq
           (expr_set_attr pattr_getter (expr_id "obj") (expr_id "fstr")
            (expr_app (expr_id "%MakeGetter")
             [expr_get_field (expr_id "attr-obj") (expr_string "get")]))
           (expr_set_attr pattr_setter (expr_id "obj") (expr_id "fstr")
            (expr_app (expr_id "%MakeSetter")
             [expr_get_field (expr_id "attr-obj") (expr_string "set")])))
          expr_undefined))
        (expr_seq
         (expr_set_attr pattr_enum (expr_id "obj") (expr_id "fstr")
          (expr_app (expr_id "%ToBoolean")
           [expr_get_field (expr_id "attr-obj") (expr_string "enumerable")]))
         (expr_seq
          (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr")
           (expr_app (expr_id "%ToBoolean")
            [expr_get_field (expr_id "attr-obj") (expr_string "configurable")]))
          expr_true)))))
     (expr_app (expr_id "%TypeError")
      [expr_string
       "(defineOwnProperty) Attempt to add a property to a non-extensible object."]))
    (expr_let "current-prop"
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined)
      [("configurable", property_data
                        (data_intro
                         (expr_get_attr pattr_config (expr_id "obj")
                          (expr_id "fstr")) expr_true expr_false expr_false));
       ("enumerable", property_data
                      (data_intro
                       (expr_get_attr pattr_enum (expr_id "obj")
                        (expr_id "fstr")) expr_true expr_false expr_false))])
     (expr_seq
      (expr_if
       (expr_op2 binary_op_is_accessor (expr_id "obj") (expr_id "fstr"))
       (expr_seq
        (expr_let "$newVal"
         (expr_get_attr pattr_getter (expr_id "obj") (expr_id "fstr"))
         (expr_set_field (expr_id "current-prop") (expr_string "get")
          (expr_id "$newVal")))
        (expr_let "$newVal"
         (expr_get_attr pattr_setter (expr_id "obj") (expr_id "fstr"))
         (expr_set_field (expr_id "current-prop") (expr_string "set")
          (expr_id "$newVal"))))
       (expr_seq
        (expr_let "$newVal"
         (expr_get_attr pattr_writable (expr_id "obj") (expr_id "fstr"))
         (expr_set_field (expr_id "current-prop") (expr_string "writable")
          (expr_id "$newVal")))
        (expr_let "$newVal"
         (expr_get_attr pattr_value (expr_id "obj") (expr_id "fstr"))
         (expr_set_field (expr_id "current-prop") (expr_string "value")
          (expr_id "$newVal")))))
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
         expr_false)
        (expr_seq
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "attr-obj") (expr_string "configurable"))
           expr_true)
          (expr_app (expr_id "%TypeError")
           [expr_string "escalating configurable from false to true"])
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_field (expr_id "attr-obj") (expr_string "enumerable"))
            (expr_op2 binary_op_stx_eq
             (expr_get_attr pattr_enum (expr_id "obj") (expr_id "fstr"))
             expr_false))
           (expr_app (expr_id "%TypeError")
            [expr_string
             "(defineOwnPoperty) Can't change enumerable of a non-configurable property"])
           expr_undefined))
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_app (expr_id "isDataDescriptor") [expr_id "current-prop"])
            (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"]))
           expr_false expr_true)
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
            expr_false)
           (expr_app (expr_id "%TypeError")
            [expr_string "(defineOwnProperty) Non-configurable property"])
           (expr_if
            (expr_app (expr_id "isDataDescriptor") [expr_id "current-prop"])
            (expr_app (expr_id "copy-data-desc")
             [expr_id "current-prop"; expr_id "attr-obj"])
            (expr_app (expr_id "copy-access-desc")
             [expr_id "current-prop"; expr_id "attr-obj"]))) expr_undefined))
        expr_undefined)
       (expr_seq
        (expr_if
         (expr_if
          (expr_app (expr_id "isDataDescriptor") [expr_id "current-prop"])
          (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"])
          expr_false)
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "current-prop")
            (expr_string "configurable")) expr_false)
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_field (expr_id "current-prop") (expr_string "writable"))
            expr_false)
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_get_field (expr_id "attr-obj") (expr_string "writable"))
             expr_true)
            (expr_app (expr_id "%TypeError")
             [expr_string
              "(defineOwnProperty) Cannot escalate writable from false to true."])
            (expr_if
             (expr_op2 binary_op_stx_eq
              (expr_op2 binary_op_same_value
               (expr_get_field (expr_id "attr-obj") (expr_string "value"))
               (expr_get_field (expr_id "current-prop") (expr_string "value")))
              expr_false)
             (expr_app (expr_id "%TypeError")
              [expr_string
               "(defineOwnProperty) Cannot change a non-configurable value"])
             (expr_app (expr_id "copy-data-desc")
              [expr_id "current-prop"; expr_id "attr-obj"])))
           (expr_app (expr_id "copy-data-desc")
            [expr_id "current-prop"; expr_id "attr-obj"]))
          (expr_app (expr_id "copy-data-desc")
           [expr_id "current-prop"; expr_id "attr-obj"]))
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "current-prop")
            (expr_string "configurable")) expr_false)
          (expr_if
           (expr_let "%or"
            (expr_op2 binary_op_stx_eq
             (expr_op2 binary_op_same_value
              (expr_get_field (expr_id "current-prop") (expr_string "set"))
              (expr_get_field (expr_id "attr-obj") (expr_string "set")))
             expr_false)
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_op2 binary_op_stx_eq
              (expr_op2 binary_op_same_value
               (expr_get_field (expr_id "current-prop") (expr_string "get"))
               (expr_get_field (expr_id "attr-obj") (expr_string "get")))
              expr_false)))
           (expr_app (expr_id "%TypeError")
            [expr_op2 binary_op_string_plus
             (expr_string
              "(defineOwnProperty) Cannot change setter or getter of non-configurable property ")
             (expr_id "fstr")])
           (expr_app (expr_id "copy-access-desc")
            [expr_id "current-prop"; expr_id "attr-obj"]))
          (expr_app (expr_id "copy-access-desc")
           [expr_id "current-prop"; expr_id "attr-obj"])))
        (expr_seq
         (expr_if
          (expr_app (expr_id "isDataDescriptor") [expr_id "current-prop"])
          (expr_seq
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_op2 binary_op_same_value
              (expr_get_attr pattr_value (expr_id "obj") (expr_id "fstr"))
              (expr_get_field (expr_id "current-prop") (expr_string "value")))
             expr_false)
            (expr_set_attr pattr_value (expr_id "obj") (expr_id "fstr")
             (expr_get_field (expr_id "current-prop") (expr_string "value")))
            expr_undefined)
           (expr_if
            (expr_if
             (expr_op2 binary_op_stx_eq
              (expr_get_attr pattr_writable (expr_id "obj") (expr_id "fstr"))
              (expr_get_field (expr_id "current-prop")
               (expr_string "writable"))) expr_false expr_true)
            (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
             (expr_get_field (expr_id "current-prop")
              (expr_string "writable"))) expr_undefined))
          (expr_if
           (expr_app (expr_id "isAccessorDescriptor")
            [expr_id "current-prop"])
           (expr_seq
            (expr_set_attr pattr_getter (expr_id "obj") (expr_id "fstr")
             (expr_get_field (expr_id "current-prop") (expr_string "get")))
            (expr_set_attr pattr_setter (expr_id "obj") (expr_id "fstr")
             (expr_get_field (expr_id "current-prop") (expr_string "set"))))
           expr_undefined))
         (expr_seq
          (expr_if
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_get_attr pattr_enum (expr_id "obj") (expr_id "fstr"))
             (expr_get_field (expr_id "current-prop")
              (expr_string "enumerable"))) expr_false expr_true)
           (expr_set_attr pattr_enum (expr_id "obj") (expr_id "fstr")
            (expr_get_field (expr_id "current-prop")
             (expr_string "enumerable"))) expr_undefined)
          (expr_seq
           (expr_if
            (expr_if
             (expr_op2 binary_op_stx_eq
              (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
              (expr_get_field (expr_id "current-prop")
               (expr_string "configurable"))) expr_false expr_true)
            (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr")
             (expr_get_field (expr_id "current-prop")
              (expr_string "configurable"))) expr_undefined) expr_true)))))))))))
.
Definition privArrayConstructor := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%JSError", privJSError);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_op2 binary_op_ge
     (expr_get_field (expr_id "args") (expr_string "length"))
     (expr_number (JsNumber.of_int 2)))
    (expr_let "rtnobj"
     (expr_object
      (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
       expr_null expr_undefined)
      [("length", property_data
                  (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                   expr_false expr_false))])
     (expr_recc "init"
      (expr_lambda ["n"]
       (expr_seq
        (expr_let "$newVal"
         (expr_get_field (expr_id "args")
          (expr_op1 unary_op_prim_to_str (expr_id "n")))
         (expr_set_field (expr_id "rtnobj")
          (expr_op1 unary_op_prim_to_str (expr_id "n")) (expr_id "$newVal")))
        (expr_if
         (expr_op2 binary_op_gt (expr_id "n")
          (expr_number (JsNumber.of_int 0)))
         (expr_app (expr_id "init")
          [expr_op2 binary_op_sub (expr_id "n")
           (expr_number (JsNumber.of_int 1))]) expr_undefined)))
      (expr_seq
       (expr_app (expr_id "init")
        [expr_get_field (expr_id "args") (expr_string "length")])
       (expr_seq
        (expr_let "$newVal"
         (expr_get_field (expr_id "args") (expr_string "length"))
         (expr_set_field (expr_id "rtnobj") (expr_string "length")
          (expr_id "$newVal"))) (expr_break "ret" (expr_id "rtnobj"))))))
    expr_null)
   (expr_let "c1"
    (expr_op2 binary_op_stx_eq
     (expr_op1 unary_op_typeof
      (expr_get_field (expr_id "args") (expr_string "0")))
     (expr_string "number"))
    (expr_let "c2"
     (expr_if (expr_id "c1")
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_app (expr_id "%ToUint32")
         [expr_get_field (expr_id "args") (expr_string "0")])
        (expr_get_field (expr_id "args") (expr_string "0"))) expr_false
       expr_true) expr_false)
     (expr_if (expr_id "c2")
      (expr_throw
       (expr_app (expr_id "%JSError")
        [expr_object
         (objattrs_intro (expr_string "Object") expr_true
          (expr_id "%RangeErrorProto") expr_null expr_undefined) []]))
      (expr_if (expr_id "c1")
       (expr_break "ret"
        (expr_object
         (objattrs_intro (expr_string "Array") expr_true
          (expr_id "%ArrayProto") expr_null expr_undefined)
         [("length", property_data
                     (data_intro
                      (expr_app (expr_id "%ToUint32")
                       [expr_get_field (expr_id "args") (expr_string "0")])
                      expr_true expr_false expr_false))]))
       (expr_let "rtn"
        (expr_object
         (objattrs_intro (expr_string "Array") expr_true
          (expr_id "%ArrayProto") expr_null expr_undefined)
         [("length", property_data
                     (data_intro
                      (expr_get_field (expr_id "args") (expr_string "length"))
                      expr_true expr_false expr_false))])
        (expr_seq
         (expr_app (expr_id "%defineOwnProperty")
          [expr_id "rtn";
           expr_string "0";
           expr_object
           (objattrs_intro (expr_string "Object") expr_true expr_null
            expr_null expr_undefined)
           [("value", property_data
                      (data_intro
                       (expr_get_field (expr_id "args") (expr_string "0"))
                       expr_true expr_false expr_false));
            ("writable", property_data
                         (data_intro expr_true expr_true expr_false
                          expr_false));
            ("enumerable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false));
            ("configurable", property_data
                             (data_intro expr_true expr_true expr_false
                              expr_false))]])
         (expr_break "ret" (expr_id "rtn")))))))))))
.
Definition privArrayGlobalFuncObj :=  value_object 108 .
Definition privArrayLengthChange := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["arr"; "newlen"]
 (expr_let "oldlen"
  (expr_app (expr_id "%ToUint32")
   [expr_get_field (expr_id "arr") (expr_string "length")])
  (expr_recc "fix"
   (expr_lambda ["i"]
    (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "oldlen"))
     (expr_seq
      (expr_delete_field (expr_id "arr")
       (expr_op1 unary_op_prim_to_str (expr_id "i")))
      (expr_app (expr_id "fix")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int 1))])) expr_undefined))
   (expr_app (expr_id "fix") [expr_id "newlen"]))))
.
Definition privToInt32 := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["n"]
 (expr_let "int32bit" (expr_app (expr_id "%ToUint32") [expr_id "n"])
  (expr_if
   (expr_op2 binary_op_ge (expr_id "int32bit")
    (expr_number (JsNumber.of_int 2147483648)))
   (expr_op2 binary_op_sub (expr_id "int32bit")
    (expr_number (JsNumber.of_int 4294967296))) (expr_id "int32bit"))))
.
Definition privBitwiseAnd := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["l"; "r"]
 (expr_op2 binary_op_band (expr_app (expr_id "%ToInt32") [expr_id "l"])
  (expr_app (expr_id "%ToInt32") [expr_id "r"])))
.
Definition privBitwiseInfix := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["l"; "r"; "op"]
 (expr_let "lnum" (expr_app (expr_id "%ToInt32") [expr_id "l"])
  (expr_let "rnum" (expr_app (expr_id "%ToInt32") [expr_id "r"])
   (expr_app (expr_id "op") [expr_id "lnum"; expr_id "rnum"]))))
.
Definition privBitwiseNot := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["expr"]
 (expr_let "oldValue" (expr_app (expr_id "%ToInt32") [expr_id "expr"])
  (expr_op1 unary_op_bnot (expr_id "oldValue"))))
.
Definition privBooleanProto :=  value_object 12 .
Definition privBooleanConstructor := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto); ("%ToBoolean", privToBoolean)] 
 None ["this"; "args"]
 (expr_let "b"
  (expr_app (expr_id "%ToBoolean")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
   (expr_id "b")
   (expr_object
    (objattrs_intro (expr_string "Boolean") expr_true
     (expr_id "%BooleanProto") expr_null (expr_id "b")) []))))
.
Definition privBooleanGlobalFuncObj :=  value_object 34 .
Definition privCheckObjectCoercible := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 (expr_if
  (expr_let "%or" (expr_op2 binary_op_stx_eq (expr_id "o") expr_undefined)
   (expr_if (expr_id "%or") (expr_id "%or")
    (expr_op2 binary_op_stx_eq (expr_id "o") expr_null)))
  (expr_app (expr_id "%TypeError") [expr_string "Not object coercible"])
  expr_undefined))
.
Definition privCompareOp := 
value_closure
(closure_intro
 [("%ToNumber", privToNumber); ("%ToPrimitiveHint", privToPrimitiveHint)]
 None ["l"; "r"; "LeftFirst"]
 (expr_let "rest"
  (expr_lambda ["px"; "py"]
   (expr_let "pxtype" (expr_op1 unary_op_typeof (expr_id "px"))
    (expr_let "pytype" (expr_op1 unary_op_typeof (expr_id "py"))
     (expr_label "ret"
      (expr_if
       (expr_let "%or"
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "pxtype") (expr_string "string"))
         expr_false expr_true)
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "pytype")
           (expr_string "string")) expr_false expr_true)))
       (expr_let "nx" (expr_app (expr_id "%ToNumber") [expr_id "px"])
        (expr_let "ny" (expr_app (expr_id "%ToNumber") [expr_id "py"])
         (expr_seq
          (expr_if
           (expr_let "%or"
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "nx") (expr_id "nx"))
             expr_false expr_true)
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "ny") (expr_id "ny"))
              expr_false expr_true))) (expr_break "ret" expr_undefined)
           expr_null)
          (expr_seq
           (expr_if (expr_op2 binary_op_stx_eq (expr_id "nx") (expr_id "ny"))
            (expr_break "ret" expr_false) expr_null)
           (expr_seq
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "nx")
              (expr_number (JsNumber.of_int 0)))
             (expr_break "ret" expr_false) expr_null)
            (expr_seq
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "ny")
               (expr_number (JsNumber.of_int 0)))
              (expr_break "ret" expr_true) expr_null)
             (expr_seq
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "ny")
                (expr_number (JsNumber.of_int 0)))
               (expr_break "ret" expr_false) expr_null)
              (expr_seq
               (expr_if
                (expr_op2 binary_op_stx_eq (expr_id "nx")
                 (expr_number (JsNumber.of_int 0)))
                (expr_break "ret" expr_true) expr_null)
               (expr_break "ret"
                (expr_op2 binary_op_lt (expr_id "nx") (expr_id "ny")))))))))))
       (expr_break "ret"
        (expr_op2 binary_op_string_lt (expr_id "px") (expr_id "py"))))))))
  (expr_if (expr_id "LeftFirst")
   (expr_let "px"
    (expr_app (expr_id "%ToPrimitiveHint")
     [expr_id "l"; expr_string "number"])
    (expr_let "py"
     (expr_app (expr_id "%ToPrimitiveHint")
      [expr_id "r"; expr_string "number"])
     (expr_app (expr_id "rest") [expr_id "px"; expr_id "py"])))
   (expr_let "py"
    (expr_app (expr_id "%ToPrimitiveHint")
     [expr_id "r"; expr_string "number"])
    (expr_let "px"
     (expr_app (expr_id "%ToPrimitiveHint")
      [expr_id "l"; expr_string "number"])
     (expr_app (expr_id "rest") [expr_id "px"; expr_id "py"]))))))
.
Definition privDateProto :=  value_object 174 .
Definition privmsPerDay :=  value_number (JsNumber.of_int 86400000) .
Definition privMakeDate := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["day"; "time"]
 (expr_op2 binary_op_add
  (expr_op2 binary_op_mul (expr_id "day") (expr_id "%msPerDay"))
  (expr_id "time")))
.
Definition privDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"]
 (expr_op1 unary_op_floor
  (expr_op2 binary_op_div (expr_id "t") (expr_id "%msPerDay"))))
.
Definition privDayFromYear := 
value_closure
(closure_intro [] None ["y"]
 (expr_let "fragment"
  (expr_lambda ["offset"; "coefficient"]
   (expr_op1 unary_op_floor
    (expr_op2 binary_op_div
     (expr_op2 binary_op_sub (expr_id "y") (expr_id "offset"))
     (expr_id "coefficient"))))
  (expr_let "base"
   (expr_op2 binary_op_mul (expr_number (JsNumber.of_int 365))
    (expr_op2 binary_op_sub (expr_id "y")
     (expr_number (JsNumber.of_int 1970))))
   (expr_let "part1"
    (expr_app (expr_id "fragment")
     [expr_number (JsNumber.of_int 1969); expr_number (JsNumber.of_int 4)])
    (expr_let "part2"
     (expr_app (expr_id "fragment")
      [expr_number (JsNumber.of_int 1901); expr_number (JsNumber.of_int 100)])
     (expr_let "part3"
      (expr_app (expr_id "fragment")
       [expr_number (JsNumber.of_int 1601); expr_number (JsNumber.of_int 400)])
      (expr_op2 binary_op_add
       (expr_op2 binary_op_sub
        (expr_op2 binary_op_add (expr_id "base") (expr_id "part1"))
        (expr_id "part2")) (expr_id "part3"))))))))
.
Definition privTimeFromYear := 
value_closure
(closure_intro
 [("%DayFromYear", privDayFromYear); ("%msPerDay", privmsPerDay)] None 
 ["y"]
 (expr_op2 binary_op_mul (expr_id "%msPerDay")
  (expr_app (expr_id "%DayFromYear") [expr_id "y"])))
.
Definition privYearFromTime := 
value_closure
(closure_intro [("%TimeFromYear", privTimeFromYear)] None ["t"]
 (expr_let "sign"
  (expr_if
   (expr_op2 binary_op_gt (expr_id "t") (expr_number (JsNumber.of_int 0)))
   (expr_number (JsNumber.of_int 1))
   (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
    (expr_number (JsNumber.of_int 1))))
  (expr_let "start"
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "sign")
     (expr_number (JsNumber.of_int 1))) (expr_number (JsNumber.of_int 1969))
    (expr_number (JsNumber.of_int 1970)))
   (expr_recc "loop"
    (expr_lambda ["y"]
     (expr_if
      (expr_if
       (expr_op2 binary_op_le
        (expr_app (expr_id "%TimeFromYear") [expr_id "y"]) (expr_id "t"))
       (expr_op2 binary_op_gt
        (expr_app (expr_id "%TimeFromYear")
         [expr_op2 binary_op_add (expr_number (JsNumber.of_int 1))
          (expr_id "y")]) (expr_id "t")) expr_false) (expr_id "y")
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "y") (expr_id "sign")])))
    (expr_app (expr_id "loop") [expr_id "start"])))))
.
Definition privDayWithinYear := 
value_closure
(closure_intro
 [("%Day", privDay);
  ("%DayFromYear", privDayFromYear);
  ("%YearFromTime", privYearFromTime)] None ["t"]
 (expr_op2 binary_op_sub (expr_app (expr_id "%Day") [expr_id "t"])
  (expr_app (expr_id "%DayFromYear")
   [expr_app (expr_id "%YearFromTime") [expr_id "t"]])))
.
Definition privDaysInYear := 
value_closure
(closure_intro [] None ["y"]
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_op2 binary_op_mod (expr_id "y") (expr_number (JsNumber.of_int 4)))
    (expr_number (JsNumber.of_int 0))) expr_false expr_true)
  (expr_number (JsNumber.of_int 365))
  (expr_if
   (expr_let "%or"
    (expr_op2 binary_op_stx_eq
     (expr_op2 binary_op_mod (expr_id "y")
      (expr_number (JsNumber.of_int 400))) (expr_number (JsNumber.of_int 0)))
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_op2 binary_op_mod (expr_id "y")
        (expr_number (JsNumber.of_int 100)))
       (expr_number (JsNumber.of_int 0))) expr_false expr_true)))
   (expr_number (JsNumber.of_int 366)) (expr_number (JsNumber.of_int 365)))))
.
Definition privInLeapYear := 
value_closure
(closure_intro
 [("%DaysInYear", privDaysInYear); ("%YearFromTime", privYearFromTime)] 
 None ["t"]
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "%DaysInYear")
    [expr_app (expr_id "%YearFromTime") [expr_id "t"]])
   (expr_number (JsNumber.of_int 365))) (expr_number (JsNumber.of_int 0))
  (expr_number (JsNumber.of_int 1))))
.
Definition privMonthFromTime := 
value_closure
(closure_intro
 [("%Day", privDay);
  ("%DayFromYear", privDayFromYear);
  ("%DayWithinYear", privDayWithinYear);
  ("%InLeapYear", privInLeapYear);
  ("%TypeError", privTypeError);
  ("%YearFromTime", privYearFromTime)] None ["t"]
 (expr_let "DayWithinYear"
  (expr_lambda ["t"]
   (expr_op2 binary_op_sub (expr_app (expr_id "%Day") [expr_id "t"])
    (expr_app (expr_id "%DayFromYear")
     [expr_app (expr_id "%YearFromTime") [expr_id "t"]])))
  (expr_let "CheckLeapRange"
   (expr_lambda ["start"; "end"]
    (expr_if
     (expr_op2 binary_op_le
      (expr_op2 binary_op_add (expr_id "start")
       (expr_app (expr_id "%InLeapYear") [expr_id "t"]))
      (expr_app (expr_id "DayWithinYear") [expr_id "t"]))
     (expr_op2 binary_op_lt
      (expr_app (expr_id "DayWithinYear") [expr_id "t"])
      (expr_op2 binary_op_add (expr_id "end")
       (expr_app (expr_id "%InLeapYear") [expr_id "t"]))) expr_false))
   (expr_if
    (expr_if
     (expr_op2 binary_op_le (expr_number (JsNumber.of_int 0))
      (expr_app (expr_id "%DayWithinYear") [expr_id "t"]))
     (expr_op2 binary_op_lt
      (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
      (expr_number (JsNumber.of_int 31))) expr_false)
    (expr_number (JsNumber.of_int 0))
    (expr_if
     (expr_if
      (expr_op2 binary_op_le (expr_number (JsNumber.of_int 31))
       (expr_app (expr_id "%DayWithinYear") [expr_id "t"]))
      (expr_op2 binary_op_lt
       (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
       (expr_op2 binary_op_add (expr_number (JsNumber.of_int 59))
        (expr_app (expr_id "%InLeapYear") [expr_id "t"]))) expr_false)
     (expr_number (JsNumber.of_int 1))
     (expr_if
      (expr_app (expr_id "CheckLeapRange")
       [expr_number (JsNumber.of_int 59); expr_number (JsNumber.of_int 90)])
      (expr_number (JsNumber.of_int 2))
      (expr_if
       (expr_app (expr_id "CheckLeapRange")
        [expr_number (JsNumber.of_int 90); expr_number (JsNumber.of_int 120)])
       (expr_number (JsNumber.of_int 3))
       (expr_if
        (expr_app (expr_id "CheckLeapRange")
         [expr_number (JsNumber.of_int 120);
          expr_number (JsNumber.of_int 151)])
        (expr_number (JsNumber.of_int 4))
        (expr_if
         (expr_app (expr_id "CheckLeapRange")
          [expr_number (JsNumber.of_int 151);
           expr_number (JsNumber.of_int 181)])
         (expr_number (JsNumber.of_int 5))
         (expr_if
          (expr_app (expr_id "CheckLeapRange")
           [expr_number (JsNumber.of_int 181);
            expr_number (JsNumber.of_int 212)])
          (expr_number (JsNumber.of_int 6))
          (expr_if
           (expr_app (expr_id "CheckLeapRange")
            [expr_number (JsNumber.of_int 212);
             expr_number (JsNumber.of_int 243)])
           (expr_number (JsNumber.of_int 7))
           (expr_if
            (expr_app (expr_id "CheckLeapRange")
             [expr_number (JsNumber.of_int 243);
              expr_number (JsNumber.of_int 273)])
            (expr_number (JsNumber.of_int 8))
            (expr_if
             (expr_app (expr_id "CheckLeapRange")
              [expr_number (JsNumber.of_int 273);
               expr_number (JsNumber.of_int 304)])
             (expr_number (JsNumber.of_int 9))
             (expr_if
              (expr_app (expr_id "CheckLeapRange")
               [expr_number (JsNumber.of_int 304);
                expr_number (JsNumber.of_int 334)])
              (expr_number (JsNumber.of_int 10))
              (expr_if
               (expr_app (expr_id "CheckLeapRange")
                [expr_number (JsNumber.of_int 334);
                 expr_number (JsNumber.of_int 365)])
               (expr_number (JsNumber.of_int 11))
               (expr_app (expr_id "%TypeError")
                [expr_string "Something terrible in date %MonthFromTime"]))))))))))))))))
.
Definition privDateFromTime := 
value_closure
(closure_intro
 [("%DayWithinYear", privDayWithinYear);
  ("%InLeapYear", privInLeapYear);
  ("%MonthFromTime", privMonthFromTime);
  ("%TypeError", privTypeError)] None ["t"]
 (expr_let "mft" (expr_app (expr_id "%MonthFromTime") [expr_id "t"])
  (expr_let "CalcDay"
   (expr_lambda ["offset"]
    (expr_op2 binary_op_sub
     (expr_op2 binary_op_sub
      (expr_app (expr_id "%DayWithinYear") [expr_id "t"]) (expr_id "offset"))
     (expr_app (expr_id "%InLeapYear") [expr_id "t"])))
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "mft")
     (expr_number (JsNumber.of_int 0)))
    (expr_op2 binary_op_add
     (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
     (expr_number (JsNumber.of_int 1)))
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "mft")
      (expr_number (JsNumber.of_int 1)))
     (expr_op2 binary_op_sub
      (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
      (expr_number (JsNumber.of_int 30)))
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "mft")
       (expr_number (JsNumber.of_int 2)))
      (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 58)])
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "mft")
        (expr_number (JsNumber.of_int 3)))
       (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 89)])
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "mft")
         (expr_number (JsNumber.of_int 4)))
        (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 119)])
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "mft")
          (expr_number (JsNumber.of_int 5)))
         (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 150)])
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "mft")
           (expr_number (JsNumber.of_int 6)))
          (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 180)])
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "mft")
            (expr_number (JsNumber.of_int 7)))
           (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 211)])
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "mft")
             (expr_number (JsNumber.of_int 8)))
            (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 242)])
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "mft")
              (expr_number (JsNumber.of_int 9)))
             (expr_app (expr_id "CalcDay")
              [expr_number (JsNumber.of_int 272)])
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "mft")
               (expr_number (JsNumber.of_int 10)))
              (expr_app (expr_id "CalcDay")
               [expr_number (JsNumber.of_int 303)])
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "mft")
                (expr_number (JsNumber.of_int 11)))
               (expr_app (expr_id "CalcDay")
                [expr_number (JsNumber.of_int 333)])
               (expr_app (expr_id "%TypeError")
                [expr_string "Something terrible happened in %DateFromTime"]))))))))))))))))
.
Definition privDaysInMonth := 
value_closure
(closure_intro [] None ["m"; "leap"]
 (expr_let "m"
  (expr_op2 binary_op_mod (expr_id "m") (expr_number (JsNumber.of_int 12)))
  (expr_if
   (expr_let "%or"
    (expr_let "%or"
     (expr_let "%or"
      (expr_op2 binary_op_stx_eq (expr_id "m")
       (expr_number (JsNumber.of_int 3)))
      (expr_if (expr_id "%or") (expr_id "%or")
       (expr_op2 binary_op_stx_eq (expr_id "m")
        (expr_number (JsNumber.of_int 5)))))
     (expr_if (expr_id "%or") (expr_id "%or")
      (expr_op2 binary_op_stx_eq (expr_id "m")
       (expr_number (JsNumber.of_int 8)))))
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_stx_eq (expr_id "m")
      (expr_number (JsNumber.of_int 10)))))
   (expr_number (JsNumber.of_int 30))
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "m")
     (expr_number (JsNumber.of_int 1)))
    (expr_op2 binary_op_add (expr_number (JsNumber.of_int 28))
     (expr_id "leap")) (expr_number (JsNumber.of_int 31))))))
.
Definition privIsFinite := 
value_closure
(closure_intro [] None ["n"]
 (expr_op1 unary_op_not
  (expr_let "%or"
   (expr_let "%or"
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
     expr_false expr_true)
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_stx_eq (expr_id "n")
      (expr_number (JsNumber.of_int 0)))))
   (expr_if (expr_id "%or") (expr_id "%or")
    (expr_op2 binary_op_stx_eq (expr_id "n")
     (expr_number (JsNumber.of_int 0)))))))
.
Definition privToInteger := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["i"]
 (expr_label "ret"
  (expr_let "number" (expr_app (expr_id "%ToNumber") [expr_id "i"])
   (expr_seq
    (expr_if
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "number") (expr_id "number"))
      expr_false expr_true)
     (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
    (expr_seq
     (expr_if
      (expr_let "%or"
       (expr_let "%or"
        (expr_op2 binary_op_stx_eq (expr_id "number")
         (expr_number (JsNumber.of_int 0)))
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_op2 binary_op_stx_eq (expr_id "number")
          (expr_number (JsNumber.of_int 0)))))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "number")
         (expr_number (JsNumber.of_int 0)))))
      (expr_break "ret" (expr_id "number")) expr_null)
     (expr_let "sign"
      (expr_if
       (expr_op2 binary_op_lt (expr_id "number")
        (expr_number (JsNumber.of_int 0)))
       (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
        (expr_number (JsNumber.of_int 1))) (expr_number (JsNumber.of_int 1)))
      (expr_let "a" (expr_op1 unary_op_abs (expr_id "number"))
       (expr_let "f" (expr_op1 unary_op_floor (expr_id "a"))
        (expr_let "r" (expr_op2 binary_op_mul (expr_id "sign") (expr_id "f"))
         (expr_break "ret" (expr_id "r")))))))))))
.
Definition privMakeDay := 
value_closure
(closure_intro
 [("%DateFromTime", privDateFromTime);
  ("%Day", privDay);
  ("%DaysInMonth", privDaysInMonth);
  ("%InLeapYear", privInLeapYear);
  ("%IsFinite", privIsFinite);
  ("%MonthFromTime", privMonthFromTime);
  ("%TimeFromYear", privTimeFromYear);
  ("%ToInteger", privToInteger);
  ("%YearFromTime", privYearFromTime);
  ("%msPerDay", privmsPerDay)] None ["yr"; "mt"; "date"]
 (expr_if
  (expr_op1 unary_op_not
   (expr_if
    (expr_if (expr_app (expr_id "%IsFinite") [expr_id "yr"])
     (expr_app (expr_id "%IsFinite") [expr_id "mt"]) expr_false)
    (expr_app (expr_id "%IsFinite") [expr_id "date"]) expr_false))
  (expr_number (JsNumber.of_int 0))
  (expr_let "y" (expr_app (expr_id "%ToInteger") [expr_id "yr"])
   (expr_let "m" (expr_app (expr_id "%ToInteger") [expr_id "mt"])
    (expr_let "dt" (expr_app (expr_id "%ToInteger") [expr_id "date"])
     (expr_let "ym"
      (expr_op2 binary_op_add (expr_id "y")
       (expr_op1 unary_op_floor
        (expr_op2 binary_op_div (expr_id "m")
         (expr_number (JsNumber.of_int 12)))))
      (expr_let "mn"
       (expr_op2 binary_op_mod (expr_id "m")
        (expr_number (JsNumber.of_int 12)))
       (expr_let "yt" (expr_app (expr_id "%TimeFromYear") [expr_id "y"])
        (expr_recc "loop"
         (expr_lambda ["t"; "mo"; "leap"]
          (expr_if (expr_op2 binary_op_lt (expr_id "mo") (expr_id "m"))
           (expr_let "leap" (expr_app (expr_id "%InLeapYear") [expr_id "t"])
            (expr_let "t"
             (expr_op2 binary_op_add (expr_id "t")
              (expr_op2 binary_op_mul
               (expr_app (expr_id "%DaysInMonth")
                [expr_id "mo"; expr_id "leap"]) (expr_id "%msPerDay")))
             (expr_app (expr_id "loop")
              [expr_id "t";
               expr_op2 binary_op_add (expr_id "mo")
               (expr_number (JsNumber.of_int 1));
               expr_id "leap"]))) (expr_id "t")))
         (expr_let "t"
          (expr_app (expr_id "loop")
           [expr_id "yt";
            expr_number (JsNumber.of_int 0);
            expr_app (expr_id "%InLeapYear") [expr_id "yt"]])
          (expr_if
           (expr_let "%or"
            (expr_let "%or"
             (expr_if
              (expr_op2 binary_op_stx_eq
               (expr_app (expr_id "%YearFromTime") [expr_id "t"])
               (expr_id "ym")) expr_false expr_true)
             (expr_if (expr_id "%or") (expr_id "%or")
              (expr_if
               (expr_op2 binary_op_stx_eq
                (expr_app (expr_id "%MonthFromTime") [expr_id "t"])
                (expr_id "mn")) expr_false expr_true)))
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_if
              (expr_op2 binary_op_stx_eq
               (expr_app (expr_id "%DateFromTime") [expr_id "t"])
               (expr_number (JsNumber.of_int 1))) expr_false expr_true)))
           (expr_number (JsNumber.of_int 0))
           (expr_op2 binary_op_sub
            (expr_op2 binary_op_add (expr_app (expr_id "%Day") [expr_id "t"])
             (expr_id "dt")) (expr_number (JsNumber.of_int 1))))))))))))))
.
Definition privmsPerHour :=  value_number (JsNumber.of_int 3600000) .
Definition privmsPerMin :=  value_number (JsNumber.of_int 60000) .
Definition privmsPerSecond :=  value_number (JsNumber.of_int 1000) .
Definition privMakeTime := 
value_closure
(closure_intro
 [("%IsFinite", privIsFinite);
  ("%ToInteger", privToInteger);
  ("%msPerHour", privmsPerHour);
  ("%msPerMin", privmsPerMin);
  ("%msPerSecond", privmsPerSecond)] None ["h"; "m"; "s"; "ms"]
 (expr_if
  (expr_op1 unary_op_not
   (expr_if
    (expr_if
     (expr_if (expr_app (expr_id "%IsFinite") [expr_id "h"])
      (expr_app (expr_id "%IsFinite") [expr_id "m"]) expr_false)
     (expr_app (expr_id "%IsFinite") [expr_id "s"]) expr_false)
    (expr_app (expr_id "%IsFinite") [expr_id "ms"]) expr_false))
  (expr_number (JsNumber.of_int 0))
  (expr_let "hour" (expr_app (expr_id "%ToInteger") [expr_id "h"])
   (expr_let "min" (expr_app (expr_id "%ToInteger") [expr_id "m"])
    (expr_let "sec" (expr_app (expr_id "%ToInteger") [expr_id "s"])
     (expr_let "millis" (expr_app (expr_id "%ToInteger") [expr_id "ms"])
      (expr_let "t"
       (expr_op2 binary_op_add
        (expr_op2 binary_op_add
         (expr_op2 binary_op_add
          (expr_op2 binary_op_mul (expr_id "hour") (expr_id "%msPerHour"))
          (expr_op2 binary_op_mul (expr_id "min") (expr_id "%msPerMin")))
         (expr_op2 binary_op_mul (expr_id "sec") (expr_id "%msPerSecond")))
        (expr_id "millis")) (expr_id "t"))))))))
.
Definition privTimeClip := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToInteger", privToInteger)]
 None ["t"]
 (expr_if
  (expr_op1 unary_op_not
   (expr_if (expr_app (expr_id "%IsFinite") [expr_id "t"])
    (expr_op2 binary_op_le (expr_op1 unary_op_abs (expr_id "t"))
     (expr_number (JsNumber.of_int 8640000000000000))) expr_false))
  (expr_number (JsNumber.of_int 0))
  (expr_app (expr_id "%ToInteger") [expr_id "t"])))
.
Definition privToPrimitive := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 (expr_app (expr_id "%ToPrimitiveHint") [expr_id "val"; expr_string "number"]))
.
Definition privUTC := 
value_closure (closure_intro [] None ["t"] (expr_id "t"))
.
Definition privdateToStringLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "Date toString NYI"))
.
Definition privgetCurrentUTC := 
value_closure
(closure_intro [] None []
 (expr_op1 unary_op_current_utc_millis (expr_string "ignored")))
.
Definition privparse := 
value_closure (closure_intro [] None ["v"] (expr_number (JsNumber.of_int 0)))
.
Definition privDateConstructor := 
value_closure
(closure_intro
 [("%DateProto", privDateProto);
  ("%MakeDate", privMakeDate);
  ("%MakeDay", privMakeDay);
  ("%MakeTime", privMakeTime);
  ("%TimeClip", privTimeClip);
  ("%ToInteger", privToInteger);
  ("%ToNumber", privToNumber);
  ("%ToPrimitive", privToPrimitive);
  ("%UTC", privUTC);
  ("%dateToStringLambda", privdateToStringLambda);
  ("%getCurrentUTC", privgetCurrentUTC);
  ("%parse", privparse)] None ["this"; "args"]
 (expr_let "calledAsFunction"
  (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
  (expr_let "nargs" (expr_get_field (expr_id "args") (expr_string "length"))
   (expr_if (expr_id "calledAsFunction")
    (expr_let "v" (expr_app (expr_id "%getCurrentUTC") [])
     (expr_let "o"
      (expr_object
       (objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
        expr_null (expr_id "v")) [])
      (expr_app (expr_id "%dateToStringLambda")
       [expr_id "o";
        expr_object
        (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
         expr_undefined) []])))
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "nargs")
      (expr_number (JsNumber.of_int 0)))
     (expr_let "v" (expr_app (expr_id "%getCurrentUTC") [])
      (expr_object
       (objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
        expr_null (expr_id "v")) []))
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "nargs")
       (expr_number (JsNumber.of_int 1)))
      (expr_let "v"
       (expr_app (expr_id "%ToPrimitive")
        [expr_get_field (expr_id "args") (expr_string "0")])
       (expr_let "V"
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "v"))
          (expr_string "string")) (expr_app (expr_id "%parse") [expr_id "v"])
         (expr_app (expr_id "%ToNumber") [expr_id "v"]))
        (expr_let "clipped" (expr_app (expr_id "%TimeClip") [expr_id "V"])
         (expr_object
          (objattrs_intro (expr_string "Date") expr_true
           (expr_id "%DateProto") expr_null (expr_id "clipped")) []))))
      (expr_let "y"
       (expr_app (expr_id "%ToNumber")
        [expr_get_field (expr_id "args") (expr_string "0")])
       (expr_let "m"
        (expr_app (expr_id "%ToNumber")
         [expr_get_field (expr_id "args") (expr_string "1")])
        (expr_let "dt"
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "args") (expr_string "2")) expr_undefined)
          (expr_number (JsNumber.of_int 1))
          (expr_app (expr_id "%ToNumber")
           [expr_get_field (expr_id "args") (expr_string "2")]))
         (expr_let "h"
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_field (expr_id "args") (expr_string "3"))
            expr_undefined) (expr_number (JsNumber.of_int 0))
           (expr_app (expr_id "%ToNumber")
            [expr_get_field (expr_id "args") (expr_string "3")]))
          (expr_let "min"
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_get_field (expr_id "args") (expr_string "4"))
             expr_undefined) (expr_number (JsNumber.of_int 0))
            (expr_app (expr_id "%ToNumber")
             [expr_get_field (expr_id "args") (expr_string "4")]))
           (expr_let "s"
            (expr_if
             (expr_op2 binary_op_stx_eq
              (expr_get_field (expr_id "args") (expr_string "5"))
              expr_undefined) (expr_number (JsNumber.of_int 0))
             (expr_app (expr_id "%ToNumber")
              [expr_get_field (expr_id "args") (expr_string "5")]))
            (expr_let "milli"
             (expr_if
              (expr_op2 binary_op_stx_eq
               (expr_get_field (expr_id "args") (expr_string "6"))
               expr_undefined) (expr_number (JsNumber.of_int 0))
              (expr_app (expr_id "%ToNumber")
               [expr_get_field (expr_id "args") (expr_string "6")]))
             (expr_let "yr"
              (expr_let "tiy" (expr_app (expr_id "%ToInteger") [expr_id "y"])
               (expr_let "rangecond1"
                (expr_let "%or"
                 (expr_op2 binary_op_lt (expr_number (JsNumber.of_int 0))
                  (expr_id "tiy"))
                 (expr_if (expr_id "%or") (expr_id "%or")
                  (expr_op2 binary_op_stx_eq
                   (expr_number (JsNumber.of_int 0)) (expr_id "tiy"))))
                (expr_let "rangecond2"
                 (expr_let "%or"
                  (expr_op2 binary_op_lt (expr_id "tiy")
                   (expr_number (JsNumber.of_int 99)))
                  (expr_if (expr_id "%or") (expr_id "%or")
                   (expr_op2 binary_op_stx_eq (expr_id "tiy")
                    (expr_number (JsNumber.of_int 99)))))
                 (expr_if
                  (expr_if
                   (expr_if
                    (expr_if
                     (expr_op2 binary_op_stx_eq (expr_id "y") (expr_id "y"))
                     expr_false expr_true) (expr_id "rangecond1") expr_false)
                   (expr_id "rangecond2") expr_false)
                  (expr_op2 binary_op_add
                   (expr_number (JsNumber.of_int 1900)) (expr_id "tiy"))
                  (expr_id "y")))))
              (expr_let "finalDate"
               (expr_app (expr_id "%MakeDate")
                [expr_app (expr_id "%MakeDay")
                 [expr_id "yr"; expr_id "m"; expr_id "dt"];
                 expr_app (expr_id "%MakeTime")
                 [expr_id "h"; expr_id "min"; expr_id "s"; expr_id "milli"]])
               (expr_let "primval"
                (expr_app (expr_id "%TimeClip")
                 [expr_app (expr_id "%UTC") [expr_id "finalDate"]])
                (expr_object
                 (objattrs_intro (expr_string "Date") expr_true
                  (expr_id "%DateProto") expr_null (expr_id "primval")) 
                 [])))))))))))))))))
.
Definition privDateGlobalFuncObj :=  value_object 178 .
Definition privReferenceErrorProto :=  value_object 10 .
Definition privIsJSError := 
value_closure
(closure_intro [] None ["thing"]
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "thing"))
   (expr_string "object"))
  (expr_op2 binary_op_has_own_property (expr_id "thing")
   (expr_string "%js-exn")) expr_false))
.
Definition privErrorDispatch := 
value_closure
(closure_intro [("%IsJSError", privIsJSError); ("%TypeError", privTypeError)]
 None ["maybe-js-error"]
 (expr_if (expr_app (expr_id "%IsJSError") [expr_id "maybe-js-error"])
  (expr_throw (expr_id "maybe-js-error"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
    (expr_string "unwritable-field"))
   (expr_app (expr_id "%TypeError") [expr_string "Field not writable"])
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
     (expr_string "unconfigurable-delete"))
    (expr_app (expr_id "%TypeError") [expr_string "Field not deletable"])
    (expr_throw (expr_id "maybe-js-error"))))))
.
Definition privUnwritableDispatch := 
value_closure
(closure_intro
 [("%ErrorDispatch", privErrorDispatch); ("%TypeError", privTypeError)] 
 None ["id"]
 (expr_lambda ["e"]
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "e") (expr_string "unwritable-field"))
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus (expr_id "id")
     (expr_string " not writable")])
   (expr_app (expr_id "%ErrorDispatch") [expr_id "e"]))))
.
Definition privglobal :=  value_object 3 .
Definition privisUnbound := 
value_closure
(closure_intro [("%global", privglobal)] None ["context"; "id"]
 (expr_op1 unary_op_not
  (expr_op2 binary_op_has_property (expr_id "%global") (expr_id "id"))))
.
Definition privNumberProto :=  value_object 13 .
Definition privStringIndices := 
value_closure
(closure_intro [] None ["obj"; "s"]
 (expr_let "len" (expr_op1 unary_op_strlen (expr_id "s"))
  (expr_recc "loop"
   (expr_lambda ["i"]
    (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
     (expr_seq
      (expr_let "$newVal"
       (expr_op2 binary_op_char_at (expr_id "s") (expr_id "i"))
       (expr_set_field (expr_id "obj")
        (expr_op1 unary_op_prim_to_str (expr_id "i")) (expr_id "$newVal")))
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int 1))])) expr_undefined))
   (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)]))))
.
Definition privStringProto :=  value_object 14 .
Definition privToObject := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto);
  ("%NumberProto", privNumberProto);
  ("%StringIndices", privStringIndices);
  ("%StringProto", privStringProto);
  ("%TypeError", privTypeError)] None ["o"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "o") expr_null)
  (expr_app (expr_id "%TypeError") [expr_string "%ToObject received null"])
  (expr_label "ret"
   (expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
    (expr_seq
     (expr_if
      (expr_let "%or"
       (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))))
      (expr_break "ret" (expr_id "o")) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "string"))
       (expr_let "obj"
        (expr_object
         (objattrs_intro (expr_string "String") expr_true
          (expr_id "%StringProto") expr_null (expr_id "o"))
         [("length", property_data
                     (data_intro (expr_op1 unary_op_strlen (expr_id "o"))
                      expr_true expr_false expr_false))])
        (expr_seq
         (expr_app (expr_id "%StringIndices") [expr_id "obj"; expr_id "o"])
         (expr_break "ret" (expr_id "obj")))) expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "number"))
        (expr_break "ret"
         (expr_object
          (objattrs_intro (expr_string "Number") expr_true
           (expr_id "%NumberProto") expr_null (expr_id "o")) [])) expr_null)
       (expr_seq
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "boolean"))
         (expr_break "ret"
          (expr_object
           (objattrs_intro (expr_string "Boolean") expr_true
            (expr_id "%BooleanProto") expr_null (expr_id "o")) [])) expr_null)
        (expr_seq
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
          (expr_break "ret"
           (expr_object
            (objattrs_intro (expr_string "Function") expr_true
             (expr_id "%BooleanProto") expr_null (expr_id "o")) []))
          expr_null)
         (expr_app (expr_id "%TypeError")
          [expr_string "%ToObject received undefined"]))))))))))
.
Definition privset_property := 
value_closure
(closure_intro
 [("%ArrayLengthChange", privArrayLengthChange);
  ("%JSError", privJSError);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToNumber", privToNumber);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "fld"; "val"]
 (expr_let "obj" (expr_app (expr_id "%ToObject") [expr_id "obj"])
  (expr_let "fld" (expr_app (expr_id "%ToString") [expr_id "fld"])
   (expr_let "check"
    (expr_lambda ["flag"]
     (expr_if (expr_id "flag")
      (expr_app (expr_id "%TypeError") [expr_string "set-property failed"])
      expr_null))
    (expr_let "e"
     (expr_op1 unary_op_not
      (expr_get_obj_attr oattr_extensible (expr_id "obj")))
     (expr_seq (expr_app (expr_id "check") [expr_id "e"])
      (expr_let "isArrayIndex"
       (expr_lambda []
        (expr_let "uint" (expr_app (expr_id "%ToUint32") [expr_id "fld"])
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_app (expr_id "%ToString") [expr_id "uint"]) (expr_id "fld"))
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "uint")
            (expr_number (JsNumber.of_int 4294967295))) expr_false expr_true)
          expr_false)))
       (expr_let "setArrayField"
        (expr_lambda []
         (expr_let "lenCheck"
          (expr_lambda []
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "fld") (expr_string "length"))
            (expr_let "newLen"
             (expr_app (expr_id "%ToUint32") [expr_id "val"])
             (expr_let "toCompare"
              (expr_app (expr_id "%ToNumber") [expr_id "val"])
              (expr_if
               (expr_if
                (expr_op2 binary_op_stx_eq (expr_id "newLen")
                 (expr_id "toCompare")) expr_false expr_true)
               (expr_throw
                (expr_app (expr_id "%JSError")
                 [expr_object
                  (objattrs_intro (expr_string "Object") expr_true
                   (expr_id "%RangeErrorProto") expr_null expr_undefined) 
                  []]))
               (expr_if
                (expr_op2 binary_op_lt (expr_id "newLen")
                 (expr_get_field (expr_id "obj") (expr_string "length")))
                (expr_app (expr_id "%ArrayLengthChange")
                 [expr_id "obj"; expr_id "newLen"]) expr_undefined))))
            expr_undefined))
          (expr_seq (expr_app (expr_id "lenCheck") [])
           (expr_seq
            (expr_let "$newVal"
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "fld")
               (expr_string "length"))
              (expr_app (expr_id "%ToUint32") [expr_id "val"])
              (expr_id "val"))
             (expr_set_field (expr_id "obj") (expr_id "fld")
              (expr_id "$newVal")))
            (expr_if (expr_app (expr_id "isArrayIndex") [])
             (expr_let "uint"
              (expr_app (expr_id "%ToUint32") [expr_id "fld"])
              (expr_let "len"
               (expr_get_field (expr_id "obj") (expr_string "length"))
               (expr_if
                (expr_op2 binary_op_lt (expr_id "len")
                 (expr_op2 binary_op_add (expr_id "uint")
                  (expr_number (JsNumber.of_int 1))))
                (expr_let "$newVal"
                 (expr_op2 binary_op_add (expr_id "uint")
                  (expr_number (JsNumber.of_int 1)))
                 (expr_set_field (expr_id "obj") (expr_string "length")
                  (expr_id "$newVal"))) expr_undefined))) expr_undefined)))))
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_obj_attr oattr_class (expr_id "obj"))
          (expr_string "Array")) (expr_app (expr_id "setArrayField") [])
         (expr_let "$newVal" (expr_id "val")
          (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal"))))))))))))
.
Definition privEnvCheckAssign := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto);
  ("%UnwritableDispatch", privUnwritableDispatch);
  ("%isUnbound", privisUnbound);
  ("%set-property", privset_property)] None
 ["context"; "id"; "val"; "strict"]
 (expr_if
  (expr_if (expr_id "strict")
   (expr_app (expr_id "%isUnbound") [expr_id "context"; expr_id "id"])
   expr_false)
  (expr_throw
   (expr_app (expr_id "%JSError")
    [expr_object
     (objattrs_intro (expr_string "Object") expr_true
      (expr_id "%ReferenceErrorProto") expr_null expr_undefined)
     [("message", property_data
                  (data_intro (expr_id "id") expr_true expr_false expr_false))]]))
  (expr_try_catch
   (expr_app (expr_id "%set-property")
    [expr_id "context"; expr_id "id"; expr_id "val"])
   (expr_app (expr_id "%UnwritableDispatch") [expr_id "id"]))))
.
Definition privUnboundId := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto)] None ["id"]
 (expr_throw
  (expr_app (expr_id "%JSError")
   [expr_object
    (objattrs_intro (expr_string "Object") expr_true
     (expr_id "%ReferenceErrorProto") expr_null expr_undefined)
    [("message", property_data
                 (data_intro
                  (expr_op2 binary_op_string_plus
                   (expr_string "Unbound identifier: ") (expr_id "id"))
                  expr_true expr_false expr_false))]])))
.
Definition privEnvGet := 
value_closure
(closure_intro [("%UnboundId", privUnboundId); ("%isUnbound", privisUnbound)]
 None ["context"; "id"; "strict"]
 (expr_if
  (expr_if (expr_id "strict")
   (expr_app (expr_id "%isUnbound") [expr_id "context"; expr_id "id"])
   expr_false) (expr_app (expr_id "%UnboundId") [expr_id "id"])
  (expr_get_field (expr_id "context") (expr_id "id"))))
.
Definition privEqEq := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] (Some "eqeq") ["x1"; "x2"]
 (expr_label "ret"
  (expr_let "t1" (expr_op1 unary_op_typeof (expr_id "x1"))
   (expr_let "t2" (expr_op1 unary_op_typeof (expr_id "x2"))
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_id "t2"))
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "undefined"))
      (expr_break "ret" expr_true)
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "null"))
       (expr_break "ret" expr_true)
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "number"))
        (expr_break "ret"
         (expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2")))
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "string"))
         (expr_break "ret"
          (expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2")))
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "object"))
          (expr_break "ret"
           (expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2")))
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "boolean"))
           (expr_break "ret"
            (expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2")))
           (expr_throw (expr_string "[env] Catastrophe---unknown type in =="))))))))
     (expr_if
      (expr_let "%or"
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "x1") expr_undefined)
        (expr_op2 binary_op_stx_eq (expr_id "x2") expr_null) expr_false)
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_if (expr_op2 binary_op_stx_eq (expr_id "x1") expr_null)
         (expr_op2 binary_op_stx_eq (expr_id "x2") expr_undefined) expr_false)))
      (expr_break "ret" expr_true)
      (expr_if
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "number"))
        (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "string"))
        expr_false)
       (expr_break "ret"
        (expr_op2 binary_op_stx_eq (expr_id "x1")
         (expr_op1 unary_op_prim_to_num (expr_id "x2"))))
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "string"))
         (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "number"))
         expr_false)
        (expr_break "ret"
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_prim_to_num (expr_id "x1")) (expr_id "x2")))
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "boolean"))
         (expr_break "ret"
          (expr_app (expr_id "eqeq")
           [expr_op1 unary_op_prim_to_num (expr_id "x1"); expr_id "x2"]))
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "boolean"))
          (expr_break "ret"
           (expr_app (expr_id "eqeq")
            [expr_id "x1"; expr_op1 unary_op_prim_to_num (expr_id "x2")]))
          (expr_if
           (expr_if
            (expr_let "%or"
             (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "string"))
             (expr_if (expr_id "%or") (expr_id "%or")
              (expr_op2 binary_op_stx_eq (expr_id "t1")
               (expr_string "number"))))
            (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "object"))
            expr_false)
           (expr_break "ret"
            (expr_app (expr_id "eqeq")
             [expr_id "x1"; expr_app (expr_id "%ToPrimitive") [expr_id "x2"]]))
           (expr_if
            (expr_if
             (expr_let "%or"
              (expr_op2 binary_op_stx_eq (expr_id "t2")
               (expr_string "string"))
              (expr_if (expr_id "%or") (expr_id "%or")
               (expr_op2 binary_op_stx_eq (expr_id "t2")
                (expr_string "number"))))
             (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "object"))
             expr_false)
            (expr_break "ret"
             (expr_app (expr_id "eqeq")
              [expr_app (expr_id "%ToPrimitive") [expr_id "x1"]; expr_id "x2"]))
            (expr_break "ret" expr_false)))))))))))))
.
Definition privErrorProto :=  value_object 7 .
Definition privErrorConstructor := 
value_closure
(closure_intro [("%ErrorProto", privErrorProto); ("%ToString", privToString)]
 None ["this"; "args"]
 (expr_let "o"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "%ErrorProto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_op2 binary_op_ge
    (expr_get_field (expr_id "args") (expr_string "length"))
    (expr_number (JsNumber.of_int 1)))
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "o") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "o")) (expr_id "o"))))
.
Definition privErrorGlobalFuncObj :=  value_object 24 .
Definition proto :=  value_object 47 .
Definition privEvalErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", proto)] None
 ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privEvalErrorGlobalFuncObj :=  value_object 50 .
Definition privglobalContext :=  value_object 4 .
Definition privmakeContextVarDefiner := 
value_closure
(closure_intro
 [("%UnboundId", privUnboundId);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None []
 (expr_let "envstore"
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined) [])
  (expr_lambda ["context"; "id"]
   (expr_let "envstore"
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "context")
      (expr_id "%globalContext")) (expr_id "%global") (expr_id "envstore"))
    (expr_if
     (expr_op2 binary_op_has_own_property (expr_id "context") (expr_id "id"))
     (expr_seq
      (expr_if
       (expr_op1 unary_op_not
        (expr_op2 binary_op_has_property (expr_id "envstore") (expr_id "id")))
       (expr_let "$newVal" expr_undefined
        (expr_set_field (expr_id "envstore") (expr_id "id")
         (expr_id "$newVal"))) expr_undefined) expr_undefined)
     (expr_seq
      (expr_let "$newVal" expr_undefined
       (expr_set_field (expr_id "envstore") (expr_id "id")
        (expr_id "$newVal")))
      (expr_let "%setter"
       (expr_object
        (objattrs_intro (expr_string "Object") expr_true expr_null
         (expr_lambda ["this"; "args"]
          (expr_if
           (expr_op2 binary_op_has_property (expr_id "envstore")
            (expr_id "id"))
           (expr_let "$newVal"
            (expr_get_field (expr_id "args") (expr_string "0"))
            (expr_set_field (expr_id "envstore") (expr_id "id")
             (expr_id "$newVal")))
           (expr_app (expr_id "%UnboundId") [expr_id "id"]))) expr_undefined)
        [])
       (expr_let "%getter"
        (expr_object
         (objattrs_intro (expr_string "Object") expr_true expr_null
          (expr_lambda ["this"; "args"]
           (expr_if
            (expr_op2 binary_op_has_property (expr_id "envstore")
             (expr_id "id"))
            (expr_get_field (expr_id "envstore") (expr_id "id"))
            (expr_app (expr_id "%UnboundId") [expr_id "id"]))) expr_undefined)
         [])
        (expr_app (expr_id "%defineOwnProperty")
         [expr_id "context";
          expr_id "id";
          expr_object
          (objattrs_intro (expr_string "Object") expr_true expr_null
           expr_null expr_undefined)
          [("get", property_data
                   (data_intro (expr_id "%getter") expr_true expr_false
                    expr_false));
           ("set", property_data
                   (data_intro (expr_id "%setter") expr_true expr_false
                    expr_false))]])))))))))
.
Definition privmakeGlobalEnv :=  value_object 1 .
Definition privconfigurableEval := 
value_closure
(closure_intro
 [("%makeContextVarDefiner", privmakeContextVarDefiner);
  ("%makeGlobalEnv", privmakeGlobalEnv)] None
 ["evalThis"; "evalContext"; "useStrict"; "args"]
 (expr_let "evalStr" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_let "evalStr"
   (expr_if (expr_id "useStrict")
    (expr_op2 binary_op_string_plus (expr_string "'use strict';")
     (expr_id "evalStr")) (expr_id "evalStr"))
   (expr_let "globalEnv"
    (expr_get_field (expr_id "%makeGlobalEnv") (expr_string "make"))
    (expr_seq
     (expr_let "$newVal" (expr_id "evalThis")
      (expr_set_field (expr_id "globalEnv") (expr_string "%this")
       (expr_id "$newVal")))
     (expr_seq
      (expr_let "$newVal"
       (expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "evalContext") expr_null expr_true) [])
       (expr_set_field (expr_id "globalEnv") (expr_string "%strictContext")
        (expr_id "$newVal")))
      (expr_seq
       (expr_let "$newVal" (expr_id "evalContext")
        (expr_set_field (expr_id "globalEnv")
         (expr_string "%nonstrictContext") (expr_id "$newVal")))
       (expr_seq
        (expr_let "$newVal" (expr_app (expr_id "%makeContextVarDefiner") [])
         (expr_set_field (expr_id "globalEnv")
          (expr_string "%defineGlobalVar") (expr_id "$newVal")))
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "evalStr"))
          (expr_string "string"))
         (expr_eval (expr_id "evalStr") (expr_id "globalEnv"))
         (expr_id "evalStr"))))))))))
.
Definition privevallambda := 
value_closure
(closure_intro
 [("%configurableEval", privconfigurableEval);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None ["this"; "args"]
 (expr_app (expr_id "%configurableEval")
  [expr_id "%global"; expr_id "%globalContext"; expr_false; expr_id "args"]))
.
Definition privFunctionConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("%evallambda", privevallambda)]
 None ["this"; "args"]
 (expr_let "argCount"
  (expr_get_field (expr_id "args") (expr_string "length"))
  (expr_recc "formArgString"
   (expr_lambda ["n"; "result"]
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "n")
      (expr_op2 binary_op_sub (expr_id "argCount")
       (expr_number (JsNumber.of_int 1)))) (expr_id "result")
     (expr_let "currentArg"
      (expr_app (expr_id "%ToString")
       [expr_get_field (expr_id "args")
        (expr_op1 unary_op_prim_to_str (expr_id "n"))])
      (expr_let "next"
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "n")
         (expr_op2 binary_op_sub (expr_id "argCount")
          (expr_number (JsNumber.of_int 2))))
        (expr_op2 binary_op_string_plus (expr_id "result")
         (expr_id "currentArg"))
        (expr_op2 binary_op_string_plus
         (expr_op2 binary_op_string_plus (expr_id "result")
          (expr_id "currentArg")) (expr_string ",")))
       (expr_app (expr_id "formArgString")
        [expr_op2 binary_op_add (expr_id "n")
         (expr_number (JsNumber.of_int 1));
         expr_id "next"])))))
   (expr_let "body"
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "argCount")
      (expr_number (JsNumber.of_int 0))) (expr_string "")
     (expr_get_field (expr_id "args")
      (expr_op1 unary_op_prim_to_str
       (expr_op2 binary_op_sub (expr_id "argCount")
        (expr_number (JsNumber.of_int 1))))))
    (expr_let "P"
     (expr_if
      (expr_let "%or"
       (expr_op2 binary_op_stx_eq (expr_id "argCount")
        (expr_number (JsNumber.of_int 0)))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "argCount")
         (expr_number (JsNumber.of_int 1))))) (expr_string "")
      (expr_app (expr_id "formArgString")
       [expr_number (JsNumber.of_int 0); expr_string ""]))
     (expr_let "prefix"
      (expr_op2 binary_op_string_plus
       (expr_string "((function(){ return function (")
       (expr_op2 binary_op_string_plus (expr_id "P") (expr_string "){")))
      (expr_let "final"
       (expr_op2 binary_op_string_plus (expr_id "prefix")
        (expr_op2 binary_op_string_plus (expr_id "body")
         (expr_string "}; })());")))
       (expr_app (expr_id "%evallambda")
        [expr_undefined;
         expr_object
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined)
         [("0", property_data
                (data_intro (expr_id "final") expr_false expr_false
                 expr_false))]]))))))))
.
Definition privFunctionGlobalFuncObj :=  value_object 317 .
Definition privFunctionProto :=  value_object 5 .
Definition privGetterValue := 
value_closure
(closure_intro [] None ["o"]
 (expr_get_field (expr_id "o") (expr_string "func")))
.
Definition privGreaterEqual := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 (expr_let "result"
  (expr_app (expr_id "%CompareOp") [expr_id "l"; expr_id "r"; expr_true])
  (expr_if
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
    expr_false expr_true) (expr_op1 unary_op_not (expr_id "result"))
   expr_false)))
.
Definition privGreaterThan := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 (expr_let "result"
  (expr_app (expr_id "%CompareOp") [expr_id "r"; expr_id "l"; expr_false])
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
   expr_false (expr_id "result"))))
.
Definition privImmut := 
value_closure
(closure_intro [] None ["obj"; "prop"]
 (expr_seq (expr_op1 unary_op_pretty (expr_id "obj"))
  (expr_seq
   (expr_set_attr pattr_enum (expr_id "obj") (expr_id "prop") expr_false)
   (expr_set_attr pattr_config (expr_id "obj") (expr_id "prop") expr_false))))
.
Definition privIsObject := 
value_closure
(closure_intro [] None ["o"]
 (expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
  (expr_let "c1"
   (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
   (expr_let "c2"
    (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
    (expr_let "%or" (expr_id "c1")
     (expr_if (expr_id "%or") (expr_id "%or") (expr_id "c2")))))))
.
Definition privIsPrototypeOflambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 (expr_recc "searchChain"
  (expr_lambda ["o"; "v"]
   (expr_let "vproto" (expr_get_obj_attr oattr_proto (expr_id "v"))
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "vproto") expr_null)
     expr_false
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "o") (expr_id "vproto"))
      expr_true
      (expr_app (expr_id "searchChain") [expr_id "o"; expr_id "vproto"])))))
  (expr_let "vtype"
   (expr_op1 unary_op_typeof
    (expr_get_field (expr_id "args") (expr_string "0")))
   (expr_if
    (expr_if
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq (expr_id "vtype") (expr_string "object")))
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq (expr_id "vtype") (expr_string "function")))
     expr_false) expr_false
    (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
     (expr_app (expr_id "searchChain")
      [expr_id "O"; expr_get_field (expr_id "args") (expr_string "0")]))))))
.
Definition privLeftShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"]
 (expr_op2 binary_op_shiftl (expr_app (expr_id "%ToInt32") [expr_id "l"])
  (expr_app (expr_id "%ToUint32") [expr_id "r"])))
.
Definition privLessEqual := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 (expr_let "result"
  (expr_app (expr_id "%CompareOp") [expr_id "r"; expr_id "l"; expr_false])
  (expr_if
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
    expr_false expr_true) (expr_op1 unary_op_not (expr_id "result"))
   expr_false)))
.
Definition privLessThan := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 (expr_let "result"
  (expr_app (expr_id "%CompareOp") [expr_id "l"; expr_id "r"; expr_true])
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
   expr_false (expr_id "result"))))
.
Definition privMath :=  value_object 262 .
Definition privNativeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString)] None ["proto"]
 (expr_lambda ["this"; "args"]
  (expr_let "rtn"
   (expr_object
    (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
     expr_null expr_undefined) [])
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
     expr_false expr_true)
    (expr_seq
     (expr_let "$newVal"
      (expr_app (expr_id "%ToString")
       [expr_get_field (expr_id "args") (expr_string "0")])
      (expr_set_field (expr_id "rtn") (expr_string "message")
       (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn")))))
.
Definition privNumberConstructor := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto); ("%ToNumber", privToNumber)] None
 ["this"; "args"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_field (expr_id "args") (expr_string "length"))
    (expr_number (JsNumber.of_int 0))) (expr_number (JsNumber.of_int 0))
   (expr_app (expr_id "%ToNumber")
    [expr_get_field (expr_id "args") (expr_string "0")]))
  (expr_let "hasProp"
   (expr_op2 binary_op_has_property (expr_id "args") (expr_string "0"))
   (expr_let "argUndef"
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    (expr_let "v"
     (expr_if (expr_if (expr_id "hasProp") (expr_id "argUndef") expr_false)
      (expr_number (JsNumber.of_int 0))
      (expr_if (expr_id "argUndef") (expr_number (JsNumber.of_int 0))
       (expr_app (expr_id "%ToNumber")
        [expr_get_field (expr_id "args") (expr_string "0")])))
     (expr_object
      (objattrs_intro (expr_string "Number") expr_true
       (expr_id "%NumberProto") expr_null (expr_id "v")) []))))))
.
Definition privNumberGlobalFuncObj :=  value_object 27 .
Definition privObjectProto :=  value_object 2 .
Definition privObjectConstructor := 
value_closure
(closure_intro
 [("%ObjectProto", privObjectProto); ("%ToObject", privToObject)] None
 ["this"; "args"]
 (expr_let "calledAsFunction"
  (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
  (expr_let "hasArg"
   (expr_op2 binary_op_gt
    (expr_get_field (expr_id "args") (expr_string "length"))
    (expr_number (JsNumber.of_int 0)))
   (expr_let "notNull"
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq
      (expr_get_field (expr_id "args") (expr_string "0")) expr_null))
    (expr_let "notUndefined"
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq
       (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined))
     (expr_let "shouldReturnEarly"
      (expr_if
       (expr_if
        (expr_if (expr_id "calledAsFunction") (expr_id "hasArg") expr_false)
        (expr_id "notNull") expr_false) (expr_id "notUndefined") expr_false)
      (expr_let "defaultRtn"
       (expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "%ObjectProto") expr_null expr_undefined) [])
       (expr_if (expr_id "shouldReturnEarly")
        (expr_app (expr_id "%ToObject")
         [expr_get_field (expr_id "args") (expr_string "0")])
        (expr_if (expr_id "hasArg")
         (expr_let "argtype"
          (expr_op1 unary_op_typeof
           (expr_get_field (expr_id "args") (expr_string "0")))
          (expr_let "isArgObject"
           (expr_let "%or"
            (expr_op2 binary_op_stx_eq (expr_id "argtype")
             (expr_string "object"))
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_op2 binary_op_stx_eq (expr_id "argtype")
              (expr_string "function"))))
           (expr_let "isArgSomething"
            (expr_let "%or"
             (expr_let "%or"
              (expr_op2 binary_op_stx_eq (expr_id "argtype")
               (expr_string "boolean"))
              (expr_if (expr_id "%or") (expr_id "%or")
               (expr_op2 binary_op_stx_eq (expr_id "argtype")
                (expr_string "string"))))
             (expr_if (expr_id "%or") (expr_id "%or")
              (expr_op2 binary_op_stx_eq (expr_id "argtype")
               (expr_string "number"))))
            (expr_if (expr_id "isArgObject")
             (expr_get_field (expr_id "args") (expr_string "0"))
             (expr_if (expr_id "isArgSomething")
              (expr_app (expr_id "%ToObject")
               [expr_get_field (expr_id "args") (expr_string "0")])
              (expr_id "defaultRtn")))))) (expr_id "defaultRtn"))))))))))
.
Definition privObjectGlobalFuncObj :=  value_object 36 .
Definition privObjectTypeCheck := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 (expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
  (expr_let "c1"
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
    expr_false expr_true)
   (expr_let "c2"
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
     expr_false expr_true)
    (expr_if (expr_if (expr_id "c1") (expr_id "c2") expr_false)
     (expr_app (expr_id "%TypeError")
      [expr_op2 binary_op_string_plus
       (expr_op1 unary_op_prim_to_str (expr_id "o"))
       (expr_string " is not an object")]) expr_null)))))
.
Definition privPostfixOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "fld"; "op"]
 (expr_let "oldValue"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "obj") (expr_id "fld")])
  (expr_let "newValue"
   (expr_app (expr_id "op")
    [expr_id "oldValue"; expr_number (JsNumber.of_int 1)])
   (expr_seq
    (expr_let "$newVal" (expr_id "newValue")
     (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal")))
    (expr_id "oldValue")))))
.
Definition privPrimSub := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["l"; "r"]
 (expr_let "l" (expr_app (expr_id "%ToNumber") [expr_id "l"])
  (expr_let "r" (expr_app (expr_id "%ToNumber") [expr_id "r"])
   (expr_op2 binary_op_sub (expr_id "l") (expr_id "r")))))
.
Definition privPostDecrement := 
value_closure
(closure_intro [("%PostfixOp", privPostfixOp); ("%PrimSub", privPrimSub)]
 None ["obj"; "fld"]
 (expr_app (expr_id "%PostfixOp")
  [expr_id "obj"; expr_id "fld"; expr_id "%PrimSub"]))
.
Definition privPrimAdd := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] None ["l"; "r"]
 (expr_let "l" (expr_app (expr_id "%ToPrimitive") [expr_id "l"])
  (expr_let "r" (expr_app (expr_id "%ToPrimitive") [expr_id "r"])
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "l"))
     (expr_string "string"))
    (expr_let "lstr" (expr_op1 unary_op_prim_to_str (expr_id "l"))
     (expr_let "rstr" (expr_op1 unary_op_prim_to_str (expr_id "r"))
      (expr_op2 binary_op_string_plus (expr_id "lstr") (expr_id "rstr"))))
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "r"))
      (expr_string "string"))
     (expr_let "lstr" (expr_op1 unary_op_prim_to_str (expr_id "l"))
      (expr_let "rstr" (expr_op1 unary_op_prim_to_str (expr_id "r"))
       (expr_op2 binary_op_string_plus (expr_id "lstr") (expr_id "rstr"))))
     (expr_let "lnum" (expr_op1 unary_op_prim_to_num (expr_id "l"))
      (expr_let "rnum" (expr_op1 unary_op_prim_to_num (expr_id "r"))
       (expr_op2 binary_op_add (expr_id "lnum") (expr_id "rnum")))))))))
.
Definition privPostIncrement := 
value_closure
(closure_intro [("%PostfixOp", privPostfixOp); ("%PrimAdd", privPrimAdd)]
 None ["obj"; "fld"]
 (expr_app (expr_id "%PostfixOp")
  [expr_id "obj"; expr_id "fld"; expr_id "%PrimAdd"]))
.
Definition privPrefixOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "fld"; "op"]
 (expr_let "oldValue"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "obj") (expr_id "fld")])
  (expr_let "newValue"
   (expr_app (expr_id "op")
    [expr_id "oldValue"; expr_number (JsNumber.of_int 1)])
   (expr_seq
    (expr_let "$newVal" (expr_id "newValue")
     (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal")))
    (expr_id "newValue")))))
.
Definition privPrefixDecrement := 
value_closure
(closure_intro [("%PrefixOp", privPrefixOp); ("%PrimSub", privPrimSub)] 
 None ["obj"; "fld"]
 (expr_app (expr_id "%PrefixOp")
  [expr_id "obj"; expr_id "fld"; expr_id "%PrimSub"]))
.
Definition privPrefixIncrement := 
value_closure
(closure_intro [("%PrefixOp", privPrefixOp); ("%PrimAdd", privPrimAdd)] 
 None ["obj"; "fld"]
 (expr_app (expr_id "%PrefixOp")
  [expr_id "obj"; expr_id "fld"; expr_id "%PrimAdd"]))
.
Definition privPrimMultOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["l"; "r"; "op"]
 (expr_let "lNum" (expr_app (expr_id "%ToNumber") [expr_id "l"])
  (expr_let "rNum" (expr_app (expr_id "%ToNumber") [expr_id "r"])
   (expr_app (expr_id "op") [expr_id "lNum"; expr_id "rNum"]))))
.
Definition privPrimNew := 
value_closure
(closure_intro
 [("%AppExprCheck", privAppExprCheck);
  ("%IsObject", privIsObject);
  ("%ObjectProto", privObjectProto)] None ["constr"; "args"]
 (expr_let "cproto1"
  (expr_get_field (expr_id "constr") (expr_string "prototype"))
  (expr_let "cproto"
   (expr_if (expr_app (expr_id "%IsObject") [expr_id "cproto1"])
    (expr_id "cproto1") (expr_id "%ObjectProto"))
   (expr_let "newobj"
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true (expr_id "cproto")
      expr_null expr_undefined) [])
    (expr_let "constr_ret"
     (expr_app (expr_id "%AppExprCheck")
      [expr_id "constr"; expr_id "newobj"; expr_id "args"])
     (expr_if (expr_app (expr_id "%IsObject") [expr_id "constr_ret"])
      (expr_id "constr_ret") (expr_id "newobj")))))))
.
Definition privPropAccessorCheck := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto);
  ("%ToObject", privToObject)] None ["o"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "o") expr_undefined)
  (expr_throw
   (expr_app (expr_id "%JSError")
    [expr_object
     (objattrs_intro (expr_string "Object") expr_true
      (expr_id "%ReferenceErrorProto") expr_null expr_undefined) []]))
  (expr_app (expr_id "%ToObject") [expr_id "o"])))
.
Definition privRangeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privRangeErrorProto)]
 None ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privRangeErrorGlobalFuncObj :=  value_object 52 .
Definition privReferenceErrorConstructor := 
value_closure
(closure_intro
 [("%ToString", privToString); ("proto", privReferenceErrorProto)] None
 ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privReferenceErrorGlobalFuncObj :=  value_object 54 .
Definition privRegExpProto :=  value_object 254 .
Definition privRegExpConstructor := 
value_closure
(closure_intro [("%RegExpProto", privRegExpProto)] None ["this"; "args"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true (expr_id "%RegExpProto")
   expr_null expr_undefined) []))
.
Definition privRegExpGlobalFuncObj :=  value_object 255 .
Definition privSignedRightShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"]
 (expr_op2 binary_op_shiftr (expr_app (expr_id "%ToInt32") [expr_id "l"])
  (expr_app (expr_id "%ToUint32") [expr_id "r"])))
.
Definition privStringConstructor := 
value_closure
(closure_intro
 [("%StringIndices", privStringIndices);
  ("%StringProto", privStringProto);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_let "S"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_field (expr_id "args") (expr_string "length"))
    (expr_number (JsNumber.of_int 0))) (expr_string "")
   (expr_app (expr_id "%ToString")
    [expr_get_field (expr_id "args") (expr_string "0")]))
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
   (expr_id "S")
   (expr_let "obj"
    (expr_object
     (objattrs_intro (expr_string "String") expr_true
      (expr_id "%StringProto") expr_null (expr_id "S"))
     [("length", property_data
                 (data_intro (expr_op1 unary_op_strlen (expr_id "S"))
                  expr_true expr_false expr_false))])
    (expr_seq
     (expr_app (expr_id "%StringIndices") [expr_id "obj"; expr_id "S"])
     (expr_id "obj"))))))
.
Definition privStringGlobalFuncObj :=  value_object 30 .
Definition privStringIndexOf :=  value_object 163 .
Definition privmax := 
value_closure
(closure_intro [] None ["a"; "b"]
 (expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "b")
  (expr_id "a")))
.
Definition privmin := 
value_closure
(closure_intro [] None ["a"; "b"]
 (expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "a")
  (expr_id "b")))
.
Definition privStringIndexOflambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "searchStr"
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_let "pos"
     (expr_app (expr_id "%ToInteger")
      [expr_get_field (expr_id "args") (expr_string "1")])
     (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
      (expr_let "start"
       (expr_app (expr_id "%min")
        [expr_app (expr_id "%max")
         [expr_id "pos"; expr_number (JsNumber.of_int 0)];
         expr_id "len"])
       (expr_let "searchLen" (expr_op1 unary_op_strlen (expr_id "searchStr"))
        (expr_let "check_k"
         (expr_lambda ["k"]
          (expr_recc "check_j"
           (expr_lambda ["j"]
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "j") (expr_id "searchLen"))
             expr_true
             (expr_if
              (expr_if
               (expr_op2 binary_op_stx_eq
                (expr_op2 binary_op_char_at (expr_id "S")
                 (expr_op2 binary_op_add (expr_id "k") (expr_id "j")))
                (expr_op2 binary_op_char_at (expr_id "searchStr")
                 (expr_id "j"))) expr_false expr_true) expr_false
              (expr_app (expr_id "check_j")
               [expr_op2 binary_op_add (expr_id "j")
                (expr_number (JsNumber.of_int 1))]))))
           (expr_if
            (expr_op1 unary_op_not
             (expr_op2 binary_op_le
              (expr_op2 binary_op_add (expr_id "k") (expr_id "searchLen"))
              (expr_id "len"))) expr_false
            (expr_if
             (expr_op1 unary_op_not
              (expr_app (expr_id "check_j") [expr_number (JsNumber.of_int 0)]))
             expr_false expr_true))))
         (expr_recc "find_k"
          (expr_lambda ["curr"]
           (expr_if
            (expr_op2 binary_op_gt
             (expr_op2 binary_op_add (expr_id "curr") (expr_id "searchLen"))
             (expr_id "len"))
            (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
             (expr_number (JsNumber.of_int 1)))
            (expr_if (expr_app (expr_id "check_k") [expr_id "curr"])
             (expr_id "curr")
             (expr_app (expr_id "find_k")
              [expr_op2 binary_op_add (expr_id "curr")
               (expr_number (JsNumber.of_int 1))]))))
          (expr_app (expr_id "find_k") [expr_id "start"])))))))))))
.
Definition privStringLastIndexOf :=  value_object 165 .
Definition privSyntaxErrorProto :=  value_object 11 .
Definition privSyntaxError := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%SyntaxErrorProto", privSyntaxErrorProto)]
 None ["msg"]
 (expr_throw
  (expr_app (expr_id "%JSError")
   [expr_object
    (objattrs_intro (expr_string "Object") expr_true
     (expr_id "%SyntaxErrorProto") expr_null expr_undefined)
    [("message", property_data
                 (data_intro
                  (expr_op2 binary_op_string_plus
                   (expr_string "ReferenceError: ") (expr_id "msg"))
                  expr_true expr_false expr_false))]])))
.
Definition privSyntaxErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privSyntaxErrorProto)]
 None ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privSyntaxErrorGlobalFuncObj :=  value_object 49 .
Definition privThrowReferenceError :=  value_object 15 .
Definition privThrowSyntaxError :=  value_object 16 .
Definition privThrowTypeError :=  value_object 9 .
Definition privTimeWithinDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"]
 (expr_op2 binary_op_mod (expr_id "t") (expr_id "%msPerDay")))
.
Definition privToJSError := 
value_closure
(closure_intro
 [("%IsJSError", privIsJSError); ("%MakeTypeError", privMakeTypeError)] 
 None ["maybe-js-error"]
 (expr_if (expr_app (expr_id "%IsJSError") [expr_id "maybe-js-error"])
  (expr_get_field (expr_id "maybe-js-error") (expr_string "%js-exn"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
    (expr_string "unwritable-field"))
   (expr_app (expr_id "%MakeTypeError") [expr_string "Field not writable"])
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
     (expr_string "unconfigurable-delete"))
    (expr_app (expr_id "%MakeTypeError") [expr_string "Field not deletable"])
    (expr_throw (expr_id "maybe-js-error"))))))
.
Definition privToUint16 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"]
 (expr_app (expr_id "%ToUint")
  [expr_id "n"; expr_number (JsNumber.of_int 65536)]))
.
Definition privTypeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privTypeErrorProto)]
 None ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privTypeErrorGlobalFuncObj :=  value_object 56 .
Definition privTypeof := 
value_closure
(closure_intro [] None ["context"; "id"]
 (expr_try_catch
  (expr_op1 unary_op_typeof
   (expr_get_field (expr_id "context") (expr_id "id")))
  (expr_lambda ["e"] (expr_string "undefined"))))
.
Definition proto1 :=  value_object 57 .
Definition privURIErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", proto1)] None
 ["this"; "args"]
 (expr_let "rtn"
  (expr_object
   (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
    expr_null expr_undefined) [])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
    expr_false expr_true)
   (expr_seq
    (expr_let "$newVal"
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_set_field (expr_id "rtn") (expr_string "message")
      (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))))
.
Definition privURIErrorGlobalFuncObj :=  value_object 58 .
Definition privUnaryNeg := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"]
 (expr_let "oldValue" (expr_app (expr_id "%ToNumber") [expr_id "expr"])
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "oldValue") (expr_id "oldValue"))
    expr_false expr_true) (expr_id "oldValue")
   (expr_let "negOne"
    (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
     (expr_number (JsNumber.of_int 1)))
    (expr_op2 binary_op_mul (expr_id "oldValue") (expr_id "negOne"))))))
.
Definition privUnaryPlus := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"]
 (expr_app (expr_id "%ToNumber") [expr_id "expr"]))
.
Definition privUnsignedRightShift := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["l"; "r"]
 (expr_op2 binary_op_zfshiftr (expr_app (expr_id "%ToUint32") [expr_id "l"])
  (expr_app (expr_id "%ToUint32") [expr_id "r"])))
.
Definition privacos :=  value_object 271 .
Definition privacosLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "acos NYI"))
.
Definition privaiolambda := 
value_closure
(closure_intro
 [("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%max", privmax)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "negOne"
     (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
      (expr_number (JsNumber.of_int 1)))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "len")
         (expr_number (JsNumber.of_int 0)))
        (expr_break "ret" (expr_id "negOne")) expr_undefined)
       (expr_let "n"
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_field (expr_id "args") (expr_string "1")) expr_undefined)
         (expr_number (JsNumber.of_int 0))
         (expr_app (expr_id "%ToInteger")
          [expr_get_field (expr_id "args") (expr_string "1")]))
        (expr_seq
         (expr_if (expr_op2 binary_op_ge (expr_id "n") (expr_id "len"))
          (expr_break "ret" (expr_id "negOne")) expr_undefined)
         (expr_recc "loop"
          (expr_lambda ["k"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "kStr" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_if
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "kStr"))
              (expr_seq
               (expr_let "elementK"
                (expr_get_field (expr_id "O") (expr_id "kStr"))
                (expr_if
                 (expr_op2 binary_op_stx_eq
                  (expr_get_field (expr_id "args") (expr_string "0"))
                  (expr_id "elementK")) (expr_break "ret" (expr_id "k"))
                 expr_undefined))
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int 1))]))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1))]))) expr_undefined))
          (expr_let "start"
           (expr_if
            (expr_op2 binary_op_ge (expr_id "n")
             (expr_number (JsNumber.of_int 0))) (expr_id "n")
            (expr_app (expr_id "%max")
             [expr_op2 binary_op_sub (expr_id "len")
              (expr_op1 unary_op_abs (expr_id "n"));
              expr_number (JsNumber.of_int 0)]))
           (expr_seq (expr_app (expr_id "loop") [expr_id "start"])
            (expr_break "ret" (expr_id "negOne"))))))))))))))
.
Definition privaliolambda := 
value_closure
(closure_intro
 [("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%min", privmin)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "negOne"
     (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
      (expr_number (JsNumber.of_int 1)))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "len")
         (expr_number (JsNumber.of_int 0)))
        (expr_break "ret" (expr_id "negOne")) expr_undefined)
       (expr_seq
        (expr_let "n"
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "args") (expr_string "1")) expr_undefined)
          (expr_op2 binary_op_sub (expr_id "len")
           (expr_number (JsNumber.of_int 1)))
          (expr_app (expr_id "%ToInteger")
           [expr_get_field (expr_id "args") (expr_string "1")]))
         (expr_recc "loop"
          (expr_lambda ["k"]
           (expr_if
            (expr_op2 binary_op_ge (expr_id "k")
             (expr_number (JsNumber.of_int 0)))
            (expr_let "kstr" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_if
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "kstr"))
              (expr_if
               (expr_op2 binary_op_stx_eq
                (expr_get_field (expr_id "O") (expr_id "kstr"))
                (expr_get_field (expr_id "args") (expr_string "0")))
               (expr_break "ret" (expr_id "k"))
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_sub (expr_id "k")
                 (expr_number (JsNumber.of_int 1))]))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_sub (expr_id "k")
                (expr_number (JsNumber.of_int 1))]))) expr_undefined))
          (expr_let "start"
           (expr_if
            (expr_op2 binary_op_ge (expr_id "n")
             (expr_number (JsNumber.of_int 0)))
            (expr_app (expr_id "%min")
             [expr_id "n";
              expr_op2 binary_op_sub (expr_id "len")
              (expr_number (JsNumber.of_int 1))])
            (expr_op2 binary_op_sub (expr_id "len")
             (expr_op1 unary_op_abs (expr_id "n"))))
           (expr_app (expr_id "loop") [expr_id "start"]))))
        (expr_break "ret" (expr_id "negOne"))))))))))
.
Definition privapply :=  value_object 20 .
Definition privmkArgsObjBase := 
value_closure
(closure_intro
 [("%MakeGetter", privMakeGetter);
  ("%MakeSetter", privMakeSetter);
  ("%ObjectProto", privObjectProto);
  ("%ThrowTypeError", privThrowTypeError);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["args"]
 (expr_let "keys" (expr_own_field_names (expr_id "args"))
  (expr_let "argsObj"
   (expr_object
    (objattrs_intro (expr_string "Arguments") expr_true
     (expr_id "%ObjectProto") expr_null expr_undefined)
    [("callee", property_accessor
                (accessor_intro
                 (expr_app (expr_id "%MakeGetter")
                  [expr_id "%ThrowTypeError"])
                 (expr_app (expr_id "%MakeSetter")
                  [expr_id "%ThrowTypeError"]) expr_false expr_true));
     ("caller", property_accessor
                (accessor_intro
                 (expr_app (expr_id "%MakeGetter")
                  [expr_id "%ThrowTypeError"])
                 (expr_app (expr_id "%MakeSetter")
                  [expr_id "%ThrowTypeError"]) expr_false expr_true))])
   (expr_seq
    (expr_set_attr pattr_config (expr_id "argsObj") (expr_string "callee")
     expr_false)
    (expr_seq
     (expr_set_attr pattr_config (expr_id "argsObj") (expr_string "caller")
      expr_false)
     (expr_recc "loop"
      (expr_lambda ["iter"]
       (expr_let "strx" (expr_app (expr_id "%ToString") [expr_id "iter"])
        (expr_if
         (expr_op2 binary_op_has_own_property (expr_id "keys")
          (expr_id "strx"))
         (expr_seq
          (expr_app (expr_id "%defineOwnProperty")
           [expr_id "argsObj";
            expr_id "strx";
            expr_object
            (objattrs_intro (expr_string "Object") expr_true expr_null
             expr_null expr_undefined)
            [("value", property_data
                       (data_intro
                        (expr_get_field (expr_id "args") (expr_id "strx"))
                        expr_false expr_false expr_false));
             ("writable", property_data
                          (data_intro expr_true expr_false expr_false
                           expr_false));
             ("configurable", property_data
                              (data_intro expr_true expr_false expr_false
                               expr_false));
             ("enumerable", property_data
                            (data_intro expr_true expr_false expr_false
                             expr_false))]])
          (expr_app (expr_id "loop")
           [expr_op2 binary_op_add (expr_id "iter")
            (expr_number (JsNumber.of_int 1))]))
         (expr_app (expr_id "%defineOwnProperty")
          [expr_id "argsObj";
           expr_string "length";
           expr_object
           (objattrs_intro (expr_string "Object") expr_true expr_null
            expr_null expr_undefined)
           [("value", property_data
                      (data_intro (expr_id "iter") expr_false expr_false
                       expr_false));
            ("writable", property_data
                         (data_intro expr_true expr_false expr_false
                          expr_false));
            ("configurable", property_data
                             (data_intro expr_true expr_false expr_false
                              expr_false));
            ("enumerable", property_data
                           (data_intro expr_false expr_false expr_false
                            expr_false))]]))))
      (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
       (expr_id "argsObj"))))))))
.
Definition privmkArgsObj := 
value_closure
(closure_intro [("%mkArgsObjBase", privmkArgsObjBase)] None ["args"]
 (expr_let "argsObj" (expr_app (expr_id "%mkArgsObjBase") [expr_id "args"])
  (expr_seq
   (expr_let "$newVal" expr_false
    (expr_set_field (expr_id "argsObj") (expr_string "%new")
     (expr_id "$newVal")))
   (expr_seq
    (expr_set_attr pattr_writable (expr_id "argsObj") (expr_string "%new")
     expr_false) (expr_id "argsObj")))))
.
Definition privapplylambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck); ("%mkArgsObj", privmkArgsObj)]
 None ["this"; "args"]
 (expr_let "applyArgs1" (expr_get_field (expr_id "args") (expr_string "1"))
  (expr_let "applyArgs"
   (expr_if
    (expr_let "%or"
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_typeof (expr_id "applyArgs1"))
      (expr_string "undefined"))
     (expr_if (expr_id "%or") (expr_id "%or")
      (expr_op2 binary_op_stx_eq (expr_id "applyArgs1") expr_null)))
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
      expr_undefined) []) (expr_id "applyArgs1"))
   (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "applyArgs"])
    (expr_app (expr_id "this")
     [expr_get_field (expr_id "args") (expr_string "0");
      expr_app (expr_id "%mkArgsObj") [expr_id "applyArgs"]])))))
.
Definition privarrayIndexOf :=  value_object 128 .
Definition privarrayLastIndexOf :=  value_object 131 .
Definition privarrayTLSlambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ToObject", privToObject);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%TypeErrorProto", privTypeErrorProto)] None ["this"; "args"]
 (expr_let "isCallable"
  (expr_lambda ["o"]
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_if
       (expr_op1 unary_op_not
        (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "o"))
         (expr_string "object")))
       (expr_op1 unary_op_not
        (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "o"))
         (expr_string "function"))) expr_false) (expr_break "ret" expr_false)
      expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_obj_attr oattr_code (expr_id "o")) expr_null)
       (expr_break "ret" expr_false) expr_null) (expr_break "ret" expr_true)))))
  (expr_let "array" (expr_app (expr_id "%ToObject") [expr_id "this"])
   (expr_let "arrayLen"
    (expr_get_field (expr_id "array") (expr_string "length"))
    (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "arrayLen"])
     (expr_let "separator" (expr_string " ")
      (expr_label "ret"
       (expr_seq
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "len")
          (expr_number (JsNumber.of_int 0)))
         (expr_break "ret" (expr_string "")) expr_null)
        (expr_let "firstElement"
         (expr_get_field (expr_id "array") (expr_string "0"))
         (expr_let "R"
          (expr_if
           (expr_let "%or"
            (expr_op2 binary_op_stx_eq (expr_id "firstElement") expr_null)
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_op2 binary_op_stx_eq (expr_id "firstElement")
              expr_undefined))) (expr_string "")
           (expr_let "elementObj"
            (expr_app (expr_id "%ToObject") [expr_id "firstElement"])
            (expr_let "funcc"
             (expr_get_field (expr_id "elementObj")
              (expr_string "toLocaleString"))
             (expr_seq
              (expr_if
               (expr_op1 unary_op_not
                (expr_app (expr_id "isCallable") [expr_id "funcc"]))
               (expr_app (expr_id "%TypeError")
                [expr_string "Not callable in ArrayTLS"]) expr_null)
              (expr_app (expr_id "funcc")
               [expr_id "elementObj";
                expr_object
                (objattrs_intro (expr_string "Object") expr_true expr_null
                 expr_null expr_undefined) []])))))
          (expr_recc "inner"
           (expr_lambda ["k"; "r"]
            (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "len"))
             (expr_id "r")
             (expr_let "S"
              (expr_op2 binary_op_string_plus
               (expr_op1 unary_op_prim_to_str (expr_id "r"))
               (expr_id "separator"))
              (expr_let "nextElement"
               (expr_get_field (expr_id "array")
                (expr_op1 unary_op_prim_to_str (expr_id "k")))
               (expr_let "toAppend"
                (expr_if
                 (expr_let "%or"
                  (expr_op2 binary_op_stx_eq (expr_id "nextElement")
                   expr_null)
                  (expr_if (expr_id "%or") (expr_id "%or")
                   (expr_op2 binary_op_stx_eq (expr_id "nextElement")
                    expr_undefined))) (expr_string "")
                 (expr_let "elementObj"
                  (expr_app (expr_id "%ToObject") [expr_id "nextElement"])
                  (expr_let "funcc"
                   (expr_get_field (expr_id "elementObj")
                    (expr_string "toLocaleString"))
                   (expr_seq
                    (expr_if
                     (expr_op1 unary_op_not
                      (expr_app (expr_id "isCallable") [expr_id "funcc"]))
                     (expr_throw
                      (expr_app (expr_id "%JSError")
                       [expr_object
                        (objattrs_intro (expr_string "Object") expr_true
                         (expr_id "%TypeErrorProto") expr_null expr_undefined)
                        []])) expr_null)
                    (expr_app (expr_id "funcc")
                     [expr_id "elementObj";
                      expr_object
                      (objattrs_intro (expr_string "Object") expr_true
                       expr_null expr_null expr_undefined) []])))))
                (expr_app (expr_id "inner")
                 [expr_op2 binary_op_add (expr_id "k")
                  (expr_number (JsNumber.of_int 1));
                  expr_op2 binary_op_string_plus
                  (expr_op1 unary_op_prim_to_str (expr_id "r"))
                  (expr_op1 unary_op_prim_to_str (expr_id "toAppend"))]))))))
           (expr_break "ret"
            (expr_app (expr_id "inner")
             [expr_number (JsNumber.of_int 1); expr_id "R"])))))))))))))
.
Definition privarrayToLocaleString :=  value_object 100 .
Definition privarrayToString :=  value_object 97 .
Definition privobjectToStringlambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 (expr_label "ret"
  (expr_seq
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
    (expr_break "ret" (expr_string "[object Undefined]")) expr_undefined)
   (expr_seq
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_null)
     (expr_break "ret" (expr_string "[object Null]")) expr_undefined)
    (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
     (expr_let "class" (expr_get_obj_attr oattr_class (expr_id "O"))
      (expr_break "ret"
       (expr_op2 binary_op_string_plus (expr_string "[object ")
        (expr_op2 binary_op_string_plus (expr_id "class") (expr_string "]"))))))))))
.
Definition privarrayToStringlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%objectToStringlambda", privobjectToStringlambda)] None ["this"; "args"]
 (expr_let "array" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "thefunc" (expr_get_field (expr_id "array") (expr_string "join"))
   (expr_let "ffunc"
    (expr_if
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq
        (expr_op1 unary_op_typeof (expr_id "thefunc")) (expr_string "object")))
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq
        (expr_op1 unary_op_typeof (expr_id "thefunc"))
        (expr_string "function"))) expr_false)
     (expr_id "%objectToStringlambda")
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_obj_attr oattr_code (expr_id "thefunc")) expr_null)
      (expr_id "%objectToStringlambda") (expr_id "thefunc")))
    (expr_app (expr_id "ffunc")
     [expr_id "array";
      expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined) []])))))
.
Definition privasin :=  value_object 273 .
Definition privasinLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "asin NYI"))
.
Definition privatan :=  value_object 275 .
Definition privatan2 :=  value_object 277 .
Definition privatan2Lambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "atan2 NYI"))
.
Definition privatanLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "atan NYI"))
.
Definition privbind :=  value_object 157 .
Definition privconcatLambda := 
value_closure
(closure_intro
 [("%ArrayConstructor", privArrayConstructor); ("%ToObject", privToObject)]
 None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "emptyobj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
     expr_undefined) [])
   (expr_let "A"
    (expr_app (expr_id "%ArrayConstructor")
     [expr_id "emptyobj"; expr_id "emptyobj"])
    (expr_recc "procElt"
     (expr_lambda ["obj"; "elt"; "n"]
      (expr_let "procNormalElt"
       (expr_lambda ["nelt"; "k"]
        (expr_seq
         (expr_let "$newVal" (expr_id "nelt")
          (expr_set_field (expr_id "obj")
           (expr_op1 unary_op_prim_to_str (expr_id "k")) (expr_id "$newVal")))
         (expr_op2 binary_op_add (expr_id "k")
          (expr_number (JsNumber.of_int 1)))))
       (expr_recc "procArrayElt"
        (expr_lambda ["arr"; "fromIndex"; "toIndex"]
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "arr")
            (expr_op1 unary_op_prim_to_str (expr_id "fromIndex")))
           expr_undefined) (expr_id "toIndex")
          (expr_seq
           (expr_let "$newVal"
            (expr_get_field (expr_id "arr")
             (expr_op1 unary_op_prim_to_str (expr_id "fromIndex")))
            (expr_set_field (expr_id "obj")
             (expr_op1 unary_op_prim_to_str (expr_id "toIndex"))
             (expr_id "$newVal")))
           (expr_app (expr_id "procArrayElt")
            [expr_id "arr";
             expr_op2 binary_op_add (expr_id "fromIndex")
             (expr_number (JsNumber.of_int 1));
             expr_op2 binary_op_add (expr_id "toIndex")
             (expr_number (JsNumber.of_int 1))]))))
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "elt")) (expr_string "object"))
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_obj_attr oattr_class (expr_id "elt"))
           (expr_string "Array"))
          (expr_app (expr_id "procArrayElt")
           [expr_id "elt"; expr_number (JsNumber.of_int 0); expr_id "n"])
          (expr_app (expr_id "procNormalElt") [expr_id "elt"; expr_id "n"]))
         (expr_app (expr_id "procNormalElt") [expr_id "elt"; expr_id "n"])))))
     (expr_recc "procAllElts"
      (expr_lambda ["from"; "fromIndex"; "toIndex"]
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_field (expr_id "from")
           (expr_op1 unary_op_prim_to_str (expr_id "fromIndex")))
          expr_undefined) expr_false expr_true)
        (expr_let "nextI"
         (expr_app (expr_id "procElt")
          [expr_id "A";
           expr_get_field (expr_id "from")
           (expr_op1 unary_op_prim_to_str (expr_id "fromIndex"));
           expr_id "toIndex"])
         (expr_app (expr_id "procAllElts")
          [expr_id "from";
           expr_op2 binary_op_add (expr_id "fromIndex")
           (expr_number (JsNumber.of_int 1));
           expr_id "nextI"])) (expr_id "toIndex")))
      (expr_let "halftime"
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_obj_attr oattr_class (expr_id "O")) (expr_string "Array"))
        (expr_app (expr_id "procAllElts")
         [expr_id "O";
          expr_number (JsNumber.of_int 0);
          expr_number (JsNumber.of_int 0)])
        (expr_seq
         (expr_let "$newVal" (expr_id "O")
          (expr_set_field (expr_id "A") (expr_string "0") (expr_id "$newVal")))
         (expr_number (JsNumber.of_int 1))))
       (expr_let "end"
        (expr_app (expr_id "procAllElts")
         [expr_id "args"; expr_number (JsNumber.of_int 0); expr_id "halftime"])
        (expr_seq
         (expr_let "$newVal" (expr_id "end")
          (expr_set_field (expr_id "A") (expr_string "length")
           (expr_id "$newVal"))) (expr_id "A"))))))))))
.
Definition privoneArgObj := 
value_closure
(closure_intro [("%mkArgsObj", privmkArgsObj)] None ["arg"]
 (expr_app (expr_id "%mkArgsObj")
  [expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined)
   [("0", property_data
          (data_intro (expr_id "arg") expr_false expr_false expr_false));
    ("length", property_data
               (data_intro (expr_number (JsNumber.of_int 1)) expr_false
                expr_false expr_false))]]))
.
Definition privslicelambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "A"
   (expr_object
    (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
     expr_null expr_undefined)
    [("length", property_data
                (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                 expr_false expr_false))])
   (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
    (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
     (expr_let "relativeStart"
      (expr_app (expr_id "%ToInteger")
       [expr_get_field (expr_id "args") (expr_string "0")])
      (expr_let "initk"
       (expr_if
        (expr_op2 binary_op_lt (expr_id "relativeStart")
         (expr_number (JsNumber.of_int 0)))
        (expr_let "added"
         (expr_op2 binary_op_add (expr_id "len") (expr_id "relativeStart"))
         (expr_if
          (expr_op2 binary_op_gt (expr_id "added")
           (expr_number (JsNumber.of_int 0))) (expr_id "added")
          (expr_number (JsNumber.of_int 0))))
        (expr_if
         (expr_op2 binary_op_lt (expr_id "relativeStart") (expr_id "len"))
         (expr_id "relativeStart") (expr_id "len")))
       (expr_let "relativeEnd"
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_field (expr_id "args") (expr_string "1")) expr_undefined)
         (expr_id "len")
         (expr_app (expr_id "%ToInteger")
          [expr_get_field (expr_id "args") (expr_string "1")]))
        (expr_let "final"
         (expr_if
          (expr_op2 binary_op_lt (expr_id "relativeEnd")
           (expr_number (JsNumber.of_int 0)))
          (expr_let "added"
           (expr_op2 binary_op_add (expr_id "len") (expr_id "relativeEnd"))
           (expr_if
            (expr_op2 binary_op_gt (expr_id "added")
             (expr_number (JsNumber.of_int 0))) (expr_id "added")
            (expr_number (JsNumber.of_int 0))))
          (expr_if
           (expr_op2 binary_op_lt (expr_id "relativeEnd") (expr_id "len"))
           (expr_id "relativeEnd") (expr_id "len")))
         (expr_recc "loop"
          (expr_lambda ["n"; "k"; "finalLen"]
           (expr_label "ret"
            (expr_seq
             (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "final"))
              (expr_break "ret" (expr_id "finalLen")) expr_null)
             (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
              (expr_let "kPresent"
               (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
               (expr_if (expr_id "kPresent")
                (expr_seq
                 (expr_let "kValue"
                  (expr_get_field (expr_id "O") (expr_id "Pk"))
                  (expr_app (expr_id "%defineOwnProperty")
                   [expr_id "A";
                    expr_app (expr_id "%ToString") [expr_id "n"];
                    expr_object
                    (objattrs_intro (expr_string "Object") expr_true
                     expr_null expr_null expr_undefined)
                    [("value", property_data
                               (data_intro (expr_id "kValue") expr_true
                                expr_false expr_false));
                     ("writable", property_data
                                  (data_intro expr_true expr_true expr_false
                                   expr_false));
                     ("configurable", property_data
                                      (data_intro expr_true expr_true
                                       expr_false expr_false));
                     ("enumerable", property_data
                                    (data_intro expr_true expr_true
                                     expr_false expr_false))]]))
                 (expr_break "ret"
                  (expr_app (expr_id "loop")
                   [expr_op2 binary_op_add (expr_id "n")
                    (expr_number (JsNumber.of_int 1));
                    expr_op2 binary_op_add (expr_id "k")
                    (expr_number (JsNumber.of_int 1));
                    expr_op2 binary_op_add (expr_id "finalLen")
                    (expr_number (JsNumber.of_int 1))])))
                (expr_break "ret"
                 (expr_app (expr_id "loop")
                  [expr_op2 binary_op_add (expr_id "n")
                   (expr_number (JsNumber.of_int 1));
                   expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1));
                   expr_op2 binary_op_add (expr_id "finalLen")
                   (expr_number (JsNumber.of_int 1))]))))))))
          (expr_seq
           (expr_let "$newVal"
            (expr_app (expr_id "loop")
             [expr_number (JsNumber.of_int 0);
              expr_id "initk";
              expr_number (JsNumber.of_int 0)])
            (expr_set_field (expr_id "A") (expr_string "length")
             (expr_id "$newVal"))) (expr_id "A"))))))))))))
.
Definition privbindLambda := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%IsObject", privIsObject);
  ("%ObjectProto", privObjectProto);
  ("%ThrowTypeError", privThrowTypeError);
  ("%TypeError", privTypeError);
  ("%concatLambda", privconcatLambda);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("%max", privmax);
  ("%oneArgObj", privoneArgObj);
  ("%slicelambda", privslicelambda)] None ["this"; "args"]
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
      (expr_string "function")) expr_false expr_true)
    (expr_app (expr_id "%TypeError")
     [expr_string "this not function in bind"]) expr_null)
   (expr_let "thisArg" (expr_get_field (expr_id "args") (expr_string "0"))
    (expr_let "A"
     (expr_app (expr_id "%slicelambda")
      [expr_id "args";
       expr_app (expr_id "%oneArgObj") [expr_number (JsNumber.of_int 1)]])
     (expr_let "mkNewObj"
      (expr_lambda ["proto"]
       (expr_let "proto"
        (expr_if (expr_app (expr_id "%IsObject") [expr_id "proto"])
         (expr_id "proto") (expr_id "%ObjectProto"))
        (expr_object
         (objattrs_intro (expr_string "Object") expr_true (expr_id "proto")
          expr_null expr_undefined) [])))
      (expr_let "Flambda"
       (expr_lambda ["this_inner"; "args_inner"]
        (expr_let "thisArg"
         (expr_if
          (expr_get_field (expr_id "args_inner") (expr_string "%new"))
          (expr_app (expr_id "mkNewObj")
           [expr_get_field (expr_id "this") (expr_string "prototype")])
          (expr_id "thisArg"))
         (expr_let "concatted"
          (expr_app (expr_id "%concatLambda")
           [expr_id "A"; expr_id "args_inner"])
          (expr_app (expr_id "this") [expr_id "thisArg"; expr_id "concatted"]))))
       (expr_let "F"
        (expr_object
         (objattrs_intro (expr_string "Function") expr_true
          (expr_id "%FunctionProto") (expr_id "Flambda") expr_undefined) 
         [])
        (expr_let "addthrower"
         (expr_lambda ["name"]
          (expr_app (expr_id "%defineOwnProperty")
           [expr_id "F";
            expr_id "name";
            expr_object
            (objattrs_intro (expr_string "Object") expr_true expr_null
             expr_null expr_undefined)
            [("get", property_data
                     (data_intro (expr_id "%ThrowTypeError") expr_true
                      expr_false expr_false));
             ("set", property_data
                     (data_intro (expr_id "%ThrowTypeError") expr_true
                      expr_false expr_false));
             ("enumerable", property_data
                            (data_intro expr_false expr_true expr_false
                             expr_false));
             ("configurable", property_data
                              (data_intro expr_false expr_true expr_false
                               expr_false))]]))
         (expr_let "FLength"
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_obj_attr oattr_class (expr_id "this"))
            (expr_string "Function"))
           (expr_let "L"
            (expr_op2 binary_op_sub
             (expr_get_field (expr_id "this") (expr_string "length"))
             (expr_get_field (expr_id "A") (expr_string "length")))
            (expr_app (expr_id "%max")
             [expr_number (JsNumber.of_int 0); expr_id "L"]))
           (expr_number (JsNumber.of_int 0)))
          (expr_seq
           (expr_app (expr_id "%defineOwnProperty")
            [expr_id "F";
             expr_string "length";
             expr_object
             (objattrs_intro (expr_string "Object") expr_true expr_null
              expr_null expr_undefined)
             [("value", property_data
                        (data_intro (expr_id "FLength") expr_true expr_false
                         expr_false));
              ("writable", property_data
                           (data_intro expr_false expr_true expr_false
                            expr_false));
              ("enumerable", property_data
                             (data_intro expr_false expr_true expr_false
                              expr_false));
              ("configurable", property_data
                               (data_intro expr_false expr_true expr_false
                                expr_false))]])
           (expr_seq (expr_app (expr_id "addthrower") [expr_string "caller"])
            (expr_seq
             (expr_app (expr_id "addthrower") [expr_string "arguments"])
             (expr_break "ret" (expr_id "F")))))))))))))))
.
Definition privbooleanToString :=  value_object 31 .
Definition privbooleanToStringlambda := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "t" (expr_op1 unary_op_typeof (expr_id "this"))
  (expr_let "b"
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "boolean"))
    (expr_id "this")
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_obj_attr oattr_class (expr_id "this"))
       (expr_string "Boolean"))
      (expr_get_obj_attr oattr_primval (expr_id "this"))
      (expr_app (expr_id "%TypeError")
       [expr_string "Boolean.prototype.toString got non-boolean object"]))
     (expr_app (expr_id "%TypeError")
      [expr_op2 binary_op_string_plus
       (expr_string "Boolean.prototype.toString got ") (expr_id "t")])))
   (expr_if (expr_id "b") (expr_string "true") (expr_string "false")))))
.
Definition privbooleanValueOf :=  value_object 303 .
Definition privcall :=  value_object 19 .
Definition privlen := 
value_closure
(closure_intro [] None ["list"]
 (expr_recc "inner_len"
  (expr_lambda ["iter"]
   (expr_if
    (expr_op2 binary_op_has_own_property (expr_id "list")
     (expr_op1 unary_op_prim_to_str (expr_id "iter")))
    (expr_op2 binary_op_add (expr_number (JsNumber.of_int 1))
     (expr_app (expr_id "inner_len")
      [expr_op2 binary_op_add (expr_number (JsNumber.of_int 1))
       (expr_id "iter")])) (expr_id "iter")))
  (expr_app (expr_id "inner_len") [expr_number (JsNumber.of_int 0)])))
.
Definition privslice_internal := 
value_closure
(closure_intro [] None ["list"; "min"; "max"]
 (expr_let "retObj"
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined) [])
  (expr_seq
   (expr_recc "inner_slice"
    (expr_lambda ["iter"; "ix"]
     (expr_if
      (expr_op2 binary_op_has_own_property (expr_id "list")
       (expr_op1 unary_op_prim_to_str (expr_id "iter")))
      (expr_seq
       (expr_let "$newVal"
        (expr_get_field (expr_id "list")
         (expr_op1 unary_op_prim_to_str (expr_id "iter")))
        (expr_set_field (expr_id "retObj")
         (expr_op1 unary_op_prim_to_str (expr_id "ix")) (expr_id "$newVal")))
       (expr_if (expr_op2 binary_op_gt (expr_id "iter") (expr_id "max"))
        expr_undefined
        (expr_app (expr_id "inner_slice")
         [expr_op2 binary_op_add (expr_id "iter")
          (expr_number (JsNumber.of_int 1));
          expr_op2 binary_op_add (expr_id "ix")
          (expr_number (JsNumber.of_int 1))])))
      (expr_let "$newVal" (expr_id "ix")
       (expr_set_field (expr_id "retObj") (expr_string "length")
        (expr_id "$newVal")))))
    (expr_app (expr_id "inner_slice")
     [expr_id "min"; expr_number (JsNumber.of_int 0)])) (expr_id "retObj"))))
.
Definition privcalllambda := 
value_closure
(closure_intro [("%len", privlen); ("%slice_internal", privslice_internal)]
 None ["this"; "args"]
 (expr_let "callArgs"
  (expr_app (expr_id "%slice_internal")
   [expr_id "args";
    expr_number (JsNumber.of_int 1);
    expr_app (expr_id "%len") [expr_id "args"]])
  (expr_app (expr_id "this")
   [expr_get_field (expr_id "args") (expr_string "0"); expr_id "callArgs"])))
.
Definition privcharat :=  value_object 110 .
Definition privcharatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "position"
    (expr_app (expr_id "%ToInteger")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_let "size" (expr_op1 unary_op_strlen (expr_id "S"))
     (expr_if
      (expr_let "%or"
       (expr_op2 binary_op_lt (expr_id "position")
        (expr_number (JsNumber.of_int 0)))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_ge (expr_id "position") (expr_id "size"))))
      (expr_string "")
      (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position"))))))))
.
Definition privcharcodeat :=  value_object 113 .
Definition privcharcodeatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "position"
    (expr_app (expr_id "%ToInteger")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_let "size" (expr_op1 unary_op_strlen (expr_id "S"))
     (expr_if
      (expr_let "%or"
       (expr_op2 binary_op_lt (expr_id "position")
        (expr_number (JsNumber.of_int 0)))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_ge (expr_id "position") (expr_id "size"))))
      (expr_number (JsNumber.of_int 0))
      (expr_op1 unary_op_ascii_cton
       (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position")))))))))
.
Definition privconcat :=  value_object 102 .
Definition privconsole :=  value_object 315 .
Definition privcos :=  value_object 279 .
Definition privcosLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "cos NYI"))
.
Definition privcreate :=  value_object 65 .
Definition privdefinePropertylambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["this"; "args"]
 (expr_let "obj" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_let "field" (expr_get_field (expr_id "args") (expr_string "1"))
   (expr_let "propobj" (expr_get_field (expr_id "args") (expr_string "2"))
    (expr_if (expr_app (expr_id "%ObjectTypeCheck") [expr_id "obj"])
     (expr_app (expr_id "%TypeError")
      [expr_string "defineProperty didn't get object"])
     (expr_let "attrobj"
      (expr_object
       (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
        expr_undefined) [])
      (expr_seq
       (expr_let "enumerable"
        (expr_get_field (expr_id "propobj") (expr_string "enumerable"))
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_op1 unary_op_typeof (expr_id "enumerable"))
           (expr_string "undefined")) expr_false expr_true)
         (expr_let "$newVal" (expr_id "enumerable")
          (expr_set_field (expr_id "attrobj") (expr_string "enumerable")
           (expr_id "$newVal"))) (expr_id "attrobj")))
       (expr_seq
        (expr_let "configurable"
         (expr_get_field (expr_id "propobj") (expr_string "configurable"))
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_op1 unary_op_typeof (expr_id "configurable"))
            (expr_string "undefined")) expr_false expr_true)
          (expr_let "$newVal" (expr_id "configurable")
           (expr_set_field (expr_id "attrobj") (expr_string "configurable")
            (expr_id "$newVal"))) (expr_id "attrobj")))
        (expr_seq
         (expr_let "writable"
          (expr_get_field (expr_id "propobj") (expr_string "writable"))
          (expr_if
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_op1 unary_op_typeof (expr_id "writable"))
             (expr_string "undefined")) expr_false expr_true)
           (expr_let "$newVal" (expr_id "writable")
            (expr_set_field (expr_id "attrobj") (expr_string "writable")
             (expr_id "$newVal"))) (expr_id "attrobj")))
         (expr_seq
          (expr_let "value"
           (expr_get_field (expr_id "propobj") (expr_string "value"))
           (expr_if
            (expr_if
             (expr_op2 binary_op_stx_eq
              (expr_op1 unary_op_typeof (expr_id "value"))
              (expr_string "undefined")) expr_false expr_true)
            (expr_let "$newVal" (expr_id "value")
             (expr_set_field (expr_id "attrobj") (expr_string "value")
              (expr_id "$newVal"))) (expr_id "attrobj")))
          (expr_seq
           (expr_let "get"
            (expr_get_field (expr_id "propobj") (expr_string "get"))
            (expr_if
             (expr_if
              (expr_if
               (expr_op2 binary_op_stx_eq
                (expr_op1 unary_op_typeof (expr_id "get"))
                (expr_string "undefined")) expr_false expr_true)
              (expr_if
               (expr_op2 binary_op_stx_eq
                (expr_op1 unary_op_typeof (expr_id "get"))
                (expr_string "function")) expr_false expr_true) expr_false)
             (expr_app (expr_id "%TypeError")
              [expr_string "defineProperty given a non-function getter"])
             (expr_let "$newVal" (expr_id "get")
              (expr_set_field (expr_id "attrobj") (expr_string "get")
               (expr_id "$newVal")))))
           (expr_seq
            (expr_let "set"
             (expr_get_field (expr_id "propobj") (expr_string "set"))
             (expr_if
              (expr_if
               (expr_if
                (expr_op2 binary_op_stx_eq
                 (expr_op1 unary_op_typeof (expr_id "set"))
                 (expr_string "undefined")) expr_false expr_true)
               (expr_if
                (expr_op2 binary_op_stx_eq
                 (expr_op1 unary_op_typeof (expr_id "set"))
                 (expr_string "function")) expr_false expr_true) expr_false)
              (expr_app (expr_id "%TypeError")
               [expr_string "defineProperty given a non-function setter"])
              (expr_let "$newVal" (expr_id "set")
               (expr_set_field (expr_id "attrobj") (expr_string "set")
                (expr_id "$newVal")))))
            (expr_if
             (expr_if
              (expr_app (expr_id "isDataDescriptor") [expr_id "attrobj"])
              (expr_app (expr_id "isAccessorDescriptor") [expr_id "attrobj"])
              expr_false)
             (expr_app (expr_id "%TypeError")
              [expr_string
               "The attributes given to defineProperty were inconsistent"])
             (expr_app (expr_id "%defineOwnProperty")
              [expr_id "obj"; expr_id "field"; expr_id "attrobj"]))))))))))))))
.
Definition privdefinePropertiesLambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToObject", privToObject);
  ("%definePropertylambda", privdefinePropertylambda)] None ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_seq
    (expr_let "props"
     (expr_app (expr_id "%ToObject")
      [expr_get_field (expr_id "args") (expr_string "1")])
     (expr_let "names" (expr_own_field_names (expr_id "props"))
      (expr_let "len"
       (expr_get_field (expr_id "names") (expr_string "length"))
       (expr_recc "loop"
        (expr_lambda ["i"]
         (expr_label "ret"
          (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
           (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
            (expr_let "name"
             (expr_get_field (expr_id "names") (expr_id "indx"))
             (expr_if
              (expr_get_attr pattr_enum (expr_id "props") (expr_id "name"))
              (expr_let "argsObj"
               (expr_object
                (objattrs_intro (expr_string "Object") expr_true expr_null
                 expr_null expr_undefined) [])
               (expr_seq
                (expr_let "$newVal" (expr_id "O")
                 (expr_set_field (expr_id "argsObj") (expr_string "0")
                  (expr_id "$newVal")))
                (expr_seq
                 (expr_let "$newVal" (expr_id "name")
                  (expr_set_field (expr_id "argsObj") (expr_string "1")
                   (expr_id "$newVal")))
                 (expr_seq
                  (expr_let "$newVal"
                   (expr_get_field (expr_id "props") (expr_id "name"))
                   (expr_set_field (expr_id "argsObj") (expr_string "2")
                    (expr_id "$newVal")))
                  (expr_seq
                   (expr_let "$newVal" (expr_number (JsNumber.of_int 3))
                    (expr_set_field (expr_id "argsObj")
                     (expr_string "length") (expr_id "$newVal")))
                   (expr_seq
                    (expr_app (expr_id "%definePropertylambda")
                     [expr_null; expr_id "argsObj"])
                    (expr_break "ret"
                     (expr_app (expr_id "loop")
                      [expr_op2 binary_op_add (expr_id "i")
                       (expr_number (JsNumber.of_int 1))]))))))))
              (expr_break "ret"
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "i")
                 (expr_number (JsNumber.of_int 1))])))))
           (expr_break "ret" expr_undefined))))
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))
    (expr_id "O")))))
.
Definition privcreateLambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%TypeError", privTypeError);
  ("%definePropertiesLambda", privdefinePropertiesLambda)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_let "t" (expr_op1 unary_op_typeof (expr_id "O"))
   (expr_let "c1"
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
     expr_false expr_true)
    (expr_let "c2"
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
      expr_false expr_true)
     (expr_let "c3"
      (expr_if (expr_op2 binary_op_stx_eq (expr_id "O") expr_null) expr_false
       expr_true)
      (expr_seq
       (expr_if
        (expr_if (expr_if (expr_id "c1") (expr_id "c2") expr_false)
         (expr_id "c3") expr_false)
        (expr_app (expr_id "%TypeError") [expr_string "Object.create failed"])
        expr_null)
       (expr_let "obj"
        (expr_object
         (objattrs_intro (expr_string "Object") expr_true (expr_id "O")
          expr_null expr_undefined) [])
        (expr_if
         (expr_if
          (expr_op2 binary_op_ge
           (expr_get_field (expr_id "args") (expr_string "length"))
           (expr_number (JsNumber.of_int 2)))
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_field (expr_id "args") (expr_string "1"))
            expr_undefined) expr_false expr_true) expr_false)
         (expr_let "Properties"
          (expr_app (expr_id "%ToObject")
           [expr_get_field (expr_id "args") (expr_string "1")])
          (expr_let "argsObj"
           (expr_object
            (objattrs_intro (expr_string "Object") expr_true expr_null
             expr_null expr_undefined) [])
           (expr_seq
            (expr_let "$newVal" (expr_id "obj")
             (expr_set_field (expr_id "argsObj") (expr_string "0")
              (expr_id "$newVal")))
            (expr_seq
             (expr_let "$newVal" (expr_id "Properties")
              (expr_set_field (expr_id "argsObj") (expr_string "1")
               (expr_id "$newVal")))
             (expr_seq
              (expr_let "$newVal" (expr_number (JsNumber.of_int 2))
               (expr_set_field (expr_id "argsObj") (expr_string "length")
                (expr_id "$newVal")))
              (expr_seq
               (expr_app (expr_id "%definePropertiesLambda")
                [expr_null; expr_id "argsObj"]) (expr_id "obj")))))))
         (expr_id "obj"))))))))))
.
Definition privdateGetTimezoneOffset :=  value_object 179 .
Definition privdateGetTimezoneOffsetLambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_let "t" (expr_get_obj_attr oattr_primval (expr_id "this"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number (JsNumber.of_int 0)))
   (expr_number (JsNumber.of_int 0)) (expr_number (JsNumber.of_int 0)))))
.
Definition privdateToString :=  value_object 175 .
Definition privdateValueOf :=  value_object 177 .
Definition privdateValueOfLambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_get_obj_attr oattr_primval (expr_id "this")))
.
Definition privdategetDate :=  value_object 183 .
Definition privdategetDateLambda := 
value_closure
(closure_intro [("%DateFromTime", privDateFromTime); ("%LocalTime", privUTC)]
 None ["this"; "args"]
 (expr_let "t" (expr_get_obj_attr oattr_primval (expr_id "this"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number (JsNumber.of_int 0)))
   (expr_id "t")
   (expr_app (expr_id "%DateFromTime")
    [expr_app (expr_id "%LocalTime") [expr_id "t"]]))))
.
Definition privdategetDay :=  value_object 181 .
Definition privdategetDayLambda := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["this"; "args"]
 (expr_let "day"
  (expr_op1 unary_op_floor
   (expr_op2 binary_op_div (expr_get_obj_attr oattr_primval (expr_id "this"))
    (expr_id "%msPerDay")))
  (expr_let "weekday"
   (expr_op2 binary_op_mod
    (expr_op2 binary_op_add (expr_id "day") (expr_number (JsNumber.of_int 4)))
    (expr_number (JsNumber.of_int 7))) (expr_id "weekday"))))
.
Definition privdecodeURI :=  value_object 257 .
Definition privdecodeURIComponent :=  value_object 258 .
Definition privdecodeURIComponentLambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_string "decodeURIComponent NYI"))
.
Definition privdecodeURILambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "decodeURI NYI"))
.
Definition privdefine15Property := 
value_closure
(closure_intro [("%defineOwnProperty", privdefineOwnProperty)] None
 ["obj"; "field"; "prop"]
 (expr_let "%mkPropObj"
  (expr_lambda ["value"; "writable"; "enumerable"; "configurable"]
   (expr_if
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "value") expr_null)
     expr_false expr_true)
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
      expr_undefined)
     [("value", property_data
                (data_intro (expr_id "value") expr_true expr_false expr_false));
      ("writable", property_data
                   (data_intro (expr_id "writable") expr_true expr_false
                    expr_false));
      ("enumerable", property_data
                     (data_intro (expr_id "enumerable") expr_true expr_false
                      expr_false));
      ("configurable", property_data
                       (data_intro (expr_id "configurable") expr_true
                        expr_false expr_false))])
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
      expr_undefined)
     [("writable", property_data
                   (data_intro (expr_id "writable") expr_true expr_false
                    expr_false));
      ("enumerable", property_data
                     (data_intro (expr_id "enumerable") expr_true expr_false
                      expr_false));
      ("configurable", property_data
                       (data_intro (expr_id "configurable") expr_true
                        expr_false expr_false))])))
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "obj"))
     (expr_string "function"))
    (expr_op2 binary_op_stx_eq (expr_id "field") (expr_string "length"))
    expr_false)
   (expr_app (expr_id "%defineOwnProperty")
    [expr_id "obj";
     expr_id "field";
     expr_app (expr_id "%mkPropObj")
     [expr_id "prop"; expr_false; expr_false; expr_false]])
   (expr_app (expr_id "%defineOwnProperty")
    [expr_id "obj";
     expr_id "field";
     expr_app (expr_id "%mkPropObj")
     [expr_id "prop"; expr_true; expr_false; expr_true]]))))
.
Definition privmakeEnvGetter := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto); ("%UnboundId", privUnboundId)] 
 None ["object"; "id"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_false
   (expr_id "%FunctionProto")
   (expr_lambda ["this"]
    (expr_if
     (expr_op2 binary_op_has_property (expr_id "object") (expr_id "id"))
     (expr_get_field (expr_id "object") (expr_id "id"))
     (expr_app (expr_id "%UnboundId") [expr_id "id"]))) expr_undefined) 
  []))
.
Definition privmakeEnvSetter := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%UnwritableDispatch", privUnwritableDispatch)] None ["object"; "id"]
 (expr_object
  (objattrs_intro (expr_string "Object") expr_false
   (expr_id "%FunctionProto")
   (expr_lambda ["this"; "arg"]
    (expr_try_catch
     (expr_let "$newVal" (expr_id "arg")
      (expr_set_field (expr_id "object") (expr_id "id") (expr_id "$newVal")))
     (expr_app (expr_id "%UnwritableDispatch") [expr_id "id"])))
   expr_undefined) []))
.
Definition privdefineGlobalAccessors := 
value_closure
(closure_intro
 [("%global", privglobal);
  ("%globalContext", privglobalContext);
  ("%makeEnvGetter", privmakeEnvGetter);
  ("%makeEnvSetter", privmakeEnvSetter)] None ["context"; "id"]
 (expr_seq
  (expr_set_attr pattr_config (expr_id "%globalContext") (expr_id "id")
   expr_true)
  (expr_seq
   (expr_set_attr pattr_enum (expr_id "%globalContext") (expr_id "id")
    expr_true)
   (expr_seq
    (expr_set_attr pattr_getter (expr_id "%globalContext") (expr_id "id")
     (expr_app (expr_id "%makeEnvGetter") [expr_id "%global"; expr_id "id"]))
    (expr_set_attr pattr_setter (expr_id "%globalContext") (expr_id "id")
     (expr_app (expr_id "%makeEnvSetter") [expr_id "%global"; expr_id "id"]))))))
.
Definition privdefineGlobalVar := 
value_closure
(closure_intro
 [("%global", privglobal);
  ("%makeEnvGetter", privmakeEnvGetter);
  ("%makeEnvSetter", privmakeEnvSetter)] None ["context"; "id"]
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_has_property (expr_id "context") (expr_id "id")))
  (expr_seq
   (expr_set_attr pattr_config (expr_id "%global") (expr_id "id") expr_true)
   (expr_seq
    (expr_set_attr pattr_writable (expr_id "%global") (expr_id "id")
     expr_true)
    (expr_seq
     (expr_set_attr pattr_value (expr_id "%global") (expr_id "id")
      expr_undefined)
     (expr_seq
      (expr_set_attr pattr_enum (expr_id "%global") (expr_id "id") expr_true)
      (expr_seq
       (expr_set_attr pattr_config (expr_id "%global") (expr_id "id")
        expr_false)
       (expr_seq
        (expr_set_attr pattr_config (expr_id "context") (expr_id "id")
         expr_true)
        (expr_seq
         (expr_set_attr pattr_enum (expr_id "context") (expr_id "id")
          expr_true)
         (expr_seq
          (expr_set_attr pattr_getter (expr_id "context") (expr_id "id")
           (expr_app (expr_id "%makeEnvGetter")
            [expr_id "%global"; expr_id "id"]))
          (expr_set_attr pattr_setter (expr_id "context") (expr_id "id")
           (expr_app (expr_id "%makeEnvSetter")
            [expr_id "%global"; expr_id "id"])))))))))) expr_undefined))
.
Definition privdefineNYIProperty := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%TypeError", privTypeError);
  ("%define15Property", privdefine15Property)] None ["base"; "name"]
 (expr_let "unimplFunc"
  (expr_lambda ["this"; "args"]
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
  (expr_let "unimplObj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true
     (expr_id "%FunctionProto") (expr_id "unimplFunc") expr_undefined) 
    [])
   (expr_app (expr_id "%define15Property")
    [expr_id "base"; expr_id "name"; expr_id "unimplObj"]))))
.
Definition privdefineProperties :=  value_object 63 .
Definition privdefineProperty :=  value_object 18 .
Definition privencodeURI :=  value_object 259 .
Definition privencodeURIComponent :=  value_object 260 .
Definition privencodeURIComponentLambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_string "encodeURIComponent NYI"))
.
Definition privencodeURILambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "encodeURI NYI"))
.
Definition privescape :=  value_object 322 .
Definition privescapeLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "escape NYI"))
.
Definition privets :=  value_object 25 .
Definition privetslambda := 
value_closure
(closure_intro [("%ToString", privToString); ("%TypeError", privTypeError)]
 None ["this"; "args"]
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
    (expr_string "object")) expr_false expr_true)
  (expr_app (expr_id "%TypeError")
   [expr_string "This not object in Error.prototype.toString"])
  (expr_let "name"
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_field (expr_id "this") (expr_string "name")) expr_undefined)
    (expr_string "Error")
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "this") (expr_string "name")]))
   (expr_let "msg"
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_get_field (expr_id "this") (expr_string "message"))
      expr_undefined) (expr_string "")
     (expr_app (expr_id "%ToString")
      [expr_get_field (expr_id "this") (expr_string "message")]))
    (expr_let "c1"
     (expr_op2 binary_op_stx_eq (expr_id "name") (expr_string ""))
     (expr_let "c2"
      (expr_op2 binary_op_stx_eq (expr_id "msg") (expr_string ""))
      (expr_label "ret"
       (expr_seq
        (expr_if (expr_if (expr_id "c1") (expr_id "c2") expr_false)
         (expr_break "ret" (expr_string "Error")) expr_null)
        (expr_seq
         (expr_if (expr_id "c1") (expr_break "ret" (expr_id "msg")) expr_null)
         (expr_seq
          (expr_if (expr_id "c2") (expr_break "ret" (expr_id "name"))
           expr_null)
          (expr_let "prefix"
           (expr_op2 binary_op_string_plus (expr_id "name")
            (expr_string ": "))
           (expr_break "ret"
            (expr_op2 binary_op_string_plus (expr_id "prefix")
             (expr_id "msg"))))))))))))))
.
Definition priveval :=  value_object 316 .
Definition privevery :=  value_object 145 .
Definition priveverylambda := 
value_closure
(closure_intro
 [("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "callbackfn"))
          (expr_string "function")) expr_false expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "Callback not function in every"]) expr_null)
       (expr_let "T" (expr_get_field (expr_id "args") (expr_string "1"))
        (expr_recc "loop"
         (expr_lambda ["k"]
          (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
           (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
            (expr_let "kPresent"
             (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
             (expr_if (expr_id "kPresent")
              (expr_let "kValue"
               (expr_get_field (expr_id "O") (expr_id "Pk"))
               (expr_let "argsObj"
                (expr_object
                 (objattrs_intro (expr_string "Object") expr_true expr_null
                  expr_null expr_undefined) [])
                (expr_seq
                 (expr_let "$newVal" (expr_id "kValue")
                  (expr_set_field (expr_id "argsObj") (expr_string "0")
                   (expr_id "$newVal")))
                 (expr_seq
                  (expr_let "$newVal" (expr_id "k")
                   (expr_set_field (expr_id "argsObj") (expr_string "1")
                    (expr_id "$newVal")))
                  (expr_seq
                   (expr_let "$newVal" (expr_id "O")
                    (expr_set_field (expr_id "argsObj") (expr_string "2")
                     (expr_id "$newVal")))
                   (expr_seq
                    (expr_let "$newVal" (expr_number (JsNumber.of_int 3))
                     (expr_set_field (expr_id "argsObj")
                      (expr_string "length") (expr_id "$newVal")))
                    (expr_let "testResult"
                     (expr_app (expr_id "callbackfn")
                      [expr_id "T"; expr_id "argsObj"])
                     (expr_if
                      (expr_op2 binary_op_stx_eq
                       (expr_app (expr_id "%ToBoolean")
                        [expr_id "testResult"]) expr_false) expr_false
                      (expr_app (expr_id "loop")
                       [expr_op2 binary_op_add (expr_id "k")
                        (expr_number (JsNumber.of_int 1))])))))))))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1))])))) expr_true))
         (expr_break "ret"
          (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))))))
.
Definition privexp :=  value_object 261 .
Definition privexplambda := 
value_closure (closure_intro [] None [] expr_undefined)
.
Definition privfilter :=  value_object 140 .
Definition privfilterlambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "callbackfn"))
          (expr_string "function")) expr_false expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "Callback not a function in filter"]) expr_null)
       (expr_let "T" (expr_get_field (expr_id "args") (expr_string "1"))
        (expr_let "A"
         (expr_object
          (objattrs_intro (expr_string "Array") expr_true
           (expr_id "%ArrayProto") expr_null expr_undefined)
          [("length", property_data
                      (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                       expr_false expr_false))])
         (expr_recc "loop"
          (expr_lambda ["k"; "to"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_if
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
              (expr_let "kValue"
               (expr_get_field (expr_id "O") (expr_id "Pk"))
               (expr_let "argsObj"
                (expr_object
                 (objattrs_intro (expr_string "Object") expr_true expr_null
                  expr_null expr_undefined) [])
                (expr_seq
                 (expr_let "$newVal" (expr_id "kValue")
                  (expr_set_field (expr_id "argsObj") (expr_string "0")
                   (expr_id "$newVal")))
                 (expr_seq
                  (expr_let "$newVal" (expr_id "k")
                   (expr_set_field (expr_id "argsObj") (expr_string "1")
                    (expr_id "$newVal")))
                  (expr_seq
                   (expr_let "$newVal" (expr_id "O")
                    (expr_set_field (expr_id "argsObj") (expr_string "2")
                     (expr_id "$newVal")))
                   (expr_seq
                    (expr_let "$newVal" (expr_number (JsNumber.of_int 3))
                     (expr_set_field (expr_id "argsObj")
                      (expr_string "length") (expr_id "$newVal")))
                    (expr_let "selected"
                     (expr_app (expr_id "callbackfn")
                      [expr_id "T"; expr_id "argsObj"])
                     (expr_if
                      (expr_app (expr_id "%ToBoolean") [expr_id "selected"])
                      (expr_seq
                       (expr_app (expr_id "%defineOwnProperty")
                        [expr_id "A";
                         expr_app (expr_id "%ToString") [expr_id "to"];
                         expr_object
                         (objattrs_intro (expr_string "Object") expr_true
                          expr_null expr_null expr_undefined)
                         [("value", property_data
                                    (data_intro (expr_id "kValue") expr_true
                                     expr_false expr_false));
                          ("writable", property_data
                                       (data_intro expr_true expr_true
                                        expr_false expr_false));
                          ("enumerable", property_data
                                         (data_intro expr_true expr_true
                                          expr_false expr_false));
                          ("configurable", property_data
                                           (data_intro expr_true expr_true
                                            expr_false expr_false))]])
                       (expr_app (expr_id "loop")
                        [expr_op2 binary_op_add (expr_id "k")
                         (expr_number (JsNumber.of_int 1));
                         expr_op2 binary_op_add (expr_id "to")
                         (expr_number (JsNumber.of_int 1))]))
                      (expr_app (expr_id "loop")
                       [expr_op2 binary_op_add (expr_id "k")
                        (expr_number (JsNumber.of_int 1));
                        expr_id "to"])))))))))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1));
                expr_id "to"])))
            (expr_let "$newVal" (expr_id "to")
             (expr_set_field (expr_id "A") (expr_string "length")
              (expr_id "$newVal")))))
          (expr_seq
           (expr_app (expr_id "loop")
            [expr_number (JsNumber.of_int 0); expr_number (JsNumber.of_int 0)])
           (expr_break "ret" (expr_id "A")))))))))))))
.
Definition privforeach :=  value_object 134 .
Definition privforeachlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "callbackfn"))
          (expr_string "function")) expr_false expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "Callback not a function in forEach"]) expr_undefined)
       (expr_seq
        (expr_let "T" (expr_get_field (expr_id "args") (expr_string "1"))
         (expr_recc "loop"
          (expr_lambda ["k"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_if
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
              (expr_seq
               (expr_let "kValue"
                (expr_get_field (expr_id "O") (expr_id "Pk"))
                (expr_let "argslist"
                 (expr_object
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_null expr_undefined)
                  [("0", property_data
                         (data_intro (expr_id "kValue") expr_true expr_false
                          expr_false));
                   ("1", property_data
                         (data_intro (expr_id "k") expr_true expr_false
                          expr_false));
                   ("2", property_data
                         (data_intro (expr_id "O") expr_true expr_false
                          expr_false))])
                 (expr_app (expr_id "callbackfn")
                  [expr_id "T"; expr_id "argslist"])))
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int 1))]))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1))]))) expr_undefined))
          (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))
        expr_undefined))))))))
.
Definition privfreeze :=  value_object 69 .
Definition privfreezelambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "names" (expr_own_field_names (expr_id "O"))
    (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
     (expr_recc "loop"
      (expr_lambda ["i"]
       (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
        (expr_let "name"
         (expr_get_field (expr_id "names")
          (expr_op1 unary_op_prim_to_str (expr_id "i")))
         (expr_seq
          (expr_if
           (expr_op1 unary_op_not
            (expr_op2 binary_op_is_accessor (expr_id "O") (expr_id "name")))
           (expr_if
            (expr_get_attr pattr_writable (expr_id "O") (expr_id "name"))
            (expr_set_attr pattr_writable (expr_id "O") (expr_id "name")
             expr_false) expr_undefined) expr_undefined)
          (expr_seq
           (expr_set_attr pattr_config (expr_id "O") (expr_id "name")
            expr_false)
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int 1))])))) expr_null))
      (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
       (expr_seq
        (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
        (expr_id "O")))))))))
.
Definition privfromCharCode :=  value_object 81 .
Definition privfromcclambda := 
value_closure
(closure_intro [("%ToUint16", privToUint16)] None ["this"; "args"]
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_field (expr_id "args") (expr_string "length"))
   (expr_number (JsNumber.of_int 0))) (expr_string "")
  (expr_let "end" (expr_get_field (expr_id "args") (expr_string "length"))
   (expr_recc "loop"
    (expr_lambda ["i"; "soFar"]
     (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
      (expr_let "char"
       (expr_op1 unary_op_ascii_ntoc
        (expr_app (expr_id "%ToUint16")
         [expr_get_field (expr_id "args")
          (expr_op1 unary_op_prim_to_str (expr_id "i"))]))
       (expr_let "next"
        (expr_op2 binary_op_string_plus (expr_id "soFar") (expr_id "char"))
        (expr_app (expr_id "loop")
         [expr_op2 binary_op_add (expr_id "i")
          (expr_number (JsNumber.of_int 1));
          expr_id "next"]))) (expr_id "soFar")))
    (expr_app (expr_id "loop")
     [expr_number (JsNumber.of_int 0); expr_string ""])))))
.
Definition privfunctionToString :=  value_object 6 .
Definition privfunctionToStringlambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "function ToString"))
.
Definition privgetMonth :=  value_object 173 .
Definition privgetMonthlambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_number (JsNumber.of_int 3)))
.
Definition privgetYear :=  value_object 172 .
Definition privgetYearlambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_number (JsNumber.of_int 78)))
.
Definition privgopd :=  value_object 39 .
Definition privgopdLambda := 
value_closure
(closure_intro
 [("%ObjectProto", privObjectProto);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "name"
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "args") (expr_string "1")])
    (expr_label "ret"
     (expr_seq
      (expr_if
       (expr_op1 unary_op_not
        (expr_op2 binary_op_has_own_property (expr_id "O") (expr_id "name")))
       (expr_break "ret" expr_undefined) expr_null)
      (expr_let "obj"
       (expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "%ObjectProto") expr_null expr_undefined) [])
       (expr_seq
        (expr_app (expr_id "%defineOwnProperty")
         [expr_id "obj";
          expr_string "enumerable";
          expr_object
          (objattrs_intro (expr_string "Object") expr_true expr_null
           expr_null expr_undefined)
          [("value", property_data
                     (data_intro
                      (expr_get_attr pattr_enum (expr_id "O")
                       (expr_id "name")) expr_true expr_false expr_false));
           ("writable", property_data
                        (data_intro expr_true expr_true expr_false expr_false));
           ("enumerable", property_data
                          (data_intro expr_true expr_true expr_false
                           expr_false));
           ("configurable", property_data
                            (data_intro expr_true expr_true expr_false
                             expr_false))]])
        (expr_seq
         (expr_app (expr_id "%defineOwnProperty")
          [expr_id "obj";
           expr_string "configurable";
           expr_object
           (objattrs_intro (expr_string "Object") expr_true expr_null
            expr_null expr_undefined)
           [("value", property_data
                      (data_intro
                       (expr_get_attr pattr_config (expr_id "O")
                        (expr_id "name")) expr_true expr_false expr_false));
            ("writable", property_data
                         (data_intro expr_true expr_true expr_false
                          expr_false));
            ("enumerable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false));
            ("configurable", property_data
                             (data_intro expr_true expr_true expr_false
                              expr_false))]])
         (expr_if
          (expr_op1 unary_op_not
           (expr_op2 binary_op_is_accessor (expr_id "O") (expr_id "name")))
          (expr_seq
           (expr_app (expr_id "%defineOwnProperty")
            [expr_id "obj";
             expr_string "value";
             expr_object
             (objattrs_intro (expr_string "Object") expr_true expr_null
              expr_null expr_undefined)
             [("value", property_data
                        (data_intro
                         (expr_get_field (expr_id "O") (expr_id "name"))
                         expr_true expr_false expr_false));
              ("writable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false));
              ("enumerable", property_data
                             (data_intro expr_true expr_true expr_false
                              expr_false));
              ("configurable", property_data
                               (data_intro expr_true expr_true expr_false
                                expr_false))]])
           (expr_seq
            (expr_app (expr_id "%defineOwnProperty")
             [expr_id "obj";
              expr_string "writable";
              expr_object
              (objattrs_intro (expr_string "Object") expr_true expr_null
               expr_null expr_undefined)
              [("value", property_data
                         (data_intro
                          (expr_get_attr pattr_writable (expr_id "O")
                           (expr_id "name")) expr_true expr_false expr_false));
               ("writable", property_data
                            (data_intro expr_true expr_true expr_false
                             expr_false));
               ("enumerable", property_data
                              (data_intro expr_true expr_true expr_false
                               expr_false));
               ("configurable", property_data
                                (data_intro expr_true expr_true expr_false
                                 expr_false))]])
            (expr_break "ret" (expr_id "obj"))))
          (expr_seq
           (expr_app (expr_id "%defineOwnProperty")
            [expr_id "obj";
             expr_string "get";
             expr_object
             (objattrs_intro (expr_string "Object") expr_true expr_null
              expr_null expr_undefined)
             [("value", property_data
                        (data_intro
                         (expr_get_attr pattr_getter (expr_id "O")
                          (expr_id "name")) expr_true expr_false expr_false));
              ("writable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false));
              ("enumerable", property_data
                             (data_intro expr_true expr_true expr_false
                              expr_false));
              ("configurable", property_data
                               (data_intro expr_true expr_true expr_false
                                expr_false))]])
           (expr_seq
            (expr_app (expr_id "%defineOwnProperty")
             [expr_id "obj";
              expr_string "set";
              expr_object
              (objattrs_intro (expr_string "Object") expr_true expr_null
               expr_null expr_undefined)
              [("value", property_data
                         (data_intro
                          (expr_get_attr pattr_setter (expr_id "O")
                           (expr_id "name")) expr_true expr_false expr_false));
               ("writable", property_data
                            (data_intro expr_true expr_true expr_false
                             expr_false));
               ("enumerable", property_data
                              (data_intro expr_true expr_true expr_false
                               expr_false));
               ("configurable", property_data
                                (data_intro expr_true expr_true expr_false
                                 expr_false))]])
            (expr_break "ret" (expr_id "obj"))))))))))))))
.
Definition privgopn :=  value_object 60 .
Definition privgopnLambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto); ("%ObjectTypeCheck", privObjectTypeCheck)]
 None ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "A"
    (expr_object
     (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
      expr_null expr_undefined)
     [("length", property_data
                 (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                  expr_false expr_false))])
    (expr_let "props" (expr_own_field_names (expr_id "O"))
     (expr_let "len"
      (expr_get_field (expr_id "props") (expr_string "length"))
      (expr_recc "loop"
       (expr_lambda ["i"]
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_seq
          (expr_let "to" (expr_op1 unary_op_prim_to_str (expr_id "i"))
           (expr_let "from"
            (expr_op1 unary_op_prim_to_str
             (expr_op2 binary_op_sub (expr_id "len")
              (expr_op2 binary_op_add (expr_id "i")
               (expr_number (JsNumber.of_int 1)))))
            (expr_let "$newVal"
             (expr_get_field (expr_id "props") (expr_id "from"))
             (expr_set_field (expr_id "A") (expr_id "to") (expr_id "$newVal")))))
          (expr_app (expr_id "loop")
           [expr_op2 binary_op_add (expr_id "i")
            (expr_number (JsNumber.of_int 1))]))
         (expr_let "$newVal" (expr_id "i")
          (expr_set_field (expr_id "A") (expr_string "length")
           (expr_id "$newVal")))))
       (expr_seq
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
        (expr_id "A")))))))))
.
Definition privgpo :=  value_object 37 .
Definition privgpoLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_get_obj_attr oattr_proto (expr_id "O")))))
.
Definition privhasOwnProperty :=  value_object 45 .
Definition privhasOwnPropertylambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_if
  (expr_op2 binary_op_has_own_property (expr_id "this")
   (expr_get_field (expr_id "args") (expr_string "0"))) expr_true expr_false))
.
Definition privin := 
value_closure
(closure_intro [("%ToString", privToString); ("%TypeError", privTypeError)]
 None ["l"; "r"]
 (expr_let "rtype" (expr_op1 unary_op_typeof (expr_id "r"))
  (expr_if
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "rtype") (expr_string "object"))
     expr_false expr_true)
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "rtype") (expr_string "function"))
     expr_false expr_true) expr_false)
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus
     (expr_app (expr_id "%ToString") [expr_id "r"])
     (expr_string " is not an object")])
   (expr_op2 binary_op_has_property (expr_id "r")
    (expr_app (expr_id "%ToString") [expr_id "l"])))))
.
Definition privinstanceof := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["l"; "r"]
 (expr_let "rtype" (expr_op1 unary_op_typeof (expr_id "r"))
  (expr_let "ltype" (expr_op1 unary_op_typeof (expr_id "l"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "rtype") (expr_string "function"))
       expr_false expr_true)
      (expr_app (expr_id "%TypeError")
       [expr_string "Non-function given to instanceof"]) expr_null)
     (expr_seq
      (expr_if
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "ltype")
          (expr_string "function")) expr_false expr_true)
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "ltype") (expr_string "object"))
         expr_false expr_true) expr_false) (expr_break "ret" expr_false)
       expr_null)
      (expr_let "O" (expr_get_field (expr_id "r") (expr_string "prototype"))
       (expr_let "Otype" (expr_op1 unary_op_typeof (expr_id "O"))
        (expr_seq
         (expr_if
          (expr_if
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "Otype")
             (expr_string "function")) expr_false expr_true)
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "Otype")
             (expr_string "object")) expr_false expr_true) expr_false)
          (expr_app (expr_id "%TypeError")
           [expr_string "Prototype was not function or object"]) expr_null)
         (expr_recc "search"
          (expr_lambda ["v"]
           (expr_let "vp" (expr_get_obj_attr oattr_proto (expr_id "v"))
            (expr_if (expr_op2 binary_op_stx_eq (expr_id "vp") expr_null)
             expr_false
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "O") (expr_id "vp"))
              expr_true (expr_app (expr_id "search") [expr_id "vp"])))))
          (expr_break "ret" (expr_app (expr_id "search") [expr_id "l"]))))))))))))
.
Definition privisExtensible :=  value_object 77 .
Definition privisExtensibleLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_get_obj_attr oattr_extensible (expr_id "O")))))
.
Definition privisFinite :=  value_object 318 .
Definition privisFiniteLambda := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToNumber", privToNumber)]
 None ["this"; "args"]
 (expr_let "n"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_app (expr_id "%IsFinite") [expr_id "n"])))
.
Definition privisFrozen :=  value_object 73 .
Definition privisFrozenLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "names" (expr_own_field_names (expr_id "O"))
    (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
     (expr_recc "loop"
      (expr_lambda ["i"]
       (expr_label "ret"
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_let "name"
          (expr_get_field (expr_id "names")
           (expr_op1 unary_op_prim_to_str (expr_id "i")))
          (expr_let "isData"
           (expr_op1 unary_op_not
            (expr_op2 binary_op_is_accessor (expr_id "O") (expr_id "name")))
           (expr_seq
            (expr_if
             (expr_if (expr_id "isData")
              (expr_get_attr pattr_writable (expr_id "O") (expr_id "name"))
              expr_false) (expr_break "ret" expr_false) expr_null)
            (expr_seq
             (expr_if
              (expr_get_attr pattr_config (expr_id "O") (expr_id "name"))
              (expr_break "ret" expr_false) expr_null)
             (expr_break "ret"
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "i")
                (expr_number (JsNumber.of_int 1))]))))))
         (expr_break "ret"
          (expr_op1 unary_op_not
           (expr_get_obj_attr oattr_extensible (expr_id "O")))))))
      (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))
.
Definition privisNaN :=  value_object 23 .
Definition privisNaNlambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "n"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")) expr_false
   expr_true)))
.
Definition privisPrototypeOf :=  value_object 46 .
Definition privisSealed :=  value_object 75 .
Definition privisSealedLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "names" (expr_own_field_names (expr_id "O"))
    (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
     (expr_recc "loop"
      (expr_lambda ["i"]
       (expr_label "ret"
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_seq
          (expr_let "name"
           (expr_get_field (expr_id "names")
            (expr_op1 unary_op_prim_to_str (expr_id "i")))
           (expr_if
            (expr_get_attr pattr_config (expr_id "O") (expr_id "name"))
            (expr_break "ret" expr_false) expr_null))
          (expr_break "ret"
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int 1))])))
         (expr_break "ret"
          (expr_op1 unary_op_not
           (expr_get_obj_attr oattr_extensible (expr_id "O")))))))
      (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))
.
Definition privjoin :=  value_object 83 .
Definition privjoinlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_let "sep"
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
      (expr_string ",")
      (expr_app (expr_id "%ToString")
       [expr_get_field (expr_id "args") (expr_string "0")]))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "len")
         (expr_number (JsNumber.of_int 0)))
        (expr_break "ret" (expr_string "")) expr_null)
       (expr_recc "loop"
        (expr_lambda ["k"; "R"]
         (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "len"))
          (expr_id "R")
          (expr_let "S"
           (expr_op2 binary_op_string_plus (expr_id "R") (expr_id "sep"))
           (expr_let "element"
            (expr_get_field (expr_id "O")
             (expr_app (expr_id "%ToString") [expr_id "k"]))
            (expr_let "next"
             (expr_if
              (expr_let "%or"
               (expr_op2 binary_op_stx_eq (expr_id "element") expr_null)
               (expr_if (expr_id "%or") (expr_id "%or")
                (expr_op2 binary_op_stx_eq (expr_id "element") expr_undefined)))
              (expr_string "")
              (expr_app (expr_id "%ToString") [expr_id "element"]))
             (expr_app (expr_id "loop")
              [expr_op2 binary_op_add (expr_id "k")
               (expr_number (JsNumber.of_int 1));
               expr_op2 binary_op_string_plus (expr_id "S") (expr_id "next")]))))))
        (expr_let "start"
         (expr_if
          (expr_let "%or"
           (expr_op2 binary_op_stx_eq
            (expr_get_field (expr_id "O") (expr_string "0")) expr_undefined)
           (expr_if (expr_id "%or") (expr_id "%or")
            (expr_op2 binary_op_stx_eq
             (expr_get_field (expr_id "O") (expr_string "0")) expr_null)))
          (expr_string "")
          (expr_app (expr_id "%ToString")
           [expr_get_field (expr_id "O") (expr_string "0")]))
         (expr_break "ret"
          (expr_app (expr_id "loop")
           [expr_number (JsNumber.of_int 1); expr_id "start"])))))))))))
.
Definition privkeys :=  value_object 79 .
Definition privkeysLambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_let "A"
    (expr_object
     (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
      expr_null expr_undefined)
     [("length", property_data
                 (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                  expr_false expr_false))])
    (expr_let "names" (expr_own_field_names (expr_id "O"))
     (expr_let "len"
      (expr_get_field (expr_id "names") (expr_string "length"))
      (expr_recc "loop"
       (expr_lambda ["i"; "enumCount"]
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
          (expr_let "name"
           (expr_get_field (expr_id "names") (expr_id "indx"))
           (expr_if (expr_get_attr pattr_enum (expr_id "O") (expr_id "name"))
            (expr_seq
             (expr_let "pd"
              (expr_object
               (objattrs_intro (expr_string "Object") expr_true expr_null
                expr_null expr_undefined)
               [("value", property_data
                          (data_intro (expr_id "name") expr_true expr_false
                           expr_false));
                ("writable", property_data
                             (data_intro expr_true expr_true expr_false
                              expr_false));
                ("enumerable", property_data
                               (data_intro expr_true expr_true expr_false
                                expr_false));
                ("configurable", property_data
                                 (data_intro expr_true expr_true expr_false
                                  expr_false))])
              (expr_app (expr_id "%defineOwnProperty")
               [expr_id "A";
                expr_op1 unary_op_prim_to_str (expr_id "enumCount");
                expr_id "pd"]))
             (expr_app (expr_id "loop")
              [expr_op2 binary_op_add (expr_id "i")
               (expr_number (JsNumber.of_int 1));
               expr_op2 binary_op_add (expr_id "enumCount")
               (expr_number (JsNumber.of_int 1))]))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "i")
              (expr_number (JsNumber.of_int 1));
              expr_id "enumCount"]))))
         (expr_let "$newVal" (expr_id "enumCount")
          (expr_set_field (expr_id "A") (expr_string "length")
           (expr_id "$newVal")))))
       (expr_seq
        (expr_app (expr_id "loop")
         [expr_number (JsNumber.of_int 0); expr_number (JsNumber.of_int 0)])
        (expr_id "A")))))))))
.
Definition privlocaleCompare :=  value_object 166 .
Definition privlocaleCompareLambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "That"
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_op2 binary_op_locale_compare (expr_id "S") (expr_id "That"))))))
.
Definition privlog :=  value_object 314 .
Definition privlogLambda := 
value_closure
(closure_intro [] None ["o"; "s"]
 (expr_recc "loop"
  (expr_lambda ["i"]
   (expr_if
    (expr_op2 binary_op_has_property (expr_id "s")
     (expr_op1 unary_op_prim_to_str (expr_id "i")))
    (expr_seq
     (expr_op1 unary_op_pretty
      (expr_get_field (expr_id "s")
       (expr_op1 unary_op_prim_to_str (expr_id "i"))))
     (expr_app (expr_id "loop")
      [expr_op2 binary_op_add (expr_id "i") (expr_number (JsNumber.of_int 1))]))
    expr_undefined))
  (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))
.
Definition privprimEach := 
value_closure
(closure_intro [("%ToString", privToString)] None ["arr"; "fn"]
 (expr_recc "loop"
  (expr_lambda ["i"]
   (expr_let "istr" (expr_app (expr_id "%ToString") [expr_id "i"])
    (expr_if
     (expr_op2 binary_op_has_own_property (expr_id "arr") (expr_id "istr"))
     (expr_seq
      (expr_app (expr_id "fn")
       [expr_get_field (expr_id "arr") (expr_id "istr")])
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int 1))])) expr_undefined)))
  (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))
.
Definition privpropertyNames := 
value_closure
(closure_intro [] None ["obj"; "get-non-enumerable"]
 (expr_let "aux"
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined) [])
  (expr_recc "helper"
   (expr_lambda ["obj"]
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "obj") expr_null)
     expr_undefined
     (expr_seq
      (expr_let "cur" (expr_own_field_names (expr_id "obj"))
       (expr_let "length"
        (expr_get_field (expr_id "cur") (expr_string "length"))
        (expr_recc "loop"
         (expr_lambda ["i"]
          (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "length"))
           (expr_let "istr" (expr_op1 unary_op_prim_to_str (expr_id "i"))
            (expr_seq
             (expr_if
              (expr_let "%or"
               (expr_get_attr pattr_enum (expr_id "obj")
                (expr_get_field (expr_id "cur") (expr_id "istr")))
               (expr_if (expr_id "%or") (expr_id "%or")
                (expr_id "get-non-enumerable")))
              (expr_let "$newVal" expr_true
               (expr_set_field (expr_id "aux")
                (expr_get_field (expr_id "cur") (expr_id "istr"))
                (expr_id "$newVal"))) expr_undefined)
             (expr_app (expr_id "loop")
              [expr_op2 binary_op_add (expr_id "i")
               (expr_number (JsNumber.of_int 1))]))) expr_undefined))
         (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)]))))
      (expr_app (expr_id "helper")
       [expr_get_obj_attr oattr_proto (expr_id "obj")]))))
   (expr_seq (expr_app (expr_id "helper") [expr_id "obj"])
    (expr_own_field_names (expr_id "aux"))))))
.
Definition privmakeWithContext := 
value_closure
(closure_intro
 [("%defineOwnProperty", privdefineOwnProperty);
  ("%primEach", privprimEach);
  ("%propertyNames", privpropertyNames)] None ["context"; "object"]
 (expr_let "names"
  (expr_app (expr_id "%propertyNames") [expr_id "object"; expr_true])
  (expr_let "mksetter"
   (expr_lambda ["id"]
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true expr_null
      (expr_lambda ["this"; "args"]
       (expr_if
        (expr_op2 binary_op_has_property (expr_id "object") (expr_id "id"))
        (expr_let "$newVal"
         (expr_get_field (expr_id "args") (expr_string "0"))
         (expr_set_field (expr_id "object") (expr_id "id")
          (expr_id "$newVal")))
        (expr_let "$newVal"
         (expr_get_field (expr_id "args") (expr_string "0"))
         (expr_set_field (expr_id "context") (expr_id "id")
          (expr_id "$newVal"))))) expr_undefined) []))
   (expr_let "mkgetter"
    (expr_lambda ["id"]
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null
       (expr_lambda ["this"; "args"]
        (expr_if
         (expr_op2 binary_op_has_property (expr_id "object") (expr_id "id"))
         (expr_get_field (expr_id "object") (expr_id "id"))
         (expr_get_field (expr_id "context") (expr_id "id")))) expr_undefined)
      []))
    (expr_let "newcontext"
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true (expr_id "context")
       expr_null expr_undefined) [])
     (expr_let "addBinding"
      (expr_lambda ["id"]
       (expr_app (expr_id "%defineOwnProperty")
        [expr_id "newcontext";
         expr_id "id";
         expr_object
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined)
         [("set", property_data
                  (data_intro (expr_app (expr_id "mksetter") [expr_id "id"])
                   expr_true expr_false expr_false));
          ("get", property_data
                  (data_intro (expr_app (expr_id "mkgetter") [expr_id "id"])
                   expr_true expr_false expr_false));
          ("configurable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false));
          ("enumerable", property_data
                         (data_intro expr_true expr_true expr_false
                          expr_false))]]))
      (expr_seq
       (expr_app (expr_id "%primEach")
        [expr_id "names"; expr_id "addBinding"]) (expr_id "newcontext"))))))))
.
Definition privmap :=  value_object 137 .
Definition privmaplambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "callbackfn"))
          (expr_string "function")) expr_false expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "Callback not a function in map"]) expr_null)
       (expr_let "T" (expr_get_field (expr_id "args") (expr_string "1"))
        (expr_let "A"
         (expr_object
          (objattrs_intro (expr_string "Array") expr_true
           (expr_id "%ArrayProto") expr_null expr_undefined) [])
         (expr_recc "loop"
          (expr_lambda ["k"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_if
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
              (expr_let "kValue"
               (expr_get_field (expr_id "O") (expr_id "Pk"))
               (expr_let "argsObj"
                (expr_object
                 (objattrs_intro (expr_string "Object") expr_true expr_null
                  expr_null expr_undefined) [])
                (expr_seq
                 (expr_let "$newVal" (expr_id "kValue")
                  (expr_set_field (expr_id "argsObj") (expr_string "0")
                   (expr_id "$newVal")))
                 (expr_seq
                  (expr_let "$newVal" (expr_id "k")
                   (expr_set_field (expr_id "argsObj") (expr_string "1")
                    (expr_id "$newVal")))
                  (expr_seq
                   (expr_let "$newVal" (expr_id "O")
                    (expr_set_field (expr_id "argsObj") (expr_string "2")
                     (expr_id "$newVal")))
                   (expr_seq
                    (expr_let "$newVal" (expr_number (JsNumber.of_int 3))
                     (expr_set_field (expr_id "argsObj")
                      (expr_string "length") (expr_id "$newVal")))
                    (expr_seq
                     (expr_let "mappedValue"
                      (expr_app (expr_id "callbackfn")
                       [expr_id "T"; expr_id "argsObj"])
                      (expr_app (expr_id "%defineOwnProperty")
                       [expr_id "A";
                        expr_id "Pk";
                        expr_object
                        (objattrs_intro (expr_string "Object") expr_true
                         expr_null expr_null expr_undefined)
                        [("value", property_data
                                   (data_intro (expr_id "mappedValue")
                                    expr_true expr_false expr_false));
                         ("writable", property_data
                                      (data_intro expr_true expr_true
                                       expr_false expr_false));
                         ("enumerable", property_data
                                        (data_intro expr_true expr_true
                                         expr_false expr_false));
                         ("configurable", property_data
                                          (data_intro expr_true expr_true
                                           expr_false expr_false))]]))
                     (expr_app (expr_id "loop")
                      [expr_op2 binary_op_add (expr_id "k")
                       (expr_number (JsNumber.of_int 1))]))))))))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1))])))
            (expr_let "$newVal" (expr_id "k")
             (expr_set_field (expr_id "A") (expr_string "length")
              (expr_id "$newVal")))))
          (expr_seq
           (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
           (expr_break "ret" (expr_id "A")))))))))))))
.
Definition privmathAbs :=  value_object 269 .
Definition privmathAbsLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "n"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
      expr_false expr_true) (expr_break "ret" (expr_id "n")) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_number (JsNumber.of_int 0)))
      (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
     (expr_break "ret" (expr_op1 unary_op_abs (expr_id "n"))))))))
.
Definition privmathCeil :=  value_object 293 .
Definition privmathCeilLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "x"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_let "%or"
      (expr_let "%or"
       (expr_let "%or"
        (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))
         expr_false expr_true)
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_op2 binary_op_stx_eq (expr_id "x")
          (expr_number (JsNumber.of_int 0)))))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "x")
         (expr_number (JsNumber.of_int 0)))))
      (expr_if (expr_id "%or") (expr_id "%or")
       (expr_op2 binary_op_stx_eq (expr_id "x")
        (expr_number (JsNumber.of_int 0))))) (expr_break "ret" (expr_id "x"))
     expr_null) (expr_break "ret" (expr_op1 unary_op_ceil (expr_id "x")))))))
.
Definition privmathFloor :=  value_object 295 .
Definition privmathFloorLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "x"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_let "%or"
      (expr_let "%or"
       (expr_let "%or"
        (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))
         expr_false expr_true)
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_op2 binary_op_stx_eq (expr_id "x")
          (expr_number (JsNumber.of_int 0)))))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "x")
         (expr_number (JsNumber.of_int 0)))))
      (expr_if (expr_id "%or") (expr_id "%or")
       (expr_op2 binary_op_stx_eq (expr_id "x")
        (expr_number (JsNumber.of_int 0))))) (expr_break "ret" (expr_id "x"))
     expr_null) (expr_break "ret" (expr_op1 unary_op_floor (expr_id "x")))))))
.
Definition privmathLog :=  value_object 291 .
Definition privmathLogLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "n"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
      expr_false expr_true) (expr_break "ret" (expr_id "n")) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_lt (expr_id "n") (expr_number (JsNumber.of_int 0)))
      (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "n")
        (expr_number (JsNumber.of_int 0)))
       (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "n")
         (expr_number (JsNumber.of_int 1)))
        (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
       (expr_seq
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "n")
          (expr_number (JsNumber.of_int 0))) (expr_break "ret" (expr_id "n"))
         expr_null) (expr_break "ret" (expr_op1 unary_op_log (expr_id "n")))))))))))
.
Definition privmathMax :=  value_object 266 .
Definition privminMaxLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None
 ["this"; "args"; "op"; "init"]
 (expr_let "end" (expr_get_field (expr_id "args") (expr_string "length"))
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "end")
      (expr_number (JsNumber.of_int 0))) (expr_break "ret" (expr_id "init"))
     expr_null)
    (expr_recc "loop"
     (expr_lambda ["best"; "i"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
       (expr_let "curr"
        (expr_app (expr_id "%ToNumber")
         [expr_get_field (expr_id "args")
          (expr_op1 unary_op_prim_to_str (expr_id "i"))])
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "curr") (expr_id "curr"))
           expr_false expr_true)
          (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
         (expr_app (expr_id "loop")
          [expr_app (expr_id "op") [expr_id "best"; expr_id "curr"];
           expr_op2 binary_op_add (expr_id "i")
           (expr_number (JsNumber.of_int 1))]))) (expr_id "best")))
     (expr_break "ret"
      (expr_app (expr_id "loop")
       [expr_id "init"; expr_number (JsNumber.of_int 0)])))))))
.
Definition privmathMaxLambda := 
value_closure
(closure_intro [("%max", privmax); ("%minMaxLambda", privminMaxLambda)] 
 None ["this"; "args"]
 (expr_app (expr_id "%minMaxLambda")
  [expr_id "this";
   expr_id "args";
   expr_id "%max";
   expr_number (JsNumber.of_int 0)]))
.
Definition privmathMin :=  value_object 263 .
Definition privmathMinLambda := 
value_closure
(closure_intro [("%min", privmin); ("%minMaxLambda", privminMaxLambda)] 
 None ["this"; "args"]
 (expr_app (expr_id "%minMaxLambda")
  [expr_id "this";
   expr_id "args";
   expr_id "%min";
   expr_number (JsNumber.of_int 0)]))
.
Definition privmathPow :=  value_object 297 .
Definition privmathPowLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "x"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_let "y"
   (expr_app (expr_id "%ToNumber")
    [expr_get_field (expr_id "args") (expr_string "1")])
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_if (expr_op2 binary_op_stx_eq (expr_id "y") (expr_id "y"))
       expr_false expr_true)
      (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "y")
        (expr_number (JsNumber.of_int 0)))
       (expr_break "ret" (expr_number (JsNumber.of_int 1))) expr_null)
      (expr_seq
       (expr_if
        (expr_if
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))
          expr_false expr_true)
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "y")
           (expr_number (JsNumber.of_int 0))) expr_false expr_true)
         expr_false) (expr_break "ret" (expr_number (JsNumber.of_int 0)))
        expr_null)
       (expr_let "absX" (expr_op1 unary_op_abs (expr_id "x"))
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_gt (expr_id "absX")
            (expr_number (JsNumber.of_int 1)))
           (expr_op2 binary_op_stx_eq (expr_id "y")
            (expr_number (JsNumber.of_int 0))) expr_false)
          (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
         (expr_seq
          (expr_if
           (expr_if
            (expr_op2 binary_op_gt (expr_id "absX")
             (expr_number (JsNumber.of_int 1)))
            (expr_op2 binary_op_stx_eq (expr_id "y")
             (expr_number (JsNumber.of_int 0))) expr_false)
           (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
          (expr_seq
           (expr_if
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "absX")
              (expr_number (JsNumber.of_int 1)))
             (expr_let "%or"
              (expr_op2 binary_op_stx_eq (expr_id "y")
               (expr_number (JsNumber.of_int 0)))
              (expr_if (expr_id "%or") (expr_id "%or")
               (expr_op2 binary_op_stx_eq (expr_id "y")
                (expr_number (JsNumber.of_int 0))))) expr_false)
            (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
           (expr_seq
            (expr_if
             (expr_if
              (expr_op2 binary_op_lt (expr_id "absX")
               (expr_number (JsNumber.of_int 1)))
              (expr_op2 binary_op_stx_eq (expr_id "y")
               (expr_number (JsNumber.of_int 0))) expr_false)
             (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
            (expr_seq
             (expr_if
              (expr_if
               (expr_op2 binary_op_lt (expr_id "absX")
                (expr_number (JsNumber.of_int 1)))
               (expr_op2 binary_op_stx_eq (expr_id "y")
                (expr_number (JsNumber.of_int 0))) expr_false)
              (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
             (expr_seq
              (expr_if
               (expr_if
                (expr_op2 binary_op_stx_eq (expr_id "x")
                 (expr_number (JsNumber.of_int 0)))
                (expr_op2 binary_op_gt (expr_id "y")
                 (expr_number (JsNumber.of_int 0))) expr_false)
               (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
              (expr_seq
               (expr_if
                (expr_if
                 (expr_op2 binary_op_stx_eq (expr_id "x")
                  (expr_number (JsNumber.of_int 0)))
                 (expr_op2 binary_op_lt (expr_id "y")
                  (expr_number (JsNumber.of_int 0))) expr_false)
                (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                expr_null)
               (expr_let "isOdd"
                (expr_lambda ["n"]
                 (expr_let "divided"
                  (expr_op2 binary_op_div (expr_id "n")
                   (expr_number (JsNumber.of_int 2)))
                  (expr_if
                   (expr_op2 binary_op_stx_eq
                    (expr_op1 unary_op_floor (expr_id "n")) (expr_id "n"))
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_op1 unary_op_floor (expr_id "divided"))
                     (expr_id "divided")) expr_false expr_true) expr_false)))
                (expr_seq
                 (expr_if
                  (expr_if
                   (expr_op2 binary_op_stx_eq (expr_id "x")
                    (expr_number (JsNumber.of_int 0)))
                   (expr_op2 binary_op_gt (expr_id "y")
                    (expr_number (JsNumber.of_int 0))) expr_false)
                  (expr_break "ret"
                   (expr_if (expr_app (expr_id "isOdd") [expr_id "y"])
                    (expr_number (JsNumber.of_int 0))
                    (expr_number (JsNumber.of_int 0)))) expr_null)
                 (expr_seq
                  (expr_if
                   (expr_if
                    (expr_op2 binary_op_stx_eq (expr_id "x")
                     (expr_number (JsNumber.of_int 0)))
                    (expr_op2 binary_op_lt (expr_id "y")
                     (expr_number (JsNumber.of_int 0))) expr_false)
                   (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                   expr_null)
                  (expr_seq
                   (expr_if
                    (expr_if
                     (expr_op2 binary_op_stx_eq (expr_id "x")
                      (expr_number (JsNumber.of_int 0)))
                     (expr_op2 binary_op_gt (expr_id "y")
                      (expr_number (JsNumber.of_int 0))) expr_false)
                    (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                    expr_null)
                   (expr_seq
                    (expr_if
                     (expr_if
                      (expr_op2 binary_op_stx_eq (expr_id "x")
                       (expr_number (JsNumber.of_int 0)))
                      (expr_op2 binary_op_lt (expr_id "y")
                       (expr_number (JsNumber.of_int 0))) expr_false)
                     (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                     expr_null)
                    (expr_seq
                     (expr_let "oddY"
                      (expr_app (expr_id "isOdd") [expr_id "y"])
                      (expr_if
                       (expr_if
                        (expr_if
                         (expr_op2 binary_op_stx_eq (expr_id "x")
                          (expr_number (JsNumber.of_int 0)))
                         (expr_op2 binary_op_lt (expr_id "y")
                          (expr_number (JsNumber.of_int 0))) expr_false)
                        (expr_id "oddY") expr_false)
                       (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                       expr_null))
                     (expr_seq
                      (expr_if
                       (expr_if
                        (expr_op2 binary_op_stx_eq (expr_id "x")
                         (expr_number (JsNumber.of_int 0)))
                        (expr_op2 binary_op_lt (expr_id "y")
                         (expr_number (JsNumber.of_int 0))) expr_false)
                       (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                       expr_null)
                      (expr_seq
                       (expr_let "isFinite"
                        (expr_lambda ["n"]
                         (expr_if
                          (expr_if
                           (expr_op2 binary_op_stx_eq (expr_id "n")
                            (expr_number (JsNumber.of_int 0))) expr_false
                           expr_true)
                          (expr_if
                           (expr_op2 binary_op_stx_eq (expr_id "n")
                            (expr_number (JsNumber.of_int 0))) expr_false
                           expr_true) expr_false))
                        (expr_let "finiteX"
                         (expr_app (expr_id "isFinite") [expr_id "x"])
                         (expr_let "finiteY"
                          (expr_app (expr_id "isFinite") [expr_id "y"])
                          (expr_if
                           (expr_if
                            (expr_if
                             (expr_if
                              (expr_op2 binary_op_lt (expr_id "x")
                               (expr_number (JsNumber.of_int 0)))
                              (expr_id "finiteX") expr_false)
                             (expr_id "finiteY") expr_false)
                            (expr_if
                             (expr_op2 binary_op_stx_eq
                              (expr_op1 unary_op_floor (expr_id "y"))
                              (expr_id "y")) expr_false expr_true) expr_false)
                           (expr_break "ret"
                            (expr_number (JsNumber.of_int 0))) expr_null))))
                       (expr_break "ret"
                        (expr_op2 binary_op_pow (expr_id "x") (expr_id "y"))))))))))))))))))))))))))
.
Definition privmaybeDirectEval := 
value_closure
(closure_intro
 [("%AppExprCheck", privAppExprCheck);
  ("%configurableEval", privconfigurableEval);
  ("%eval", priveval)] None ["theThis"; "theContext"; "args"; "strict"]
 (expr_let "contextEval"
  (expr_get_field (expr_id "theContext") (expr_string "eval"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "contextEval") (expr_id "%eval"))
   (expr_app (expr_id "%configurableEval")
    [expr_id "theThis";
     expr_id "theContext";
     expr_id "strict";
     expr_id "args"])
   (expr_app (expr_id "%AppExprCheck")
    [expr_id "contextEval"; expr_undefined; expr_id "args"]))))
.
Definition privmkNewArgsObj := 
value_closure
(closure_intro [("%mkArgsObjBase", privmkArgsObjBase)] None ["args"]
 (expr_let "argsObj" (expr_app (expr_id "%mkArgsObjBase") [expr_id "args"])
  (expr_seq
   (expr_let "$newVal" expr_true
    (expr_set_field (expr_id "argsObj") (expr_string "%new")
     (expr_id "$newVal")))
   (expr_seq
    (expr_set_attr pattr_writable (expr_id "argsObj") (expr_string "%new")
     expr_false) (expr_id "argsObj")))))
.
Definition privnumTLS :=  value_object 308 .
Definition privtoLocaleStringlambda := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%TypeError", privTypeError)]
 None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "toString"
   (expr_get_field (expr_id "O") (expr_string "toString"))
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_code (expr_id "toString")) expr_null)
    (expr_app (expr_id "%TypeError") [expr_string "toLocaleString"])
    (expr_app (expr_id "toString")
     [expr_id "O";
      expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined) []])))))
.
Definition privnumTLSLambda := 
value_closure
(closure_intro
 [("%StringProto", privStringProto);
  ("%toLocaleStringlambda", privtoLocaleStringlambda)] None ["this"; "args"]
 (expr_let "x"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
    (expr_string "number")) (expr_id "this")
   (expr_get_obj_attr oattr_primval (expr_id "this")))
  (expr_let "obj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true (expr_id "%StringProto")
     expr_null (expr_op1 unary_op_prim_to_str (expr_id "x"))) [])
   (expr_app (expr_id "%toLocaleStringlambda")
    [expr_id "obj";
     expr_object
     (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
      expr_undefined) []]))))
.
Definition privnumToStringAbstract := 
value_closure
(closure_intro [] None ["n"; "r"]
 (expr_recc "nts"
  (expr_lambda ["n"; "r"]
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
       expr_false expr_true) (expr_break "ret" (expr_string "NaN")) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "n")
        (expr_number (JsNumber.of_int 0)))
       (expr_break "ret" (expr_string "0")) expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_lt (expr_id "n")
         (expr_number (JsNumber.of_int 0)))
        (expr_let "negOne"
         (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
          (expr_number (JsNumber.of_int 1)))
         (expr_let "newN"
          (expr_op2 binary_op_mul (expr_id "n") (expr_id "negOne"))
          (expr_break "ret"
           (expr_op2 binary_op_string_plus (expr_string "-")
            (expr_app (expr_id "nts") [expr_id "newN"; expr_id "r"])))))
        expr_null)
       (expr_seq
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "n")
          (expr_number (JsNumber.of_int 0)))
         (expr_break "ret" (expr_string "Infinity")) expr_null)
        (expr_seq
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "r")
           (expr_number (JsNumber.of_int 10)))
          (expr_break "ret" (expr_op1 unary_op_prim_to_str (expr_id "n")))
          expr_null)
         (expr_break "ret"
          (expr_op2 binary_op_base (expr_id "n") (expr_id "r"))))))))))
  (expr_app (expr_id "nts") [expr_id "n"; expr_id "r"])))
.
Definition privnumValueOf :=  value_object 301 .
Definition privnumberToString :=  value_object 160 .
Definition privnumberToStringlambda := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto);
  ("%ToInteger", privToInteger);
  ("%TypeErrorProto", privTypeErrorProto);
  ("%numToStringAbstract", privnumToStringAbstract)] None ["this"; "args"]
 (expr_let "notNumProto"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "this") (expr_id "%NumberProto"))
   expr_false expr_true)
  (expr_if
   (expr_if (expr_id "notNumProto")
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_get_obj_attr oattr_proto (expr_id "this"))
      (expr_id "%NumberProto")) expr_false expr_true) expr_false)
   (expr_throw
    (expr_object
     (objattrs_intro (expr_string "Object") expr_true
      (expr_id "%TypeErrorProto") expr_null expr_undefined) []))
   (expr_let "rint"
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
     (expr_number (JsNumber.of_int 10))
     (expr_app (expr_id "%ToInteger")
      [expr_get_field (expr_id "args") (expr_string "0")]))
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "rint")
      (expr_number (JsNumber.of_int 10)))
     (expr_app (expr_id "%numToStringAbstract")
      [expr_get_obj_attr oattr_primval (expr_id "this");
       expr_number (JsNumber.of_int 10)])
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "rint"))
        (expr_string "number"))) (expr_throw (expr_string "RangeError"))
      (expr_if
       (expr_let "%or"
        (expr_op2 binary_op_lt (expr_id "rint")
         (expr_number (JsNumber.of_int 2)))
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_op2 binary_op_gt (expr_id "rint")
          (expr_number (JsNumber.of_int 36)))))
       (expr_throw (expr_string "RangeError"))
       (expr_app (expr_id "%numToStringAbstract")
        [expr_get_obj_attr oattr_primval (expr_id "this"); expr_id "rint"]))))))))
.
Definition privobjectToString :=  value_object 41 .
Definition privparseFloat :=  value_object 320 .
Definition privparseFloatLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "parseFloat NYI"))
.
Definition privparseInt :=  value_object 256 .
Definition privparseIntlambda := 
value_closure
(closure_intro [("%ToString", privToString)] None ["this"; "args"]
 (expr_let "numstr"
  (expr_app (expr_id "%ToString")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_op1 unary_op_numstr_to_num (expr_id "numstr"))))
.
Definition privpop :=  value_object 85 .
Definition privpoplambda := 
value_closure
(closure_intro
 [("%ToNumber", privToNumber);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "len")
      (expr_number (JsNumber.of_int 0)))
     (expr_seq
      (expr_let "$newVal" (expr_number (JsNumber.of_int 0))
       (expr_set_field (expr_id "O") (expr_string "length")
        (expr_id "$newVal"))) expr_undefined)
     (expr_let "indx"
      (expr_app (expr_id "%ToString")
       [expr_op2 binary_op_sub (expr_id "len")
        (expr_number (JsNumber.of_int 1))])
      (expr_let "element" (expr_get_field (expr_id "O") (expr_id "indx"))
       (expr_seq (expr_delete_field (expr_id "O") (expr_id "indx"))
        (expr_seq
         (expr_let "$newVal"
          (expr_app (expr_id "%ToNumber") [expr_id "indx"])
          (expr_set_field (expr_id "O") (expr_string "length")
           (expr_id "$newVal"))) (expr_id "element"))))))))))
.
Definition privpreventExtensions :=  value_object 71 .
Definition privpreventExtensionsLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_seq (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
    (expr_id "O")))))
.
Definition privprint :=  value_object 17 .
Definition privprintlambda := 
value_closure
(closure_intro [("%ToString", privToString)] None ["o"; "s"]
 (expr_op1 unary_op_print
  (expr_app (expr_id "%ToString")
   [expr_get_field (expr_id "s") (expr_string "0")])))
.
Definition privpropEnumlambda := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%ToString", privToString)]
 None ["this"; "args"]
 (expr_let "getOwnProperty"
  (expr_lambda ["o"; "f"]
   (expr_if (expr_op2 binary_op_has_own_property (expr_id "o") (expr_id "f"))
    (expr_get_field (expr_id "o") (expr_id "f")) expr_undefined))
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_field (expr_id "args") (expr_string "0")) expr_undefined)
   expr_false
   (expr_let "P"
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
     (expr_let "desc"
      (expr_app (expr_id "getOwnProperty") [expr_id "O"; expr_id "P"])
      (expr_if (expr_op2 binary_op_stx_eq (expr_id "desc") expr_undefined)
       expr_false (expr_get_attr pattr_enum (expr_id "O") (expr_id "P")))))))))
.
Definition privpropertyIsEnumerable :=  value_object 42 .
Definition privprotoOfField := 
value_closure
(closure_intro [] (Some "%protoOfField") ["object"; "fld"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "object") expr_null)
  (expr_id "object")
  (expr_if
   (expr_op2 binary_op_has_own_property (expr_id "object") (expr_id "fld"))
   (expr_id "object")
   (expr_app (expr_id "%protoOfField")
    [expr_get_obj_attr oattr_proto (expr_id "object"); expr_id "fld"]))))
.
Definition privpush :=  value_object 88 .
Definition privpushlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%set-property", privset_property)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_recc "loop"
     (expr_lambda ["i"; "n"]
      (expr_if
       (expr_op2 binary_op_lt (expr_id "i")
        (expr_get_field (expr_id "args") (expr_string "length")))
       (expr_seq
        (expr_let "ii" (expr_op1 unary_op_prim_to_str (expr_id "i"))
         (expr_app (expr_id "%set-property")
          [expr_id "O";
           expr_app (expr_id "%ToString") [expr_id "n"];
           expr_get_field (expr_id "args") (expr_id "ii")]))
        (expr_app (expr_id "loop")
         [expr_op2 binary_op_add (expr_id "i")
          (expr_number (JsNumber.of_int 1));
          expr_op2 binary_op_add (expr_id "n")
          (expr_number (JsNumber.of_int 1))])) (expr_id "n")))
     (expr_app (expr_id "loop")
      [expr_number (JsNumber.of_int 0); expr_id "len"]))))))
.
Definition privrandom :=  value_object 281 .
Definition privrandomLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_number (JsNumber.of_int 4)))
.
Definition privreduce :=  value_object 142 .
Definition privreduceRight :=  value_object 151 .
Definition privreduceRightLambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_let "has_initial"
      (expr_op2 binary_op_ge
       (expr_get_field (expr_id "args") (expr_string "length"))
       (expr_number (JsNumber.of_int 2)))
      (expr_label "ret"
       (expr_seq
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_op1 unary_op_typeof (expr_id "callbackfn"))
           (expr_string "function")) expr_false expr_true)
         (expr_app (expr_id "%TypeError")
          [expr_string "Callback not function in reduceRight"]) expr_null)
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "len")
            (expr_number (JsNumber.of_int 0)))
           (expr_op1 unary_op_not (expr_id "has_initial")) expr_false)
          (expr_app (expr_id "%TypeError")
           [expr_string "Zero-length array in reduceRight"]) expr_null)
         (expr_let "origK"
          (expr_if (expr_id "has_initial") (expr_id "len")
           (expr_recc "accumLoop"
            (expr_lambda ["k"]
             (expr_if
              (expr_op2 binary_op_ge (expr_id "k")
               (expr_number (JsNumber.of_int 0)))
              (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
               (expr_let "kPresent"
                (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
                (expr_if (expr_id "kPresent") (expr_id "k")
                 (expr_app (expr_id "accumLoop")
                  [expr_op2 binary_op_sub (expr_id "k")
                   (expr_number (JsNumber.of_int 1))]))))
              (expr_app (expr_id "%TypeError") [expr_string "reduceRight"])))
            (expr_app (expr_id "accumLoop")
             [expr_op2 binary_op_sub (expr_id "len")
              (expr_number (JsNumber.of_int 1))])))
          (expr_let "accumulator"
           (expr_if (expr_id "has_initial")
            (expr_get_field (expr_id "args") (expr_string "1"))
            (expr_get_field (expr_id "O")
             (expr_app (expr_id "%ToString") [expr_id "origK"])))
           (expr_recc "outerLoop"
            (expr_lambda ["k"; "accumulator"]
             (expr_if
              (expr_op2 binary_op_ge (expr_id "k")
               (expr_number (JsNumber.of_int 0)))
              (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
               (expr_let "kPresent"
                (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
                (expr_if (expr_id "kPresent")
                 (expr_let "kValue"
                  (expr_get_field (expr_id "O") (expr_id "Pk"))
                  (expr_let "argsObj"
                   (expr_object
                    (objattrs_intro (expr_string "Object") expr_true
                     expr_null expr_null expr_undefined) [])
                   (expr_seq
                    (expr_let "$newVal" (expr_id "accumulator")
                     (expr_set_field (expr_id "argsObj") (expr_string "0")
                      (expr_id "$newVal")))
                    (expr_seq
                     (expr_let "$newVal" (expr_id "kValue")
                      (expr_set_field (expr_id "argsObj") (expr_string "1")
                       (expr_id "$newVal")))
                     (expr_seq
                      (expr_let "$newVal" (expr_id "k")
                       (expr_set_field (expr_id "argsObj") (expr_string "2")
                        (expr_id "$newVal")))
                      (expr_seq
                       (expr_let "$newVal" (expr_id "O")
                        (expr_set_field (expr_id "argsObj") (expr_string "3")
                         (expr_id "$newVal")))
                       (expr_seq
                        (expr_let "$newVal" (expr_number (JsNumber.of_int 4))
                         (expr_set_field (expr_id "argsObj")
                          (expr_string "length") (expr_id "$newVal")))
                        (expr_let "next"
                         (expr_app (expr_id "callbackfn")
                          [expr_undefined; expr_id "argsObj"])
                         (expr_app (expr_id "outerLoop")
                          [expr_op2 binary_op_sub (expr_id "k")
                           (expr_number (JsNumber.of_int 1));
                           expr_id "next"])))))))))
                 (expr_app (expr_id "outerLoop")
                  [expr_op2 binary_op_sub (expr_id "k")
                   (expr_number (JsNumber.of_int 1));
                   expr_id "accumulator"])))) (expr_id "accumulator")))
            (expr_break "ret"
             (expr_app (expr_id "outerLoop")
              [expr_op2 binary_op_sub (expr_id "origK")
               (expr_number (JsNumber.of_int 1));
               expr_id "accumulator"]))))))))))))))
.
Definition privreducelambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_let "has_initial"
      (expr_op2 binary_op_ge
       (expr_get_field (expr_id "args") (expr_string "length"))
       (expr_number (JsNumber.of_int 2)))
      (expr_label "ret"
       (expr_seq
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_op1 unary_op_typeof (expr_id "callbackfn"))
           (expr_string "function")) expr_false expr_true)
         (expr_app (expr_id "%TypeError")
          [expr_string "Callback not a function in reduce"]) expr_null)
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "len")
            (expr_number (JsNumber.of_int 0)))
           (expr_op1 unary_op_not (expr_id "has_initial")) expr_false)
          (expr_app (expr_id "%TypeError")
           [expr_string "Reducing an empty list with not enough arguments."])
          expr_null)
         (expr_let "origK"
          (expr_if (expr_id "has_initial")
           (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
            (expr_number (JsNumber.of_int 1)))
           (expr_recc "accumLoop"
            (expr_lambda ["k"]
             (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
              (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
               (expr_let "kPresent"
                (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
                (expr_if (expr_id "kPresent") (expr_id "k")
                 (expr_app (expr_id "accumLoop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1))]))))
              (expr_app (expr_id "%TypeError")
               [expr_string "In Array reduce"])))
            (expr_app (expr_id "accumLoop") [expr_number (JsNumber.of_int 0)])))
          (expr_let "accumulator"
           (expr_if (expr_id "has_initial")
            (expr_get_field (expr_id "args") (expr_string "1"))
            (expr_get_field (expr_id "O")
             (expr_app (expr_id "%ToString") [expr_id "origK"])))
           (expr_recc "outerLoop"
            (expr_lambda ["k"; "accumulator"]
             (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
              (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
               (expr_let "kPresent"
                (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
                (expr_if (expr_id "kPresent")
                 (expr_let "kValue"
                  (expr_get_field (expr_id "O") (expr_id "Pk"))
                  (expr_let "argsObj"
                   (expr_object
                    (objattrs_intro (expr_string "Object") expr_true
                     expr_null expr_null expr_undefined) [])
                   (expr_seq
                    (expr_let "$newVal" (expr_id "accumulator")
                     (expr_set_field (expr_id "argsObj") (expr_string "0")
                      (expr_id "$newVal")))
                    (expr_seq
                     (expr_let "$newVal" (expr_id "kValue")
                      (expr_set_field (expr_id "argsObj") (expr_string "1")
                       (expr_id "$newVal")))
                     (expr_seq
                      (expr_let "$newVal" (expr_id "k")
                       (expr_set_field (expr_id "argsObj") (expr_string "2")
                        (expr_id "$newVal")))
                      (expr_seq
                       (expr_let "$newVal" (expr_id "O")
                        (expr_set_field (expr_id "argsObj") (expr_string "3")
                         (expr_id "$newVal")))
                       (expr_seq
                        (expr_let "$newVal" (expr_number (JsNumber.of_int 4))
                         (expr_set_field (expr_id "argsObj")
                          (expr_string "length") (expr_id "$newVal")))
                        (expr_let "next"
                         (expr_app (expr_id "callbackfn")
                          [expr_undefined; expr_id "argsObj"])
                         (expr_app (expr_id "outerLoop")
                          [expr_op2 binary_op_add (expr_id "k")
                           (expr_number (JsNumber.of_int 1));
                           expr_id "next"])))))))))
                 (expr_app (expr_id "outerLoop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1));
                   expr_id "accumulator"])))) (expr_id "accumulator")))
            (expr_break "ret"
             (expr_app (expr_id "outerLoop")
              [expr_op2 binary_op_add (expr_id "origK")
               (expr_number (JsNumber.of_int 1));
               expr_id "accumulator"]))))))))))))))
.
Definition privreplace :=  value_object 164 .
Definition privsubstringlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
    (expr_let "intStart"
     (expr_app (expr_id "%ToInteger")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_let "intEnd"
      (expr_let "end" (expr_get_field (expr_id "args") (expr_string "1"))
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "end") expr_undefined)
        (expr_id "len") (expr_app (expr_id "%ToInteger") [expr_id "end"])))
      (expr_let "finalStart"
       (expr_app (expr_id "%min")
        [expr_app (expr_id "%max")
         [expr_id "intStart"; expr_number (JsNumber.of_int 0)];
         expr_id "len"])
       (expr_let "finalEnd"
        (expr_app (expr_id "%min")
         [expr_app (expr_id "%max")
          [expr_id "intEnd"; expr_number (JsNumber.of_int 0)];
          expr_id "len"])
        (expr_let "from"
         (expr_app (expr_id "%min")
          [expr_id "finalStart"; expr_id "finalEnd"])
         (expr_let "to"
          (expr_app (expr_id "%max")
           [expr_id "finalStart"; expr_id "finalEnd"])
          (expr_recc "loop"
           (expr_lambda ["i"; "soFar"]
            (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "to"))
             (expr_app (expr_id "loop")
              [expr_op2 binary_op_add (expr_id "i")
               (expr_number (JsNumber.of_int 1));
               expr_op2 binary_op_string_plus (expr_id "soFar")
               (expr_op2 binary_op_char_at (expr_id "S") (expr_id "i"))])
             (expr_id "soFar")))
           (expr_app (expr_id "loop") [expr_id "from"; expr_string ""]))))))))))))
.
Definition privtwoArgObj := 
value_closure
(closure_intro [("%mkArgsObj", privmkArgsObj)] None ["arg1"; "arg2"]
 (expr_app (expr_id "%mkArgsObj")
  [expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
    expr_undefined)
   [("0", property_data
          (data_intro (expr_id "arg1") expr_false expr_false expr_false));
    ("1", property_data
          (data_intro (expr_id "arg2") expr_false expr_false expr_false));
    ("length", property_data
               (data_intro (expr_number (JsNumber.of_int 2)) expr_false
                expr_false expr_false))]]))
.
Definition privreplacelambda := 
value_closure
(closure_intro
 [("%StringIndexOflambda", privStringIndexOflambda);
  ("%ToString", privToString);
  ("%oneArgObj", privoneArgObj);
  ("%substringlambda", privsubstringlambda);
  ("%twoArgObj", privtwoArgObj)] None ["this"; "args"]
 (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
  (expr_let "search"
   (expr_app (expr_id "%ToString")
    [expr_get_field (expr_id "args") (expr_string "0")])
   (expr_let "replace" (expr_get_field (expr_id "args") (expr_string "1"))
    (expr_if
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_op1 unary_op_typeof (expr_id "replace"))
       (expr_string "function")) expr_false expr_true)
     (expr_throw (expr_string "String.replace() only supports functions"))
     (expr_recc "loop"
      (expr_lambda ["str"]
       (expr_let "start"
        (expr_app (expr_id "%StringIndexOflambda")
         [expr_id "str"; expr_app (expr_id "%oneArgObj") [expr_id "search"]])
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "start")
          (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
           (expr_number (JsNumber.of_int 1)))) (expr_id "str")
         (expr_let "replaced"
          (expr_app (expr_id "%ToString")
           [expr_app (expr_id "replace")
            [expr_undefined;
             expr_app (expr_id "%oneArgObj") [expr_id "replace"]]])
          (expr_let "before"
           (expr_app (expr_id "%substringlambda")
            [expr_id "str";
             expr_app (expr_id "%twoArgObj")
             [expr_number (JsNumber.of_int 0); expr_id "start"]])
           (expr_let "afterix"
            (expr_op2 binary_op_add (expr_id "start")
             (expr_op1 unary_op_strlen (expr_id "search")))
            (expr_let "after"
             (expr_app (expr_id "%substringlambda")
              [expr_id "str";
               expr_app (expr_id "%oneArgObj") [expr_id "afterix"]])
             (expr_op2 binary_op_string_plus (expr_id "before")
              (expr_op2 binary_op_string_plus (expr_id "replaced")
               (expr_app (expr_id "loop") [expr_id "after"]))))))))))
      (expr_app (expr_id "loop") [expr_id "S"])))))))
.
Definition privresolveThis := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto);
  ("%NumberProto", privNumberProto);
  ("%StringProto", privStringProto);
  ("%global", privglobal)] None ["strict"; "obj"]
 (expr_if (expr_id "strict")
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "obj"))
     (expr_string "object"))
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "obj") expr_null) expr_false
     expr_true) expr_false)
   (expr_let "klass" (expr_get_obj_attr oattr_class (expr_id "obj"))
    (expr_if
     (expr_if
      (expr_let "%or"
       (expr_let "%or"
        (expr_op2 binary_op_stx_eq (expr_id "klass") (expr_string "Number"))
        (expr_if (expr_id "%or") (expr_id "%or")
         (expr_op2 binary_op_stx_eq (expr_id "klass") (expr_string "String"))))
       (expr_if (expr_id "%or") (expr_id "%or")
        (expr_op2 binary_op_stx_eq (expr_id "klass") (expr_string "Boolean"))))
      (expr_if
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "obj") (expr_id "%StringProto"))
         expr_false expr_true)
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "obj") (expr_id "%NumberProto"))
         expr_false expr_true) expr_false)
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "obj") (expr_id "%BooleanProto"))
        expr_false expr_true) expr_false) expr_false)
     (expr_get_obj_attr oattr_primval (expr_id "obj")) (expr_id "obj")))
   (expr_id "obj"))
  (expr_if
   (expr_let "%or" (expr_op2 binary_op_stx_eq (expr_id "obj") expr_null)
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_stx_eq (expr_id "obj") expr_undefined)))
   (expr_id "%global") (expr_id "obj"))))
.
Definition privreverse :=  value_object 91 .
Definition privreverselambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_let "middle"
     (expr_op1 unary_op_floor
      (expr_op2 binary_op_div (expr_id "len")
       (expr_number (JsNumber.of_int 2))))
     (expr_recc "loop"
      (expr_lambda ["lower"]
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "lower") (expr_id "middle"))
         expr_false expr_true)
        (expr_label "ret"
         (expr_let "upper"
          (expr_op2 binary_op_sub
           (expr_op2 binary_op_sub (expr_id "len") (expr_id "lower"))
           (expr_number (JsNumber.of_int 1)))
          (expr_let "upperP"
           (expr_app (expr_id "%ToString") [expr_id "upper"])
           (expr_let "lowerP"
            (expr_app (expr_id "%ToString") [expr_id "lower"])
            (expr_let "lowerValue"
             (expr_get_field (expr_id "O") (expr_id "lowerP"))
             (expr_let "upperValue"
              (expr_get_field (expr_id "O") (expr_id "upperP"))
              (expr_let "lowerExists"
               (expr_op2 binary_op_has_property (expr_id "O")
                (expr_id "lowerP"))
               (expr_let "upperExists"
                (expr_op2 binary_op_has_property (expr_id "O")
                 (expr_id "upperP"))
                (expr_seq
                 (expr_if
                  (expr_if (expr_id "lowerExists") (expr_id "upperExists")
                   expr_false)
                  (expr_seq
                   (expr_let "$newVal" (expr_id "upperValue")
                    (expr_set_field (expr_id "O") (expr_id "lowerP")
                     (expr_id "$newVal")))
                   (expr_seq
                    (expr_let "$newVal" (expr_id "lowerValue")
                     (expr_set_field (expr_id "O") (expr_id "upperP")
                      (expr_id "$newVal")))
                    (expr_break "ret"
                     (expr_app (expr_id "loop")
                      [expr_op2 binary_op_add (expr_id "lower")
                       (expr_number (JsNumber.of_int 1))])))) expr_null)
                 (expr_seq
                  (expr_if (expr_id "upperExists")
                   (expr_seq
                    (expr_let "$newVal" (expr_id "upperValue")
                     (expr_set_field (expr_id "O") (expr_id "lowerP")
                      (expr_id "$newVal")))
                    (expr_seq
                     (expr_delete_field (expr_id "O") (expr_id "upperP"))
                     (expr_break "ret"
                      (expr_app (expr_id "loop")
                       [expr_op2 binary_op_add (expr_id "lower")
                        (expr_number (JsNumber.of_int 1))])))) expr_null)
                  (expr_seq
                   (expr_if (expr_id "lowerExists")
                    (expr_seq
                     (expr_delete_field (expr_id "O") (expr_id "lowerP"))
                     (expr_seq
                      (expr_let "$newVal" (expr_id "lowerValue")
                       (expr_set_field (expr_id "O") (expr_id "upperP")
                        (expr_id "$newVal")))
                      (expr_break "ret"
                       (expr_app (expr_id "loop")
                        [expr_op2 binary_op_add (expr_id "lower")
                         (expr_number (JsNumber.of_int 1))])))) expr_null)
                   (expr_break "ret"
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "lower")
                      (expr_number (JsNumber.of_int 1))])))))))))))))
        expr_undefined))
      (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
       (expr_id "O"))))))))
.
Definition privround :=  value_object 283 .
Definition privroundLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "round NYI"))
.
Definition privseal :=  value_object 67 .
Definition privsealLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"]
 (expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
   (expr_seq
    (expr_let "names" (expr_own_field_names (expr_id "O"))
     (expr_let "len"
      (expr_get_field (expr_id "names") (expr_string "length"))
      (expr_recc "loop"
       (expr_lambda ["i"]
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_seq
          (expr_let "name"
           (expr_get_field (expr_id "names")
            (expr_op1 unary_op_prim_to_str (expr_id "i")))
           (expr_set_attr pattr_config (expr_id "O") (expr_id "name")
            expr_false))
          (expr_app (expr_id "loop")
           [expr_op2 binary_op_add (expr_id "i")
            (expr_number (JsNumber.of_int 1))])) expr_null))
       (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)]))))
    (expr_seq (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
     (expr_id "O"))))))
.
Definition privshift :=  value_object 94 .
Definition privshiftlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "len")
      (expr_number (JsNumber.of_int 0)))
     (expr_seq
      (expr_let "$newVal" (expr_number (JsNumber.of_int 0))
       (expr_set_field (expr_id "O") (expr_string "length")
        (expr_id "$newVal"))) expr_undefined)
     (expr_let "first" (expr_get_field (expr_id "O") (expr_string "0"))
      (expr_seq
       (expr_recc "loop"
        (expr_lambda ["k"]
         (expr_label "ret"
          (expr_seq
           (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "len"))
            (expr_break "ret" expr_undefined) expr_null)
           (expr_let "from" (expr_app (expr_id "%ToString") [expr_id "k"])
            (expr_let "to"
             (expr_app (expr_id "%ToString")
              [expr_op2 binary_op_sub (expr_id "k")
               (expr_number (JsNumber.of_int 1))])
             (expr_let "fromPresent"
              (expr_op2 binary_op_has_property (expr_id "O") (expr_id "from"))
              (expr_if (expr_id "fromPresent")
               (expr_seq
                (expr_let "fromVal"
                 (expr_get_field (expr_id "O") (expr_id "from"))
                 (expr_let "$newVal" (expr_id "fromVal")
                  (expr_set_field (expr_id "O") (expr_id "to")
                   (expr_id "$newVal"))))
                (expr_break "ret"
                 (expr_app (expr_id "loop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1))])))
               (expr_seq (expr_delete_field (expr_id "O") (expr_id "to"))
                (expr_break "ret"
                 (expr_app (expr_id "loop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1))]))))))))))
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 1)]))
       (expr_let "newLen"
        (expr_op2 binary_op_sub (expr_id "len")
         (expr_number (JsNumber.of_int 1)))
        (expr_seq
         (expr_delete_field (expr_id "O")
          (expr_app (expr_id "%ToString") [expr_id "newLen"]))
         (expr_seq
          (expr_let "$newVal" (expr_id "newLen")
           (expr_set_field (expr_id "O") (expr_string "length")
            (expr_id "$newVal"))) (expr_id "first")))))))))))
.
Definition privsin :=  value_object 285 .
Definition privsinLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 (expr_let "n"
  (expr_app (expr_id "%ToNumber")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
      expr_false expr_true) (expr_break "ret" (expr_id "n")) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_number (JsNumber.of_int 0))) (expr_break "ret" (expr_id "n"))
      expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "n")
        (expr_number (JsNumber.of_int 0)))
       (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "n")
         (expr_number (JsNumber.of_int 0)))
        (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
       (expr_break "ret" (expr_op1 unary_op_sin (expr_id "n"))))))))))
.
Definition privslice :=  value_object 154 .
Definition privsliolambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToNumber", privToNumber);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "searchStr"
    (expr_app (expr_id "%ToString")
     [expr_get_field (expr_id "args") (expr_string "0")])
    (expr_let "numPos"
     (expr_app (expr_id "%ToNumber")
      [expr_get_field (expr_id "args") (expr_string "1")])
     (expr_let "pos"
      (expr_if
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "numPos") (expr_id "numPos"))
        expr_false expr_true) (expr_number (JsNumber.of_int 0))
       (expr_app (expr_id "%ToInteger") [expr_id "numPos"]))
      (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
       (expr_let "start"
        (expr_app (expr_id "%min")
         [expr_app (expr_id "%max")
          [expr_id "pos"; expr_number (JsNumber.of_int 0)];
          expr_id "len"])
        (expr_let "searchLen"
         (expr_op1 unary_op_strlen (expr_id "searchStr"))
         (expr_let "check_k"
          (expr_lambda ["k"]
           (expr_recc "check_j"
            (expr_lambda ["j"]
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "j") (expr_id "searchLen"))
              expr_true
              (expr_if
               (expr_if
                (expr_op2 binary_op_stx_eq
                 (expr_op2 binary_op_char_at (expr_id "S")
                  (expr_op2 binary_op_add (expr_id "k") (expr_id "j")))
                 (expr_op2 binary_op_char_at (expr_id "searchStr")
                  (expr_id "j"))) expr_false expr_true) expr_false
               (expr_app (expr_id "check_j")
                [expr_op2 binary_op_add (expr_id "j")
                 (expr_number (JsNumber.of_int 1))]))))
            (expr_if
             (expr_op1 unary_op_not
              (expr_op2 binary_op_le
               (expr_op2 binary_op_add (expr_id "k") (expr_id "searchLen"))
               (expr_id "len"))) expr_false
             (expr_if
              (expr_op1 unary_op_not
               (expr_app (expr_id "check_j")
                [expr_number (JsNumber.of_int 0)])) expr_false expr_true))))
          (expr_recc "find_k"
           (expr_lambda ["curr"]
            (expr_if
             (expr_op2 binary_op_lt (expr_id "curr")
              (expr_number (JsNumber.of_int 0)))
             (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
              (expr_number (JsNumber.of_int 1)))
             (expr_if (expr_app (expr_id "check_k") [expr_id "curr"])
              (expr_id "curr")
              (expr_app (expr_id "find_k")
               [expr_op2 binary_op_sub (expr_id "curr")
                (expr_number (JsNumber.of_int 1))]))))
           (expr_app (expr_id "find_k") [expr_id "start"]))))))))))))
.
Definition privsome :=  value_object 148 .
Definition privsomelambda := 
value_closure
(closure_intro
 [("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
    (expr_let "callbackfn"
     (expr_get_field (expr_id "args") (expr_string "0"))
     (expr_label "ret"
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_op1 unary_op_typeof (expr_id "callbackfn"))
          (expr_string "function")) expr_false expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "Callback not function in some"]) expr_null)
       (expr_let "T" (expr_get_field (expr_id "args") (expr_string "1"))
        (expr_recc "loop"
         (expr_lambda ["k"]
          (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
           (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
            (expr_let "kPresent"
             (expr_op2 binary_op_has_property (expr_id "O") (expr_id "Pk"))
             (expr_if (expr_id "kPresent")
              (expr_let "kValue"
               (expr_get_field (expr_id "O") (expr_id "Pk"))
               (expr_let "argsObj"
                (expr_object
                 (objattrs_intro (expr_string "Object") expr_true expr_null
                  expr_null expr_undefined) [])
                (expr_seq
                 (expr_let "$newVal" (expr_id "kValue")
                  (expr_set_field (expr_id "argsObj") (expr_string "0")
                   (expr_id "$newVal")))
                 (expr_seq
                  (expr_let "$newVal" (expr_id "k")
                   (expr_set_field (expr_id "argsObj") (expr_string "1")
                    (expr_id "$newVal")))
                  (expr_seq
                   (expr_let "$newVal" (expr_id "O")
                    (expr_set_field (expr_id "argsObj") (expr_string "2")
                     (expr_id "$newVal")))
                   (expr_seq
                    (expr_let "$newVal" (expr_number (JsNumber.of_int 3))
                     (expr_set_field (expr_id "argsObj")
                      (expr_string "length") (expr_id "$newVal")))
                    (expr_let "testResult"
                     (expr_app (expr_id "callbackfn")
                      [expr_id "T"; expr_id "argsObj"])
                     (expr_if
                      (expr_op2 binary_op_stx_eq
                       (expr_app (expr_id "%ToBoolean")
                        [expr_id "testResult"]) expr_true) expr_true
                      (expr_app (expr_id "loop")
                       [expr_op2 binary_op_add (expr_id "k")
                        (expr_number (JsNumber.of_int 1))])))))))))
              (expr_app (expr_id "loop")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int 1))])))) expr_false))
         (expr_break "ret"
          (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))))))
.
Definition privsort :=  value_object 105 .
Definition privsortlambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%TypeErrorProto", privTypeErrorProto)] None ["this"; "args"]
 (expr_let "obj" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "sortCompare"
   (expr_lambda ["j"; "k"]
    (expr_let "jString" (expr_app (expr_id "%ToString") [expr_id "j"])
     (expr_let "kString" (expr_app (expr_id "%ToString") [expr_id "k"])
      (expr_let "hasj"
       (expr_op2 binary_op_has_property (expr_id "obj") (expr_id "jString"))
       (expr_let "hask"
        (expr_op2 binary_op_has_property (expr_id "obj") (expr_id "kString"))
        (expr_label "ret"
         (expr_seq
          (expr_if
           (expr_if (expr_op2 binary_op_stx_eq (expr_id "hasj") expr_false)
            (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false)
            expr_false) (expr_break "ret" (expr_number (JsNumber.of_int 0)))
           expr_null)
          (expr_seq
           (expr_if (expr_op2 binary_op_stx_eq (expr_id "hasj") expr_false)
            (expr_break "ret" (expr_number (JsNumber.of_int 1))) expr_null)
           (expr_seq
            (expr_if (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false)
             (expr_break "ret"
              (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
               (expr_number (JsNumber.of_int 1)))) expr_null)
            (expr_let "x"
             (expr_get_field (expr_id "obj") (expr_id "jString"))
             (expr_let "y"
              (expr_get_field (expr_id "obj") (expr_id "kString"))
              (expr_seq
               (expr_if
                (expr_if
                 (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
                 (expr_op2 binary_op_stx_eq (expr_id "y") expr_undefined)
                 expr_false)
                (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                expr_null)
               (expr_seq
                (expr_if
                 (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
                 (expr_break "ret" (expr_number (JsNumber.of_int 1)))
                 expr_null)
                (expr_seq
                 (expr_if
                  (expr_op2 binary_op_stx_eq (expr_id "y") expr_undefined)
                  (expr_break "ret"
                   (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
                    (expr_number (JsNumber.of_int 1)))) expr_null)
                 (expr_seq
                  (expr_if
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_get_field (expr_id "args") (expr_string "0"))
                     expr_undefined) expr_false expr_true)
                   (expr_seq
                    (expr_if
                     (expr_if
                      (expr_op2 binary_op_stx_eq
                       (expr_op1 unary_op_typeof
                        (expr_get_field (expr_id "args") (expr_string "0")))
                       (expr_string "function")) expr_false expr_true)
                     (expr_throw
                      (expr_app (expr_id "%JSError")
                       [expr_object
                        (objattrs_intro (expr_string "Object") expr_true
                         (expr_id "%TypeErrorProto") expr_null expr_undefined)
                        []])) expr_null)
                    (expr_break "ret"
                     (expr_app
                      (expr_get_field (expr_id "args") (expr_string "0"))
                      [expr_undefined;
                       expr_object
                       (objattrs_intro (expr_string "Object") expr_true
                        expr_null expr_null expr_undefined)
                       [("0", property_data
                              (data_intro (expr_id "x") expr_true expr_false
                               expr_false));
                        ("1", property_data
                              (data_intro (expr_id "y") expr_true expr_false
                               expr_false))]]))) expr_null)
                  (expr_let "xString"
                   (expr_app (expr_id "%ToString") [expr_id "x"])
                   (expr_let "yString"
                    (expr_app (expr_id "%ToString") [expr_id "y"])
                    (expr_seq
                     (expr_if
                      (expr_op2 binary_op_string_lt (expr_id "xString")
                       (expr_id "yString"))
                      (expr_break "ret"
                       (expr_op2 binary_op_sub
                        (expr_number (JsNumber.of_int 0))
                        (expr_number (JsNumber.of_int 1)))) expr_null)
                     (expr_seq
                      (expr_if
                       (expr_op2 binary_op_string_lt (expr_id "yString")
                        (expr_id "xString"))
                       (expr_break "ret" (expr_number (JsNumber.of_int 1)))
                       expr_null)
                      (expr_break "ret" (expr_number (JsNumber.of_int 0))))))))))))))))))))))
   (expr_let "insert"
    (expr_lambda ["elt"; "before"]
     (expr_recc "insertAndShift"
      (expr_lambda ["prior"; "i"]
       (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
        (expr_let "next" (expr_get_field (expr_id "obj") (expr_id "indx"))
         (expr_seq
          (expr_let "$newVal" (expr_id "prior")
           (expr_set_field (expr_id "obj") (expr_id "indx")
            (expr_id "$newVal")))
          (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "before"))
           (expr_app (expr_id "insertAndShift")
            [expr_id "next";
             expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int 1))]) expr_undefined)))))
      (expr_recc "loop"
       (expr_lambda ["currIndex"]
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "currIndex") (expr_id "before"))
         expr_undefined
         (expr_let "indx"
          (expr_op1 unary_op_prim_to_str (expr_id "currIndex"))
          (expr_let "result"
           (expr_app (expr_id "sortCompare")
            [expr_id "currIndex"; expr_id "before"])
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "result")
             (expr_number (JsNumber.of_int 1)))
            (expr_let "old" (expr_get_field (expr_id "obj") (expr_id "indx"))
             (expr_seq
              (expr_let "$newVal" (expr_id "elt")
               (expr_set_field (expr_id "obj") (expr_id "indx")
                (expr_id "$newVal")))
              (expr_app (expr_id "insertAndShift")
               [expr_id "old";
                expr_op2 binary_op_add (expr_id "currIndex")
                (expr_number (JsNumber.of_int 1))])))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "currIndex")
              (expr_number (JsNumber.of_int 1))]))))))
       (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)]))))
    (expr_let "len" (expr_get_field (expr_id "obj") (expr_string "length"))
     (expr_recc "isort"
      (expr_lambda ["i"]
       (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
        (expr_seq
         (expr_app (expr_id "insert")
          [expr_get_field (expr_id "obj")
           (expr_op1 unary_op_prim_to_str (expr_id "i"));
           expr_id "i"])
         (expr_app (expr_id "isort")
          [expr_op2 binary_op_add (expr_id "i")
           (expr_number (JsNumber.of_int 1))])) (expr_id "obj")))
      (expr_app (expr_id "isort") [expr_number (JsNumber.of_int 1)])))))))
.
Definition privsplice :=  value_object 122 .
Definition privsplicelambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"]
 (expr_let "start" (expr_get_field (expr_id "args") (expr_string "0"))
  (expr_let "deleteCount" (expr_get_field (expr_id "args") (expr_string "1"))
   (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
    (expr_let "emptyobj"
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined) [])
     (expr_let "A"
      (expr_object
       (objattrs_intro (expr_string "Array") expr_true
        (expr_id "%ArrayProto") expr_null expr_undefined)
       [("length", property_data
                   (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                    expr_false expr_false))])
      (expr_let "lenVal"
       (expr_get_field (expr_id "O") (expr_string "length"))
       (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
        (expr_let "relativeStart"
         (expr_app (expr_id "%ToInteger") [expr_id "start"])
         (expr_let "actualStart"
          (expr_if
           (expr_op2 binary_op_lt (expr_id "relativeStart")
            (expr_number (JsNumber.of_int 0)))
           (expr_app (expr_id "%max")
            [expr_op2 binary_op_add (expr_id "len") (expr_id "relativeStart");
             expr_number (JsNumber.of_int 0)])
           (expr_app (expr_id "%min")
            [expr_id "relativeStart"; expr_id "len"]))
          (expr_let "actualDeleteCount"
           (expr_app (expr_id "%min")
            [expr_app (expr_id "%max")
             [expr_app (expr_id "%ToInteger") [expr_id "deleteCount"];
              expr_number (JsNumber.of_int 0)];
             expr_op2 binary_op_sub (expr_id "len") (expr_id "actualStart")])
           (expr_seq
            (expr_recc "writeToALoop"
             (expr_lambda ["k"]
              (expr_if
               (expr_op2 binary_op_lt (expr_id "k")
                (expr_id "actualDeleteCount"))
               (expr_let "from"
                (expr_app (expr_id "%ToString")
                 [expr_op2 binary_op_add (expr_id "actualStart")
                  (expr_id "k")])
                (expr_if
                 (expr_op2 binary_op_has_property (expr_id "O")
                  (expr_id "from"))
                 (expr_seq
                  (expr_let "fromValue"
                   (expr_get_field (expr_id "O") (expr_id "from"))
                   (expr_app (expr_id "%defineOwnProperty")
                    [expr_id "A";
                     expr_app (expr_id "%ToString") [expr_id "k"];
                     expr_object
                     (objattrs_intro (expr_string "Object") expr_true
                      expr_null expr_null expr_undefined)
                     [("value", property_data
                                (data_intro (expr_id "fromValue") expr_true
                                 expr_false expr_false));
                      ("writable", property_data
                                   (data_intro expr_true expr_true expr_false
                                    expr_false));
                      ("enumerable", property_data
                                     (data_intro expr_true expr_true
                                      expr_false expr_false));
                      ("configurable", property_data
                                       (data_intro expr_true expr_true
                                        expr_false expr_false))]]))
                  (expr_seq
                   (expr_let "$newVal"
                    (expr_op2 binary_op_add
                     (expr_get_field (expr_id "A") (expr_string "length"))
                     (expr_number (JsNumber.of_int 1)))
                    (expr_set_field (expr_id "A") (expr_string "length")
                     (expr_id "$newVal")))
                   (expr_app (expr_id "writeToALoop")
                    [expr_op2 binary_op_add (expr_id "k")
                     (expr_number (JsNumber.of_int 1))])))
                 (expr_app (expr_id "writeToALoop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int 1))]))) expr_undefined))
             (expr_app (expr_id "writeToALoop")
              [expr_number (JsNumber.of_int 0)]))
            (expr_let "itemCount"
             (expr_op2 binary_op_sub
              (expr_get_field (expr_id "args") (expr_string "length"))
              (expr_number (JsNumber.of_int 2)))
             (expr_seq
              (expr_let "step1"
               (expr_lambda []
                (expr_if
                 (expr_op2 binary_op_lt (expr_id "itemCount")
                  (expr_id "actualDeleteCount"))
                 (expr_seq
                  (expr_let "end"
                   (expr_op2 binary_op_sub (expr_id "len")
                    (expr_id "actualDeleteCount"))
                   (expr_recc "writeToOLoop"
                    (expr_lambda ["k"]
                     (expr_if
                      (expr_op2 binary_op_lt (expr_id "k") (expr_id "end"))
                      (expr_let "from"
                       (expr_app (expr_id "%ToString")
                        [expr_op2 binary_op_add (expr_id "k")
                         (expr_id "actualDeleteCount")])
                       (expr_let "to"
                        (expr_app (expr_id "%ToString")
                         [expr_op2 binary_op_add (expr_id "k")
                          (expr_id "itemCount")])
                        (expr_if
                         (expr_op2 binary_op_has_property (expr_id "O")
                          (expr_id "from"))
                         (expr_seq
                          (expr_let "$newVal"
                           (expr_get_field (expr_id "O") (expr_id "from"))
                           (expr_set_field (expr_id "O") (expr_id "to")
                            (expr_id "$newVal")))
                          (expr_app (expr_id "writeToOLoop")
                           [expr_op2 binary_op_add (expr_id "k")
                            (expr_number (JsNumber.of_int 1))]))
                         (expr_seq
                          (expr_delete_field (expr_id "O") (expr_id "to"))
                          (expr_app (expr_id "writeToOLoop")
                           [expr_op2 binary_op_add (expr_id "k")
                            (expr_number (JsNumber.of_int 1))])))))
                      expr_undefined))
                    (expr_app (expr_id "writeToOLoop")
                     [expr_id "actualStart"])))
                  (expr_let "delLimit"
                   (expr_op2 binary_op_add
                    (expr_op2 binary_op_sub (expr_id "len")
                     (expr_id "actualDeleteCount")) (expr_id "itemCount"))
                   (expr_recc "deleteloop"
                    (expr_lambda ["k"]
                     (expr_if
                      (expr_op2 binary_op_gt (expr_id "k")
                       (expr_id "delLimit"))
                      (expr_let "next"
                       (expr_op2 binary_op_sub (expr_id "k")
                        (expr_number (JsNumber.of_int 1)))
                       (expr_seq
                        (expr_delete_field (expr_id "O")
                         (expr_app (expr_id "%ToString") [expr_id "next"]))
                        (expr_app (expr_id "deleteloop") [expr_id "next"])))
                      expr_undefined))
                    (expr_app (expr_id "deleteloop") [expr_id "len"]))))
                 expr_null)) (expr_app (expr_id "step1") []))
              (expr_seq
               (expr_let "step2"
                (expr_lambda []
                 (expr_if
                  (expr_op2 binary_op_gt (expr_id "itemCount")
                   (expr_id "actualDeleteCount"))
                  (expr_recc "writeToOLoop"
                   (expr_lambda ["k"]
                    (expr_if
                     (expr_op2 binary_op_gt (expr_id "k")
                      (expr_id "actualStart"))
                     (expr_let "from"
                      (expr_app (expr_id "%ToString")
                       [expr_op2 binary_op_add (expr_id "k")
                        (expr_op2 binary_op_sub (expr_id "actualDeleteCount")
                         (expr_number (JsNumber.of_int 1)))])
                      (expr_let "to"
                       (expr_app (expr_id "%ToString")
                        [expr_op2 binary_op_add (expr_id "k")
                         (expr_op2 binary_op_sub (expr_id "itemCount")
                          (expr_number (JsNumber.of_int 1)))])
                       (expr_if
                        (expr_op2 binary_op_has_property (expr_id "O")
                         (expr_id "from"))
                        (expr_seq
                         (expr_let "$newVal"
                          (expr_get_field (expr_id "O") (expr_id "from"))
                          (expr_set_field (expr_id "O") (expr_id "to")
                           (expr_id "$newVal")))
                         (expr_app (expr_id "writeToOLoop")
                          [expr_op2 binary_op_sub (expr_id "k")
                           (expr_number (JsNumber.of_int 1))]))
                        (expr_seq
                         (expr_delete_field (expr_id "O") (expr_id "to"))
                         (expr_app (expr_id "writeToOLoop")
                          [expr_op2 binary_op_sub (expr_id "k")
                           (expr_number (JsNumber.of_int 1))])))))
                     expr_undefined))
                   (expr_app (expr_id "writeToOLoop")
                    [expr_op2 binary_op_sub (expr_id "len")
                     (expr_id "actualDeleteCount")])) expr_undefined))
                (expr_app (expr_id "step2") []))
               (expr_seq
                (expr_let "outerEnd"
                 (expr_get_field (expr_id "args") (expr_string "length"))
                 (expr_recc "outerloop"
                  (expr_lambda ["k"; "argsIndex"]
                   (expr_if
                    (expr_op2 binary_op_lt (expr_id "argsIndex")
                     (expr_id "outerEnd"))
                    (expr_seq
                     (expr_let "$newVal"
                      (expr_get_field (expr_id "args")
                       (expr_op1 unary_op_prim_to_str (expr_id "argsIndex")))
                      (expr_set_field (expr_id "O")
                       (expr_app (expr_id "%ToString") [expr_id "k"])
                       (expr_id "$newVal")))
                     (expr_app (expr_id "outerloop")
                      [expr_op2 binary_op_add (expr_id "k")
                       (expr_number (JsNumber.of_int 1));
                       expr_op2 binary_op_add (expr_id "argsIndex")
                       (expr_number (JsNumber.of_int 1))])) expr_undefined))
                  (expr_app (expr_id "outerloop")
                   [expr_id "actualStart"; expr_number (JsNumber.of_int 2)])))
                (expr_seq
                 (expr_let "$newVal"
                  (expr_op2 binary_op_add
                   (expr_op2 binary_op_sub (expr_id "len")
                    (expr_id "actualDeleteCount")) (expr_id "itemCount"))
                  (expr_set_field (expr_id "O") (expr_string "length")
                   (expr_id "$newVal"))) (expr_id "A"))))))))))))))))))
.
Definition privsplit :=  value_object 170 .
Definition privsplitLambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_string "String.prototype.split NYI"))
.
Definition privsqrt :=  value_object 287 .
Definition privsqrtLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "sqrt NYI"))
.
Definition privstrconcat :=  value_object 116 .
Definition privstrconcatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "end" (expr_get_field (expr_id "args") (expr_string "length"))
    (expr_recc "loop"
     (expr_lambda ["i"; "soFar"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
       (expr_let "next"
        (expr_app (expr_id "%ToString")
         [expr_get_field (expr_id "args")
          (expr_op1 unary_op_prim_to_str (expr_id "i"))])
        (expr_app (expr_id "loop")
         [expr_op2 binary_op_add (expr_id "i")
          (expr_number (JsNumber.of_int 1));
          expr_op2 binary_op_string_plus (expr_id "soFar") (expr_id "next")]))
       (expr_id "soFar")))
     (expr_app (expr_id "loop")
      [expr_number (JsNumber.of_int 0); expr_id "S"]))))))
.
Definition privstringSlice :=  value_object 167 .
Definition privstringSliceLambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
    (expr_let "intStart"
     (expr_app (expr_id "%ToInteger")
      [expr_get_field (expr_id "args") (expr_string "0")])
     (expr_let "end" (expr_get_field (expr_id "args") (expr_string "1"))
      (expr_let "intEnd"
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "end") expr_undefined)
        (expr_id "len") (expr_app (expr_id "%ToInteger") [expr_id "end"]))
       (expr_let "from"
        (expr_if
         (expr_op2 binary_op_lt (expr_id "intStart")
          (expr_number (JsNumber.of_int 0)))
         (expr_app (expr_id "%max")
          [expr_op2 binary_op_add (expr_id "len") (expr_id "intStart");
           expr_number (JsNumber.of_int 0)])
         (expr_app (expr_id "%min") [expr_id "intStart"; expr_id "len"]))
        (expr_let "to"
         (expr_if
          (expr_op2 binary_op_lt (expr_id "intEnd")
           (expr_number (JsNumber.of_int 0)))
          (expr_app (expr_id "%max")
           [expr_op2 binary_op_add (expr_id "len") (expr_id "intEnd");
            expr_number (JsNumber.of_int 0)])
          (expr_app (expr_id "%min") [expr_id "intEnd"; expr_id "len"]))
         (expr_let "span"
          (expr_app (expr_id "%max")
           [expr_op2 binary_op_sub (expr_id "to") (expr_id "from");
            expr_number (JsNumber.of_int 0)])
          (expr_recc "build"
           (expr_lambda ["i"; "result"]
            (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "span"))
             (expr_let "next"
              (expr_op2 binary_op_string_plus (expr_id "result")
               (expr_op2 binary_op_char_at (expr_id "S")
                (expr_op2 binary_op_add (expr_id "from") (expr_id "i"))))
              (expr_app (expr_id "build")
               [expr_op2 binary_op_add (expr_id "i")
                (expr_number (JsNumber.of_int 1));
                expr_id "next"])) (expr_id "result")))
           (expr_app (expr_id "build")
            [expr_number (JsNumber.of_int 0); expr_string ""]))))))))))))
.
Definition privstringToString :=  value_object 28 .
Definition privstringValueOf :=  value_object 299 .
Definition privsubstring :=  value_object 119 .
Definition privtan :=  value_object 289 .
Definition privtanLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "tan NYI"))
.
Definition privtest :=  value_object 253 .
Definition privtestlambda := 
value_closure
(closure_intro [] None ["this"; "args"]
 (expr_op1 unary_op_print
  (expr_string
   "You used the es5.env testlambda.  Are you sure you didn't forget to include the regexp.js library, or regexp.env?")))
.
Definition privthrowUnboundIDErrors :=  value_false .
Definition privtlclambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_op1 unary_op_to_lower (expr_id "S")))))
.
Definition privtoExponential :=  value_object 310 .
Definition privtoExponentialLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "toExponential NYI"))
.
Definition privtoFixed :=  value_object 305 .
Definition privtoFixedLambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_let "f"
  (expr_app (expr_id "%ToInteger")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_let "%or"
      (expr_op2 binary_op_lt (expr_id "f") (expr_number (JsNumber.of_int 0)))
      (expr_if (expr_id "%or") (expr_id "%or")
       (expr_op2 binary_op_gt (expr_id "f")
        (expr_number (JsNumber.of_int 20)))))
     (expr_throw
      (expr_app (expr_id "%JSError")
       [expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "%RangeErrorProto") expr_null expr_undefined) []]))
     expr_null)
    (expr_let "x"
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
       (expr_string "number")) (expr_id "this")
      (expr_get_obj_attr oattr_primval (expr_id "this")))
     (expr_seq
      (expr_if
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))
        expr_false expr_true) (expr_break "ret" (expr_string "NaN"))
       expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_ge (expr_id "x")
         (expr_number (JsNumber.of_int 0)))
        (expr_break "ret" (expr_app (expr_id "%ToString") [expr_id "x"]))
        expr_null)
       (expr_break "ret"
        (expr_op2 binary_op_to_fixed (expr_id "x") (expr_id "f"))))))))))
.
Definition privtoLocaleString :=  value_object 43 .
Definition privtoLowerCase :=  value_object 168 .
Definition privtoPrecision :=  value_object 312 .
Definition privtoPrecisionLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "toPrecision NYI"))
.
Definition privtoUpperCase :=  value_object 169 .
Definition privtuclambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"]
 (expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
  (expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
   (expr_op1 unary_op_to_upper (expr_id "S")))))
.
Definition privunescape :=  value_object 324 .
Definition privunescapeLambda := 
value_closure
(closure_intro [] None ["this"; "args"] (expr_string "unescape NYI"))
.
Definition privunshift :=  value_object 125 .
Definition privunshiftlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"]
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
   (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
    (expr_let "argCount"
     (expr_get_field (expr_id "args") (expr_string "length"))
     (expr_seq
      (expr_recc "Oloop"
       (expr_lambda ["k"]
        (expr_if
         (expr_op2 binary_op_gt (expr_id "k")
          (expr_number (JsNumber.of_int 0)))
         (expr_let "from"
          (expr_app (expr_id "%ToString")
           [expr_op2 binary_op_sub (expr_id "k")
            (expr_number (JsNumber.of_int 1))])
          (expr_let "to"
           (expr_app (expr_id "%ToString")
            [expr_op2 binary_op_add (expr_id "k")
             (expr_op2 binary_op_sub (expr_id "argCount")
              (expr_number (JsNumber.of_int 1)))])
           (expr_if
            (expr_op2 binary_op_has_property (expr_id "O") (expr_id "from"))
            (expr_seq
             (expr_let "$newVal"
              (expr_get_field (expr_id "O") (expr_id "from"))
              (expr_set_field (expr_id "O") (expr_id "to")
               (expr_id "$newVal")))
             (expr_app (expr_id "Oloop")
              [expr_op2 binary_op_sub (expr_id "k")
               (expr_number (JsNumber.of_int 1))]))
            (expr_seq (expr_delete_field (expr_id "O") (expr_id "to"))
             (expr_app (expr_id "Oloop")
              [expr_op2 binary_op_sub (expr_id "k")
               (expr_number (JsNumber.of_int 1))]))))) expr_undefined))
       (expr_app (expr_id "Oloop") [expr_id "len"]))
      (expr_seq
       (expr_let "end"
        (expr_get_field (expr_id "args") (expr_string "length"))
        (expr_recc "argsLoop"
         (expr_lambda ["argsIndex"; "j"]
          (expr_if
           (expr_op2 binary_op_lt (expr_id "argsIndex") (expr_id "end"))
           (expr_seq
            (expr_let "$newVal"
             (expr_get_field (expr_id "args")
              (expr_op1 unary_op_prim_to_str (expr_id "argsIndex")))
             (expr_set_field (expr_id "O")
              (expr_app (expr_id "%ToString") [expr_id "j"])
              (expr_id "$newVal")))
            (expr_app (expr_id "argsLoop")
             [expr_op2 binary_op_add (expr_id "argsIndex")
              (expr_number (JsNumber.of_int 1));
              expr_op2 binary_op_add (expr_id "j")
              (expr_number (JsNumber.of_int 1))])) expr_undefined))
         (expr_app (expr_id "argsLoop")
          [expr_number (JsNumber.of_int 0); expr_number (JsNumber.of_int 0)])))
       (expr_let "finalLen"
        (expr_op2 binary_op_add (expr_id "len") (expr_id "argCount"))
        (expr_seq
         (expr_let "$newVal" (expr_id "finalLen")
          (expr_set_field (expr_id "O") (expr_string "length")
           (expr_id "$newVal"))) (expr_id "finalLen"))))))))))
.
Definition privvalueOf :=  value_object 44 .
Definition privvalueOfLambda := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None
 ["this"; "args"; "proto"; "typestr"]
 (expr_let "hasWrongProto"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_obj_attr oattr_proto (expr_id "this")) (expr_id "proto"))
   expr_false expr_true)
  (expr_let "hasWrongTypeof"
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
     (expr_id "typestr")) expr_false expr_true)
   (expr_let "isntProto"
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") (expr_id "proto"))
     expr_false expr_true)
    (expr_if
     (expr_if
      (expr_if (expr_id "hasWrongProto") (expr_id "hasWrongTypeof")
       expr_false) (expr_id "isntProto") expr_false)
     (expr_app (expr_id "%TypeError") [expr_string "valueOf"])
     (expr_if (expr_id "hasWrongTypeof")
      (expr_get_obj_attr oattr_primval (expr_id "this")) (expr_id "this")))))))
.
Definition privvalueOflambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 (expr_app (expr_id "%ToObject") [expr_id "this"]))
.
Definition isAccessorField := 
value_closure
(closure_intro [] None ["obj"; "field"]
 (expr_let "%or"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_attr pattr_setter (expr_id "obj") (expr_id "field"))
    expr_undefined) expr_false expr_true)
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_attr pattr_getter (expr_id "obj") (expr_id "field"))
     expr_undefined) expr_false expr_true))))
.
Definition isDataField := 
value_closure
(closure_intro [] None ["obj"; "field"]
 (expr_let "%or"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_attr pattr_value (expr_id "obj") (expr_id "field"))
    expr_undefined) expr_false expr_true)
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_attr pattr_writable (expr_id "obj") (expr_id "field"))
     expr_undefined) expr_false expr_true))))
.
Definition isGenericDescriptor := 
value_closure
(closure_intro
 [("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["attr-obj"]
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "isAccessorDescriptor") [expr_id "attr-obj"])
   expr_false)
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"]) expr_false)
  expr_false))
.
Definition isGenericField := 
value_closure
(closure_intro
 [("isAccessorField", isAccessorField); ("isDataField", isDataField)] 
 None ["obj"; "field"]
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "isDataField") [expr_id "obj"; expr_id "field"])
   expr_false)
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "isAccessorField") [expr_id "obj"; expr_id "field"])
   expr_false) expr_false))
.
Definition objCode1 := 
value_closure (closure_intro [] None ["this"; "args"] expr_undefined)
.
Definition objCode2 := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto)] None ["this"; "args"]
 (expr_throw
  (expr_app (expr_id "%JSError")
   [expr_object
    (objattrs_intro (expr_string "Object") expr_true
     (expr_id "%ReferenceErrorProto") expr_null expr_undefined) []])))
.
Definition objCode3 := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%SyntaxErrorProto", privSyntaxErrorProto)]
 None ["this"; "args"]
 (expr_throw
  (expr_app (expr_id "%JSError")
   [expr_object
    (objattrs_intro (expr_string "Object") expr_true
     (expr_id "%SyntaxErrorProto") expr_null expr_undefined) []])))
.
Definition name :=  value_string "parse" .
Definition objCode4 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name1 :=  value_string "UTC" .
Definition objCode5 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name1)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name2 :=  value_string "getTime" .
Definition objCode6 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name2)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name3 :=  value_string "getFullYear" .
Definition objCode7 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name3)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name4 :=  value_string "getUTCFullYear" .
Definition objCode8 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name4)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name5 :=  value_string "getUTCMonth" .
Definition objCode9 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name5)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name6 :=  value_string "getUTCDate" .
Definition objCode10 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name6)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name7 :=  value_string "getUTCDay" .
Definition objCode11 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name7)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name8 :=  value_string "getHours" .
Definition objCode12 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name8)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name9 :=  value_string "getUTCHours" .
Definition objCode13 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name9)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name10 :=  value_string "getMinutes" .
Definition objCode14 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name10)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name11 :=  value_string "getUTCMinutes" .
Definition objCode15 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name11)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name12 :=  value_string "getSeconds" .
Definition objCode16 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name12)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name13 :=  value_string "getUTCSeconds" .
Definition objCode17 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name13)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name14 :=  value_string "getMilliseconds" .
Definition objCode18 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name14)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name15 :=  value_string "getUTCMilliseconds" .
Definition objCode19 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name15)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name16 :=  value_string "setTime" .
Definition objCode20 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name16)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name17 :=  value_string "setMilliseconds" .
Definition objCode21 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name17)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name18 :=  value_string "setUTCMilliseconds" .
Definition objCode22 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name18)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name19 :=  value_string "setSeconds" .
Definition objCode23 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name19)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name20 :=  value_string "setUTCSeconds" .
Definition objCode24 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name20)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name21 :=  value_string "setMinutes" .
Definition objCode25 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name21)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name22 :=  value_string "setUTCMinutes" .
Definition objCode26 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name22)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name23 :=  value_string "setHours" .
Definition objCode27 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name23)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name24 :=  value_string "setUTCHours" .
Definition objCode28 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name24)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name25 :=  value_string "setDate" .
Definition objCode29 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name25)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name26 :=  value_string "setUTCDate" .
Definition objCode30 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name26)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name27 :=  value_string "setMonth" .
Definition objCode31 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name27)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name28 :=  value_string "setUTCMonth" .
Definition objCode32 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name28)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name29 :=  value_string "setFullYear" .
Definition objCode33 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name29)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name30 :=  value_string "setUTCFullYear" .
Definition objCode34 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name30)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name31 :=  value_string "toUTCString" .
Definition objCode35 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name31)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name32 :=  value_string "toGMTString" .
Definition objCode36 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name32)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition name33 :=  value_string "setYear" .
Definition objCode37 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name33)] None
 ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
.
Definition objCode38 := 
value_closure
(closure_intro
 [("%StringProto", privStringProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"]
 (expr_app (expr_id "%valueOfLambda")
  [expr_id "this";
   expr_id "args";
   expr_id "%StringProto";
   expr_string "string"]))
.
Definition objCode39 := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"]
 (expr_app (expr_id "%valueOfLambda")
  [expr_id "this";
   expr_id "args";
   expr_id "%NumberProto";
   expr_string "number"]))
.
Definition objCode40 := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"]
 (expr_app (expr_id "%valueOfLambda")
  [expr_id "this";
   expr_id "args";
   expr_id "%BooleanProto";
   expr_string "boolean"]))
.
Definition ctx_items := 
[("%AppExprCheck", privAppExprCheck);
 ("%ArrayConstructor", privArrayConstructor);
 ("%ArrayGlobalFuncObj", privArrayGlobalFuncObj);
 ("%ArrayLengthChange", privArrayLengthChange);
 ("%ArrayProto", privArrayProto);
 ("%BitwiseAnd", privBitwiseAnd);
 ("%BitwiseInfix", privBitwiseInfix);
 ("%BitwiseNot", privBitwiseNot);
 ("%BooleanConstructor", privBooleanConstructor);
 ("%BooleanGlobalFuncObj", privBooleanGlobalFuncObj);
 ("%BooleanProto", privBooleanProto);
 ("%CheckObjectCoercible", privCheckObjectCoercible);
 ("%CompareOp", privCompareOp);
 ("%DateConstructor", privDateConstructor);
 ("%DateFromTime", privDateFromTime);
 ("%DateGlobalFuncObj", privDateGlobalFuncObj);
 ("%DateProto", privDateProto);
 ("%Day", privDay);
 ("%DayFromYear", privDayFromYear);
 ("%DayWithinYear", privDayWithinYear);
 ("%DaysInMonth", privDaysInMonth);
 ("%DaysInYear", privDaysInYear);
 ("%EnvCheckAssign", privEnvCheckAssign);
 ("%EnvGet", privEnvGet);
 ("%EqEq", privEqEq);
 ("%ErrorConstructor", privErrorConstructor);
 ("%ErrorDispatch", privErrorDispatch);
 ("%ErrorGlobalFuncObj", privErrorGlobalFuncObj);
 ("%ErrorProto", privErrorProto);
 ("%EvalErrorConstructor", privEvalErrorConstructor);
 ("%EvalErrorGlobalFuncObj", privEvalErrorGlobalFuncObj);
 ("%EvalErrorProto", proto);
 ("%FunctionConstructor", privFunctionConstructor);
 ("%FunctionGlobalFuncObj", privFunctionGlobalFuncObj);
 ("%FunctionProto", privFunctionProto);
 ("%GetterValue", privGetterValue);
 ("%GreaterEqual", privGreaterEqual);
 ("%GreaterThan", privGreaterThan);
 ("%Immut", privImmut);
 ("%InLeapYear", privInLeapYear);
 ("%IsFinite", privIsFinite);
 ("%IsJSError", privIsJSError);
 ("%IsObject", privIsObject);
 ("%IsPrototypeOflambda", privIsPrototypeOflambda);
 ("%JSError", privJSError);
 ("%LeftShift", privLeftShift);
 ("%LessEqual", privLessEqual);
 ("%LessThan", privLessThan);
 ("%LocalTime", privUTC);
 ("%MakeDate", privMakeDate);
 ("%MakeDay", privMakeDay);
 ("%MakeGetter", privMakeGetter);
 ("%MakeSetter", privMakeSetter);
 ("%MakeTime", privMakeTime);
 ("%MakeTypeError", privMakeTypeError);
 ("%Math", privMath);
 ("%MonthFromTime", privMonthFromTime);
 ("%NativeErrorConstructor", privNativeErrorConstructor);
 ("%NumberConstructor", privNumberConstructor);
 ("%NumberGlobalFuncObj", privNumberGlobalFuncObj);
 ("%NumberProto", privNumberProto);
 ("%ObjectConstructor", privObjectConstructor);
 ("%ObjectGlobalFuncObj", privObjectGlobalFuncObj);
 ("%ObjectProto", privObjectProto);
 ("%ObjectTypeCheck", privObjectTypeCheck);
 ("%PostDecrement", privPostDecrement);
 ("%PostIncrement", privPostIncrement);
 ("%PostfixOp", privPostfixOp);
 ("%PrefixDecrement", privPrefixDecrement);
 ("%PrefixIncrement", privPrefixIncrement);
 ("%PrefixOp", privPrefixOp);
 ("%PrimAdd", privPrimAdd);
 ("%PrimMultOp", privPrimMultOp);
 ("%PrimNew", privPrimNew);
 ("%PrimSub", privPrimSub);
 ("%PropAccessorCheck", privPropAccessorCheck);
 ("%RangeErrorConstructor", privRangeErrorConstructor);
 ("%RangeErrorGlobalFuncObj", privRangeErrorGlobalFuncObj);
 ("%RangeErrorProto", privRangeErrorProto);
 ("%ReferenceErrorConstructor", privReferenceErrorConstructor);
 ("%ReferenceErrorGlobalFuncObj", privReferenceErrorGlobalFuncObj);
 ("%ReferenceErrorProto", privReferenceErrorProto);
 ("%RegExpConstructor", privRegExpConstructor);
 ("%RegExpGlobalFuncObj", privRegExpGlobalFuncObj);
 ("%RegExpProto", privRegExpProto);
 ("%SetterValue", privGetterValue);
 ("%SignedRightShift", privSignedRightShift);
 ("%StringConstructor", privStringConstructor);
 ("%StringGlobalFuncObj", privStringGlobalFuncObj);
 ("%StringIndexOf", privStringIndexOf);
 ("%StringIndexOflambda", privStringIndexOflambda);
 ("%StringIndices", privStringIndices);
 ("%StringLastIndexOf", privStringLastIndexOf);
 ("%StringProto", privStringProto);
 ("%SyntaxError", privSyntaxError);
 ("%SyntaxErrorConstructor", privSyntaxErrorConstructor);
 ("%SyntaxErrorGlobalFuncObj", privSyntaxErrorGlobalFuncObj);
 ("%SyntaxErrorProto", privSyntaxErrorProto);
 ("%ThrowReferenceError", privThrowReferenceError);
 ("%ThrowSyntaxError", privThrowSyntaxError);
 ("%ThrowTypeError", privThrowTypeError);
 ("%ThrowTypeErrorFun", privThrowTypeErrorFun);
 ("%TimeClip", privTimeClip);
 ("%TimeFromYear", privTimeFromYear);
 ("%TimeWithinDay", privTimeWithinDay);
 ("%ToBoolean", privToBoolean);
 ("%ToInt32", privToInt32);
 ("%ToInteger", privToInteger);
 ("%ToJSError", privToJSError);
 ("%ToNumber", privToNumber);
 ("%ToObject", privToObject);
 ("%ToPrimitive", privToPrimitive);
 ("%ToPrimitiveHint", privToPrimitiveHint);
 ("%ToPrimitiveNum", privToPrimitiveNum);
 ("%ToPrimitiveStr", privToPrimitiveStr);
 ("%ToString", privToString);
 ("%ToUint", privToUint);
 ("%ToUint16", privToUint16);
 ("%ToUint32", privToUint32);
 ("%TypeError", privTypeError);
 ("%TypeErrorConstructor", privTypeErrorConstructor);
 ("%TypeErrorGlobalFuncObj", privTypeErrorGlobalFuncObj);
 ("%TypeErrorProto", privTypeErrorProto);
 ("%Typeof", privTypeof);
 ("%URIErrorConstructor", privURIErrorConstructor);
 ("%URIErrorGlobalFuncObj", privURIErrorGlobalFuncObj);
 ("%URIErrorProto", proto1);
 ("%UTC", privUTC);
 ("%UnaryNeg", privUnaryNeg);
 ("%UnaryPlus", privUnaryPlus);
 ("%UnboundId", privUnboundId);
 ("%UnsignedRightShift", privUnsignedRightShift);
 ("%UnwritableDispatch", privUnwritableDispatch);
 ("%YearFromTime", privYearFromTime);
 ("%acos", privacos);
 ("%acosLambda", privacosLambda);
 ("%aiolambda", privaiolambda);
 ("%aliolambda", privaliolambda);
 ("%apply", privapply);
 ("%applylambda", privapplylambda);
 ("%arrayIndexOf", privarrayIndexOf);
 ("%arrayLastIndexOf", privarrayLastIndexOf);
 ("%arrayTLSlambda", privarrayTLSlambda);
 ("%arrayToLocaleString", privarrayToLocaleString);
 ("%arrayToString", privarrayToString);
 ("%arrayToStringlambda", privarrayToStringlambda);
 ("%asin", privasin);
 ("%asinLambda", privasinLambda);
 ("%atan", privatan);
 ("%atan2", privatan2);
 ("%atan2Lambda", privatan2Lambda);
 ("%atanLambda", privatanLambda);
 ("%bind", privbind);
 ("%bindLambda", privbindLambda);
 ("%booleanToString", privbooleanToString);
 ("%booleanToStringlambda", privbooleanToStringlambda);
 ("%booleanValueOf", privbooleanValueOf);
 ("%call", privcall);
 ("%calllambda", privcalllambda);
 ("%charat", privcharat);
 ("%charatlambda", privcharatlambda);
 ("%charcodeat", privcharcodeat);
 ("%charcodeatlambda", privcharcodeatlambda);
 ("%concat", privconcat);
 ("%concatLambda", privconcatLambda);
 ("%configurableEval", privconfigurableEval);
 ("%console", privconsole);
 ("%cos", privcos);
 ("%cosLambda", privcosLambda);
 ("%create", privcreate);
 ("%createLambda", privcreateLambda);
 ("%dateGetTimezoneOffset", privdateGetTimezoneOffset);
 ("%dateGetTimezoneOffsetLambda", privdateGetTimezoneOffsetLambda);
 ("%dateToString", privdateToString);
 ("%dateToStringLambda", privdateToStringLambda);
 ("%dateValueOf", privdateValueOf);
 ("%dateValueOfLambda", privdateValueOfLambda);
 ("%dategetDate", privdategetDate);
 ("%dategetDateLambda", privdategetDateLambda);
 ("%dategetDay", privdategetDay);
 ("%dategetDayLambda", privdategetDayLambda);
 ("%decodeURI", privdecodeURI);
 ("%decodeURIComponent", privdecodeURIComponent);
 ("%decodeURIComponentLambda", privdecodeURIComponentLambda);
 ("%decodeURILambda", privdecodeURILambda);
 ("%define15Property", privdefine15Property);
 ("%defineGlobalAccessors", privdefineGlobalAccessors);
 ("%defineGlobalVar", privdefineGlobalVar);
 ("%defineNYIProperty", privdefineNYIProperty);
 ("%defineOwnProperty", privdefineOwnProperty);
 ("%defineProperties", privdefineProperties);
 ("%definePropertiesLambda", privdefinePropertiesLambda);
 ("%defineProperty", privdefineProperty);
 ("%definePropertylambda", privdefinePropertylambda);
 ("%encodeURI", privencodeURI);
 ("%encodeURIComponent", privencodeURIComponent);
 ("%encodeURIComponentLambda", privencodeURIComponentLambda);
 ("%encodeURILambda", privencodeURILambda);
 ("%escape", privescape);
 ("%escapeLambda", privescapeLambda);
 ("%ets", privets);
 ("%etslambda", privetslambda);
 ("%eval", priveval);
 ("%evallambda", privevallambda);
 ("%every", privevery);
 ("%everylambda", priveverylambda);
 ("%exp", privexp);
 ("%explambda", privexplambda);
 ("%filter", privfilter);
 ("%filterlambda", privfilterlambda);
 ("%foreach", privforeach);
 ("%foreachlambda", privforeachlambda);
 ("%freeze", privfreeze);
 ("%freezelambda", privfreezelambda);
 ("%fromCharCode", privfromCharCode);
 ("%fromcclambda", privfromcclambda);
 ("%functionToString", privfunctionToString);
 ("%functionToStringlambda", privfunctionToStringlambda);
 ("%getCurrentUTC", privgetCurrentUTC);
 ("%getMonth", privgetMonth);
 ("%getMonthlambda", privgetMonthlambda);
 ("%getYear", privgetYear);
 ("%getYearlambda", privgetYearlambda);
 ("%global", privglobal);
 ("%globalContext", privglobalContext);
 ("%gopd", privgopd);
 ("%gopdLambda", privgopdLambda);
 ("%gopn", privgopn);
 ("%gopnLambda", privgopnLambda);
 ("%gpo", privgpo);
 ("%gpoLambda", privgpoLambda);
 ("%hasOwnProperty", privhasOwnProperty);
 ("%hasOwnPropertylambda", privhasOwnPropertylambda);
 ("%in", privin);
 ("%instanceof", privinstanceof);
 ("%isExtensible", privisExtensible);
 ("%isExtensibleLambda", privisExtensibleLambda);
 ("%isFinite", privisFinite);
 ("%isFiniteLambda", privisFiniteLambda);
 ("%isFrozen", privisFrozen);
 ("%isFrozenLambda", privisFrozenLambda);
 ("%isNaN", privisNaN);
 ("%isNaNlambda", privisNaNlambda);
 ("%isPrototypeOf", privisPrototypeOf);
 ("%isSealed", privisSealed);
 ("%isSealedLambda", privisSealedLambda);
 ("%isUnbound", privisUnbound);
 ("%join", privjoin);
 ("%joinlambda", privjoinlambda);
 ("%keys", privkeys);
 ("%keysLambda", privkeysLambda);
 ("%len", privlen);
 ("%localeCompare", privlocaleCompare);
 ("%localeCompareLambda", privlocaleCompareLambda);
 ("%log", privlog);
 ("%logLambda", privlogLambda);
 ("%makeContextVarDefiner", privmakeContextVarDefiner);
 ("%makeEnvGetter", privmakeEnvGetter);
 ("%makeEnvSetter", privmakeEnvSetter);
 ("%makeGlobalEnv", privmakeGlobalEnv);
 ("%makeWithContext", privmakeWithContext);
 ("%map", privmap);
 ("%maplambda", privmaplambda);
 ("%mathAbs", privmathAbs);
 ("%mathAbsLambda", privmathAbsLambda);
 ("%mathCeil", privmathCeil);
 ("%mathCeilLambda", privmathCeilLambda);
 ("%mathFloor", privmathFloor);
 ("%mathFloorLambda", privmathFloorLambda);
 ("%mathLog", privmathLog);
 ("%mathLogLambda", privmathLogLambda);
 ("%mathMax", privmathMax);
 ("%mathMaxLambda", privmathMaxLambda);
 ("%mathMin", privmathMin);
 ("%mathMinLambda", privmathMinLambda);
 ("%mathPow", privmathPow);
 ("%mathPowLambda", privmathPowLambda);
 ("%max", privmax);
 ("%maybeDirectEval", privmaybeDirectEval);
 ("%min", privmin);
 ("%minMaxLambda", privminMaxLambda);
 ("%mkArgsObj", privmkArgsObj);
 ("%mkArgsObjBase", privmkArgsObjBase);
 ("%mkNewArgsObj", privmkNewArgsObj);
 ("%msPerDay", privmsPerDay);
 ("%msPerHour", privmsPerHour);
 ("%msPerMin", privmsPerMin);
 ("%msPerSecond", privmsPerSecond);
 ("%nonstrictContext", privglobalContext);
 ("%numTLS", privnumTLS);
 ("%numTLSLambda", privnumTLSLambda);
 ("%numToStringAbstract", privnumToStringAbstract);
 ("%numValueOf", privnumValueOf);
 ("%numberToString", privnumberToString);
 ("%numberToStringlambda", privnumberToStringlambda);
 ("%objectToString", privobjectToString);
 ("%objectToStringlambda", privobjectToStringlambda);
 ("%oneArgObj", privoneArgObj);
 ("%parse", privparse);
 ("%parseFloat", privparseFloat);
 ("%parseFloatLambda", privparseFloatLambda);
 ("%parseInt", privparseInt);
 ("%parseIntlambda", privparseIntlambda);
 ("%pop", privpop);
 ("%poplambda", privpoplambda);
 ("%preventExtensions", privpreventExtensions);
 ("%preventExtensionsLambda", privpreventExtensionsLambda);
 ("%primEach", privprimEach);
 ("%print", privprint);
 ("%printlambda", privprintlambda);
 ("%propEnumlambda", privpropEnumlambda);
 ("%propertyIsEnumerable", privpropertyIsEnumerable);
 ("%propertyNames", privpropertyNames);
 ("%protoOfField", privprotoOfField);
 ("%push", privpush);
 ("%pushlambda", privpushlambda);
 ("%random", privrandom);
 ("%randomLambda", privrandomLambda);
 ("%reduce", privreduce);
 ("%reduceRight", privreduceRight);
 ("%reduceRightLambda", privreduceRightLambda);
 ("%reducelambda", privreducelambda);
 ("%replace", privreplace);
 ("%replacelambda", privreplacelambda);
 ("%resolveThis", privresolveThis);
 ("%reverse", privreverse);
 ("%reverselambda", privreverselambda);
 ("%round", privround);
 ("%roundLambda", privroundLambda);
 ("%seal", privseal);
 ("%sealLambda", privsealLambda);
 ("%set-property", privset_property);
 ("%shift", privshift);
 ("%shiftlambda", privshiftlambda);
 ("%sin", privsin);
 ("%sinLambda", privsinLambda);
 ("%slice", privslice);
 ("%slice_internal", privslice_internal);
 ("%slicelambda", privslicelambda);
 ("%sliolambda", privsliolambda);
 ("%some", privsome);
 ("%somelambda", privsomelambda);
 ("%sort", privsort);
 ("%sortlambda", privsortlambda);
 ("%splice", privsplice);
 ("%splicelambda", privsplicelambda);
 ("%split", privsplit);
 ("%splitLambda", privsplitLambda);
 ("%sqrt", privsqrt);
 ("%sqrtLambda", privsqrtLambda);
 ("%strconcat", privstrconcat);
 ("%strconcatlambda", privstrconcatlambda);
 ("%strictContext", privglobalContext);
 ("%stringSlice", privstringSlice);
 ("%stringSliceLambda", privstringSliceLambda);
 ("%stringToString", privstringToString);
 ("%stringToStringlambda", privdateValueOfLambda);
 ("%stringValueOf", privstringValueOf);
 ("%substring", privsubstring);
 ("%substringlambda", privsubstringlambda);
 ("%tan", privtan);
 ("%tanLambda", privtanLambda);
 ("%test", privtest);
 ("%testlambda", privtestlambda);
 ("%this", privglobal);
 ("%throwUnboundIDErrors", privthrowUnboundIDErrors);
 ("%tlclambda", privtlclambda);
 ("%toExponential", privtoExponential);
 ("%toExponentialLambda", privtoExponentialLambda);
 ("%toFixed", privtoFixed);
 ("%toFixedLambda", privtoFixedLambda);
 ("%toLocaleString", privtoLocaleString);
 ("%toLocaleStringlambda", privtoLocaleStringlambda);
 ("%toLowerCase", privtoLowerCase);
 ("%toPrecision", privtoPrecision);
 ("%toPrecisionLambda", privtoPrecisionLambda);
 ("%toUpperCase", privtoUpperCase);
 ("%tuclambda", privtuclambda);
 ("%twoArgObj", privtwoArgObj);
 ("%unescape", privunescape);
 ("%unescapeLambda", privunescapeLambda);
 ("%unshift", privunshift);
 ("%unshiftlambda", privunshiftlambda);
 ("%valueOf", privvalueOf);
 ("%valueOfLambda", privvalueOfLambda);
 ("%valueOflambda", privvalueOflambda);
 ("copy-access-desc", copy_access_desc);
 ("copy-data-desc", copy_data_desc);
 ("copy-when-defined", copy_when_defined);
 ("isAccessorDescriptor", isAccessorDescriptor);
 ("isAccessorField", isAccessorField);
 ("isDataDescriptor", isDataDescriptor);
 ("isDataField", isDataField);
 ("isGenericDescriptor", isGenericDescriptor);
 ("isGenericField", isGenericField)]
.
Definition store_items := [
(1, {|object_attrs :=
      {|oattrs_proto := value_null;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      Heap.of_list [("make", 
                     attributes_accessor_of {|attributes_accessor_get :=
                                              value_closure
                                              (closure_intro
                                               [("%AppExprCheck", privAppExprCheck);
                                                ("%ArrayConstructor", privArrayConstructor);
                                                ("%ArrayGlobalFuncObj", privArrayGlobalFuncObj);
                                                ("%ArrayLengthChange", privArrayLengthChange);
                                                ("%ArrayProto", privArrayProto);
                                                ("%BitwiseAnd", privBitwiseAnd);
                                                ("%BitwiseInfix", privBitwiseInfix);
                                                ("%BitwiseNot", privBitwiseNot);
                                                ("%BooleanConstructor", privBooleanConstructor);
                                                ("%BooleanGlobalFuncObj", privBooleanGlobalFuncObj);
                                                ("%BooleanProto", privBooleanProto);
                                                ("%CheckObjectCoercible", privCheckObjectCoercible);
                                                ("%CompareOp", privCompareOp);
                                                ("%DateConstructor", privDateConstructor);
                                                ("%DateFromTime", privDateFromTime);
                                                ("%DateGlobalFuncObj", privDateGlobalFuncObj);
                                                ("%DateProto", privDateProto);
                                                ("%Day", privDay);
                                                ("%DayFromYear", privDayFromYear);
                                                ("%DayWithinYear", privDayWithinYear);
                                                ("%DaysInMonth", privDaysInMonth);
                                                ("%DaysInYear", privDaysInYear);
                                                ("%EnvCheckAssign", privEnvCheckAssign);
                                                ("%EnvGet", privEnvGet);
                                                ("%EqEq", privEqEq);
                                                ("%ErrorConstructor", privErrorConstructor);
                                                ("%ErrorDispatch", privErrorDispatch);
                                                ("%ErrorGlobalFuncObj", privErrorGlobalFuncObj);
                                                ("%ErrorProto", privErrorProto);
                                                ("%EvalErrorConstructor", privEvalErrorConstructor);
                                                ("%EvalErrorGlobalFuncObj", privEvalErrorGlobalFuncObj);
                                                ("%EvalErrorProto", proto);
                                                ("%FunctionConstructor", privFunctionConstructor);
                                                ("%FunctionGlobalFuncObj", privFunctionGlobalFuncObj);
                                                ("%FunctionProto", privFunctionProto);
                                                ("%GetterValue", privGetterValue);
                                                ("%GreaterEqual", privGreaterEqual);
                                                ("%GreaterThan", privGreaterThan);
                                                ("%Immut", privImmut);
                                                ("%InLeapYear", privInLeapYear);
                                                ("%IsFinite", privIsFinite);
                                                ("%IsJSError", privIsJSError);
                                                ("%IsObject", privIsObject);
                                                ("%IsPrototypeOflambda", privIsPrototypeOflambda);
                                                ("%JSError", privJSError);
                                                ("%LeftShift", privLeftShift);
                                                ("%LessEqual", privLessEqual);
                                                ("%LessThan", privLessThan);
                                                ("%LocalTime", privUTC);
                                                ("%MakeDate", privMakeDate);
                                                ("%MakeDay", privMakeDay);
                                                ("%MakeGetter", privMakeGetter);
                                                ("%MakeSetter", privMakeSetter);
                                                ("%MakeTime", privMakeTime);
                                                ("%MakeTypeError", privMakeTypeError);
                                                ("%Math", privMath);
                                                ("%MonthFromTime", privMonthFromTime);
                                                ("%NativeErrorConstructor", privNativeErrorConstructor);
                                                ("%NumberConstructor", privNumberConstructor);
                                                ("%NumberGlobalFuncObj", privNumberGlobalFuncObj);
                                                ("%NumberProto", privNumberProto);
                                                ("%ObjectConstructor", privObjectConstructor);
                                                ("%ObjectGlobalFuncObj", privObjectGlobalFuncObj);
                                                ("%ObjectProto", privObjectProto);
                                                ("%ObjectTypeCheck", privObjectTypeCheck);
                                                ("%PostDecrement", privPostDecrement);
                                                ("%PostIncrement", privPostIncrement);
                                                ("%PostfixOp", privPostfixOp);
                                                ("%PrefixDecrement", privPrefixDecrement);
                                                ("%PrefixIncrement", privPrefixIncrement);
                                                ("%PrefixOp", privPrefixOp);
                                                ("%PrimAdd", privPrimAdd);
                                                ("%PrimMultOp", privPrimMultOp);
                                                ("%PrimNew", privPrimNew);
                                                ("%PrimSub", privPrimSub);
                                                ("%PropAccessorCheck", privPropAccessorCheck);
                                                ("%RangeErrorConstructor", privRangeErrorConstructor);
                                                ("%RangeErrorGlobalFuncObj", privRangeErrorGlobalFuncObj);
                                                ("%RangeErrorProto", privRangeErrorProto);
                                                ("%ReferenceErrorConstructor", privReferenceErrorConstructor);
                                                ("%ReferenceErrorGlobalFuncObj", privReferenceErrorGlobalFuncObj);
                                                ("%ReferenceErrorProto", privReferenceErrorProto);
                                                ("%RegExpConstructor", privRegExpConstructor);
                                                ("%RegExpGlobalFuncObj", privRegExpGlobalFuncObj);
                                                ("%RegExpProto", privRegExpProto);
                                                ("%SetterValue", privGetterValue);
                                                ("%SignedRightShift", privSignedRightShift);
                                                ("%StringConstructor", privStringConstructor);
                                                ("%StringGlobalFuncObj", privStringGlobalFuncObj);
                                                ("%StringIndexOf", privStringIndexOf);
                                                ("%StringIndexOflambda", privStringIndexOflambda);
                                                ("%StringIndices", privStringIndices);
                                                ("%StringLastIndexOf", privStringLastIndexOf);
                                                ("%StringProto", privStringProto);
                                                ("%SyntaxError", privSyntaxError);
                                                ("%SyntaxErrorConstructor", privSyntaxErrorConstructor);
                                                ("%SyntaxErrorGlobalFuncObj", privSyntaxErrorGlobalFuncObj);
                                                ("%SyntaxErrorProto", privSyntaxErrorProto);
                                                ("%ThrowReferenceError", privThrowReferenceError);
                                                ("%ThrowSyntaxError", privThrowSyntaxError);
                                                ("%ThrowTypeError", privThrowTypeError);
                                                ("%ThrowTypeErrorFun", privThrowTypeErrorFun);
                                                ("%TimeClip", privTimeClip);
                                                ("%TimeFromYear", privTimeFromYear);
                                                ("%TimeWithinDay", privTimeWithinDay);
                                                ("%ToBoolean", privToBoolean);
                                                ("%ToInt32", privToInt32);
                                                ("%ToInteger", privToInteger);
                                                ("%ToJSError", privToJSError);
                                                ("%ToNumber", privToNumber);
                                                ("%ToObject", privToObject);
                                                ("%ToPrimitive", privToPrimitive);
                                                ("%ToPrimitiveHint", privToPrimitiveHint);
                                                ("%ToPrimitiveNum", privToPrimitiveNum);
                                                ("%ToPrimitiveStr", privToPrimitiveStr);
                                                ("%ToString", privToString);
                                                ("%ToUint", privToUint);
                                                ("%ToUint16", privToUint16);
                                                ("%ToUint32", privToUint32);
                                                ("%TypeError", privTypeError);
                                                ("%TypeErrorConstructor", privTypeErrorConstructor);
                                                ("%TypeErrorGlobalFuncObj", privTypeErrorGlobalFuncObj);
                                                ("%TypeErrorProto", privTypeErrorProto);
                                                ("%Typeof", privTypeof);
                                                ("%URIErrorConstructor", privURIErrorConstructor);
                                                ("%URIErrorGlobalFuncObj", privURIErrorGlobalFuncObj);
                                                ("%URIErrorProto", proto1);
                                                ("%UTC", privUTC);
                                                ("%UnaryNeg", privUnaryNeg);
                                                ("%UnaryPlus", privUnaryPlus);
                                                ("%UnboundId", privUnboundId);
                                                ("%UnsignedRightShift", privUnsignedRightShift);
                                                ("%UnwritableDispatch", privUnwritableDispatch);
                                                ("%YearFromTime", privYearFromTime);
                                                ("%acos", privacos);
                                                ("%acosLambda", privacosLambda);
                                                ("%aiolambda", privaiolambda);
                                                ("%aliolambda", privaliolambda);
                                                ("%apply", privapply);
                                                ("%applylambda", privapplylambda);
                                                ("%arrayIndexOf", privarrayIndexOf);
                                                ("%arrayLastIndexOf", privarrayLastIndexOf);
                                                ("%arrayTLSlambda", privarrayTLSlambda);
                                                ("%arrayToLocaleString", privarrayToLocaleString);
                                                ("%arrayToString", privarrayToString);
                                                ("%arrayToStringlambda", privarrayToStringlambda);
                                                ("%asin", privasin);
                                                ("%asinLambda", privasinLambda);
                                                ("%atan", privatan);
                                                ("%atan2", privatan2);
                                                ("%atan2Lambda", privatan2Lambda);
                                                ("%atanLambda", privatanLambda);
                                                ("%bind", privbind);
                                                ("%bindLambda", privbindLambda);
                                                ("%booleanToString", privbooleanToString);
                                                ("%booleanToStringlambda", privbooleanToStringlambda);
                                                ("%booleanValueOf", privbooleanValueOf);
                                                ("%call", privcall);
                                                ("%calllambda", privcalllambda);
                                                ("%charat", privcharat);
                                                ("%charatlambda", privcharatlambda);
                                                ("%charcodeat", privcharcodeat);
                                                ("%charcodeatlambda", privcharcodeatlambda);
                                                ("%concat", privconcat);
                                                ("%concatLambda", privconcatLambda);
                                                ("%configurableEval", privconfigurableEval);
                                                ("%console", privconsole);
                                                ("%cos", privcos);
                                                ("%cosLambda", privcosLambda);
                                                ("%create", privcreate);
                                                ("%createLambda", privcreateLambda);
                                                ("%dateGetTimezoneOffset", privdateGetTimezoneOffset);
                                                ("%dateGetTimezoneOffsetLambda", privdateGetTimezoneOffsetLambda);
                                                ("%dateToString", privdateToString);
                                                ("%dateToStringLambda", privdateToStringLambda);
                                                ("%dateValueOf", privdateValueOf);
                                                ("%dateValueOfLambda", privdateValueOfLambda);
                                                ("%dategetDate", privdategetDate);
                                                ("%dategetDateLambda", privdategetDateLambda);
                                                ("%dategetDay", privdategetDay);
                                                ("%dategetDayLambda", privdategetDayLambda);
                                                ("%decodeURI", privdecodeURI);
                                                ("%decodeURIComponent", privdecodeURIComponent);
                                                ("%decodeURIComponentLambda", privdecodeURIComponentLambda);
                                                ("%decodeURILambda", privdecodeURILambda);
                                                ("%define15Property", privdefine15Property);
                                                ("%defineGlobalAccessors", privdefineGlobalAccessors);
                                                ("%defineGlobalVar", privdefineGlobalVar);
                                                ("%defineNYIProperty", privdefineNYIProperty);
                                                ("%defineOwnProperty", privdefineOwnProperty);
                                                ("%defineProperties", privdefineProperties);
                                                ("%definePropertiesLambda", privdefinePropertiesLambda);
                                                ("%defineProperty", privdefineProperty);
                                                ("%definePropertylambda", privdefinePropertylambda);
                                                ("%encodeURI", privencodeURI);
                                                ("%encodeURIComponent", privencodeURIComponent);
                                                ("%encodeURIComponentLambda", privencodeURIComponentLambda);
                                                ("%encodeURILambda", privencodeURILambda);
                                                ("%escape", privescape);
                                                ("%escapeLambda", privescapeLambda);
                                                ("%ets", privets);
                                                ("%etslambda", privetslambda);
                                                ("%eval", priveval);
                                                ("%evallambda", privevallambda);
                                                ("%every", privevery);
                                                ("%everylambda", priveverylambda);
                                                ("%exp", privexp);
                                                ("%explambda", privexplambda);
                                                ("%filter", privfilter);
                                                ("%filterlambda", privfilterlambda);
                                                ("%foreach", privforeach);
                                                ("%foreachlambda", privforeachlambda);
                                                ("%freeze", privfreeze);
                                                ("%freezelambda", privfreezelambda);
                                                ("%fromCharCode", privfromCharCode);
                                                ("%fromcclambda", privfromcclambda);
                                                ("%functionToString", privfunctionToString);
                                                ("%functionToStringlambda", privfunctionToStringlambda);
                                                ("%getCurrentUTC", privgetCurrentUTC);
                                                ("%getMonth", privgetMonth);
                                                ("%getMonthlambda", privgetMonthlambda);
                                                ("%getYear", privgetYear);
                                                ("%getYearlambda", privgetYearlambda);
                                                ("%global", privglobal);
                                                ("%globalContext", privglobalContext);
                                                ("%gopd", privgopd);
                                                ("%gopdLambda", privgopdLambda);
                                                ("%gopn", privgopn);
                                                ("%gopnLambda", privgopnLambda);
                                                ("%gpo", privgpo);
                                                ("%gpoLambda", privgpoLambda);
                                                ("%hasOwnProperty", privhasOwnProperty);
                                                ("%hasOwnPropertylambda", privhasOwnPropertylambda);
                                                ("%in", privin);
                                                ("%instanceof", privinstanceof);
                                                ("%isExtensible", privisExtensible);
                                                ("%isExtensibleLambda", privisExtensibleLambda);
                                                ("%isFinite", privisFinite);
                                                ("%isFiniteLambda", privisFiniteLambda);
                                                ("%isFrozen", privisFrozen);
                                                ("%isFrozenLambda", privisFrozenLambda);
                                                ("%isNaN", privisNaN);
                                                ("%isNaNlambda", privisNaNlambda);
                                                ("%isPrototypeOf", privisPrototypeOf);
                                                ("%isSealed", privisSealed);
                                                ("%isSealedLambda", privisSealedLambda);
                                                ("%isUnbound", privisUnbound);
                                                ("%join", privjoin);
                                                ("%joinlambda", privjoinlambda);
                                                ("%keys", privkeys);
                                                ("%keysLambda", privkeysLambda);
                                                ("%len", privlen);
                                                ("%localeCompare", privlocaleCompare);
                                                ("%localeCompareLambda", privlocaleCompareLambda);
                                                ("%log", privlog);
                                                ("%logLambda", privlogLambda);
                                                ("%makeContextVarDefiner", privmakeContextVarDefiner);
                                                ("%makeEnvGetter", privmakeEnvGetter);
                                                ("%makeEnvSetter", privmakeEnvSetter);
                                                ("%makeGlobalEnv", privmakeGlobalEnv);
                                                ("%makeWithContext", privmakeWithContext);
                                                ("%map", privmap);
                                                ("%maplambda", privmaplambda);
                                                ("%mathAbs", privmathAbs);
                                                ("%mathAbsLambda", privmathAbsLambda);
                                                ("%mathCeil", privmathCeil);
                                                ("%mathCeilLambda", privmathCeilLambda);
                                                ("%mathFloor", privmathFloor);
                                                ("%mathFloorLambda", privmathFloorLambda);
                                                ("%mathLog", privmathLog);
                                                ("%mathLogLambda", privmathLogLambda);
                                                ("%mathMax", privmathMax);
                                                ("%mathMaxLambda", privmathMaxLambda);
                                                ("%mathMin", privmathMin);
                                                ("%mathMinLambda", privmathMinLambda);
                                                ("%mathPow", privmathPow);
                                                ("%mathPowLambda", privmathPowLambda);
                                                ("%max", privmax);
                                                ("%maybeDirectEval", privmaybeDirectEval);
                                                ("%min", privmin);
                                                ("%minMaxLambda", privminMaxLambda);
                                                ("%mkArgsObj", privmkArgsObj);
                                                ("%mkArgsObjBase", privmkArgsObjBase);
                                                ("%mkNewArgsObj", privmkNewArgsObj);
                                                ("%msPerDay", privmsPerDay);
                                                ("%msPerHour", privmsPerHour);
                                                ("%msPerMin", privmsPerMin);
                                                ("%msPerSecond", privmsPerSecond);
                                                ("%nonstrictContext", privglobalContext);
                                                ("%numTLS", privnumTLS);
                                                ("%numTLSLambda", privnumTLSLambda);
                                                ("%numToStringAbstract", privnumToStringAbstract);
                                                ("%numValueOf", privnumValueOf);
                                                ("%numberToString", privnumberToString);
                                                ("%numberToStringlambda", privnumberToStringlambda);
                                                ("%objectToString", privobjectToString);
                                                ("%objectToStringlambda", privobjectToStringlambda);
                                                ("%oneArgObj", privoneArgObj);
                                                ("%parse", privparse);
                                                ("%parseFloat", privparseFloat);
                                                ("%parseFloatLambda", privparseFloatLambda);
                                                ("%parseInt", privparseInt);
                                                ("%parseIntlambda", privparseIntlambda);
                                                ("%pop", privpop);
                                                ("%poplambda", privpoplambda);
                                                ("%preventExtensions", privpreventExtensions);
                                                ("%preventExtensionsLambda", privpreventExtensionsLambda);
                                                ("%primEach", privprimEach);
                                                ("%print", privprint);
                                                ("%printlambda", privprintlambda);
                                                ("%propEnumlambda", privpropEnumlambda);
                                                ("%propertyIsEnumerable", privpropertyIsEnumerable);
                                                ("%propertyNames", privpropertyNames);
                                                ("%protoOfField", privprotoOfField);
                                                ("%push", privpush);
                                                ("%pushlambda", privpushlambda);
                                                ("%random", privrandom);
                                                ("%randomLambda", privrandomLambda);
                                                ("%reduce", privreduce);
                                                ("%reduceRight", privreduceRight);
                                                ("%reduceRightLambda", privreduceRightLambda);
                                                ("%reducelambda", privreducelambda);
                                                ("%replace", privreplace);
                                                ("%replacelambda", privreplacelambda);
                                                ("%resolveThis", privresolveThis);
                                                ("%reverse", privreverse);
                                                ("%reverselambda", privreverselambda);
                                                ("%round", privround);
                                                ("%roundLambda", privroundLambda);
                                                ("%seal", privseal);
                                                ("%sealLambda", privsealLambda);
                                                ("%set-property", privset_property);
                                                ("%shift", privshift);
                                                ("%shiftlambda", privshiftlambda);
                                                ("%sin", privsin);
                                                ("%sinLambda", privsinLambda);
                                                ("%slice", privslice);
                                                ("%slice_internal", privslice_internal);
                                                ("%slicelambda", privslicelambda);
                                                ("%sliolambda", privsliolambda);
                                                ("%some", privsome);
                                                ("%somelambda", privsomelambda);
                                                ("%sort", privsort);
                                                ("%sortlambda", privsortlambda);
                                                ("%splice", privsplice);
                                                ("%splicelambda", privsplicelambda);
                                                ("%split", privsplit);
                                                ("%splitLambda", privsplitLambda);
                                                ("%sqrt", privsqrt);
                                                ("%sqrtLambda", privsqrtLambda);
                                                ("%strconcat", privstrconcat);
                                                ("%strconcatlambda", privstrconcatlambda);
                                                ("%strictContext", privglobalContext);
                                                ("%stringSlice", privstringSlice);
                                                ("%stringSliceLambda", privstringSliceLambda);
                                                ("%stringToString", privstringToString);
                                                ("%stringToStringlambda", privdateValueOfLambda);
                                                ("%stringValueOf", privstringValueOf);
                                                ("%substring", privsubstring);
                                                ("%substringlambda", privsubstringlambda);
                                                ("%tan", privtan);
                                                ("%tanLambda", privtanLambda);
                                                ("%test", privtest);
                                                ("%testlambda", privtestlambda);
                                                ("%this", privglobal);
                                                ("%throwUnboundIDErrors", privthrowUnboundIDErrors);
                                                ("%tlclambda", privtlclambda);
                                                ("%toExponential", privtoExponential);
                                                ("%toExponentialLambda", privtoExponentialLambda);
                                                ("%toFixed", privtoFixed);
                                                ("%toFixedLambda", privtoFixedLambda);
                                                ("%toLocaleString", privtoLocaleString);
                                                ("%toLocaleStringlambda", privtoLocaleStringlambda);
                                                ("%toLowerCase", privtoLowerCase);
                                                ("%toPrecision", privtoPrecision);
                                                ("%toPrecisionLambda", privtoPrecisionLambda);
                                                ("%toUpperCase", privtoUpperCase);
                                                ("%tuclambda", privtuclambda);
                                                ("%twoArgObj", privtwoArgObj);
                                                ("%unescape", privunescape);
                                                ("%unescapeLambda", privunescapeLambda);
                                                ("%unshift", privunshift);
                                                ("%unshiftlambda", privunshiftlambda);
                                                ("%valueOf", privvalueOf);
                                                ("%valueOfLambda", privvalueOfLambda);
                                                ("%valueOflambda", privvalueOflambda);
                                                ("copy-access-desc", copy_access_desc);
                                                ("copy-data-desc", copy_data_desc);
                                                ("copy-when-defined", copy_when_defined);
                                                ("isAccessorDescriptor", isAccessorDescriptor);
                                                ("isAccessorField", isAccessorField);
                                                ("isDataDescriptor", isDataDescriptor);
                                                ("isDataField", isDataField);
                                                ("isGenericDescriptor", isGenericDescriptor);
                                                ("isGenericField", isGenericField)]
                                               None ["%"]
                                               (expr_object
                                                (objattrs_intro
                                                 (expr_string "Object")
                                                 expr_true expr_null
                                                 expr_null expr_undefined)
                                                [("%AppExprCheck", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%AppExprCheck")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%ArrayConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ArrayConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ArrayGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ArrayGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ArrayLengthChange", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ArrayLengthChange")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ArrayProto", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%ArrayProto")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%BitwiseAnd", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%BitwiseAnd")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%BitwiseInfix", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%BitwiseInfix")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%BitwiseNot", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%BitwiseNot")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%BooleanConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%BooleanConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%BooleanGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%BooleanGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%BooleanProto", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%BooleanProto")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%CheckObjectCoercible", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%CheckObjectCoercible")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%CompareOp", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%CompareOp")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%DateConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%DateConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%DateFromTime", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%DateFromTime")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%DateGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%DateGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%DateProto", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%DateProto")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%Day", property_data
                                                          (data_intro
                                                           (expr_id "%Day")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%DayFromYear", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%DayFromYear")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%DayWithinYear", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%DayWithinYear")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%DaysInMonth", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%DaysInMonth")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%DaysInYear", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%DaysInYear")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%EnvCheckAssign", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%EnvCheckAssign")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%EnvGet", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%EnvGet")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%EqEq", property_data
                                                           (data_intro
                                                            (expr_id "%EqEq")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%ErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ErrorDispatch", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%ErrorDispatch")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%ErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ErrorProto", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%ErrorProto")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%EvalErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%EvalErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%EvalErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%EvalErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%EvalErrorProto", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%EvalErrorProto")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%FunctionConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%FunctionConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%FunctionGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%FunctionGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%FunctionProto", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%FunctionProto")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%GetterValue", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%GetterValue")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%GreaterEqual", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%GreaterEqual")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%GreaterThan", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%GreaterThan")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%Immut", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%Immut")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%InLeapYear", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%InLeapYear")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%IsFinite", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%IsFinite")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%IsJSError", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%IsJSError")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%IsObject", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%IsObject")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%IsPrototypeOflambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%IsPrototypeOflambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%JSError", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%JSError")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%LeftShift", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%LeftShift")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%LessEqual", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%LessEqual")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%LessThan", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%LessThan")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%LocalTime", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%LocalTime")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%MakeDate", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%MakeDate")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%MakeDay", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%MakeDay")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%MakeGetter", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%MakeGetter")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%MakeSetter", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%MakeSetter")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%MakeTime", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%MakeTime")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%MakeTypeError", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%MakeTypeError")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%Math", property_data
                                                           (data_intro
                                                            (expr_id "%Math")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%MonthFromTime", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%MonthFromTime")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%NativeErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%NativeErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%NumberConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%NumberConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%NumberGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%NumberGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%NumberProto", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%NumberProto")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%ObjectConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ObjectConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ObjectGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ObjectGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ObjectProto", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%ObjectProto")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%ObjectTypeCheck", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ObjectTypeCheck")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%PostDecrement", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%PostDecrement")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%PostIncrement", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%PostIncrement")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%PostfixOp", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%PostfixOp")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%PrefixDecrement", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%PrefixDecrement")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%PrefixIncrement", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%PrefixIncrement")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%PrefixOp", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%PrefixOp")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%PrimAdd", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%PrimAdd")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%PrimMultOp", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%PrimMultOp")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%PrimNew", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%PrimNew")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%PrimSub", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%PrimSub")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%PropAccessorCheck", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%PropAccessorCheck")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RangeErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%RangeErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RangeErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%RangeErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RangeErrorProto", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%RangeErrorProto")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ReferenceErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ReferenceErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ReferenceErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ReferenceErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ReferenceErrorProto", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ReferenceErrorProto")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RegExpConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%RegExpConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RegExpGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%RegExpGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%RegExpProto", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%RegExpProto")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%SetterValue", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%SetterValue")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%SignedRightShift", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%SignedRightShift")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%StringConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%StringConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%StringGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%StringGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%StringIndexOf", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%StringIndexOf")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%StringIndexOflambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%StringIndexOflambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%StringIndices", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%StringIndices")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%StringLastIndexOf", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%StringLastIndexOf")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%StringProto", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%StringProto")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%SyntaxError", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%SyntaxError")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%SyntaxErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%SyntaxErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%SyntaxErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%SyntaxErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%SyntaxErrorProto", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%SyntaxErrorProto")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ThrowReferenceError", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ThrowReferenceError")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ThrowSyntaxError", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ThrowSyntaxError")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ThrowTypeError", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ThrowTypeError")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ThrowTypeErrorFun", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ThrowTypeErrorFun")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%TimeClip", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%TimeClip")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%TimeFromYear", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%TimeFromYear")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%TimeWithinDay", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%TimeWithinDay")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%ToBoolean", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%ToBoolean")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%ToInt32", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%ToInt32")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%ToInteger", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%ToInteger")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%ToJSError", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%ToJSError")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%ToNumber", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%ToNumber")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%ToObject", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%ToObject")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%ToPrimitive", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%ToPrimitive")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%ToPrimitiveHint", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ToPrimitiveHint")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ToPrimitiveNum", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ToPrimitiveNum")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ToPrimitiveStr", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%ToPrimitiveStr")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%ToString", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%ToString")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%ToUint", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%ToUint")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%ToUint16", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%ToUint16")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%ToUint32", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%ToUint32")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%TypeError", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%TypeError")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%TypeErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%TypeErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%TypeErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%TypeErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%TypeErrorProto", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%TypeErrorProto")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%Typeof", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%Typeof")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%URIErrorConstructor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%URIErrorConstructor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%URIErrorGlobalFuncObj", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%URIErrorGlobalFuncObj")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%URIErrorProto", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%URIErrorProto")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%UTC", property_data
                                                          (data_intro
                                                           (expr_id "%UTC")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%UnaryNeg", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%UnaryNeg")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%UnaryPlus", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%UnaryPlus")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%UnboundId", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%UnboundId")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%UnsignedRightShift", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%UnsignedRightShift")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%UnwritableDispatch", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%UnwritableDispatch")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%YearFromTime", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%YearFromTime")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%acos", property_data
                                                           (data_intro
                                                            (expr_id "%acos")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%acosLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%acosLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%aiolambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%aiolambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%aliolambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%aliolambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%apply", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%apply")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%applylambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%applylambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%arrayIndexOf", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%arrayIndexOf")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%arrayLastIndexOf", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%arrayLastIndexOf")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%arrayTLSlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%arrayTLSlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%arrayToLocaleString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%arrayToLocaleString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%arrayToString", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%arrayToString")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%arrayToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%arrayToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%asin", property_data
                                                           (data_intro
                                                            (expr_id "%asin")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%asinLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%asinLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%atan", property_data
                                                           (data_intro
                                                            (expr_id "%atan")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%atan2", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%atan2")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%atan2Lambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%atan2Lambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%atanLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%atanLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%bind", property_data
                                                           (data_intro
                                                            (expr_id "%bind")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%bindLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%bindLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%booleanToString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%booleanToString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%booleanToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%booleanToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%booleanValueOf", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%booleanValueOf")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%call", property_data
                                                           (data_intro
                                                            (expr_id "%call")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%calllambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%calllambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%charat", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%charat")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%charatlambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%charatlambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%charcodeat", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%charcodeat")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%charcodeatlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%charcodeatlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%concat", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%concat")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%concatLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%concatLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%configurableEval", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%configurableEval")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%console", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%console")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%cos", property_data
                                                          (data_intro
                                                           (expr_id "%cos")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%cosLambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%cosLambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%create", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%create")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%createLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%createLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%dateGetTimezoneOffset", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dateGetTimezoneOffset")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%dateGetTimezoneOffsetLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dateGetTimezoneOffsetLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%dateToString", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%dateToString")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%dateToStringLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dateToStringLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%dateValueOf", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%dateValueOf")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%dateValueOfLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dateValueOfLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%dategetDate", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%dategetDate")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%dategetDateLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dategetDateLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%dategetDay", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%dategetDay")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%dategetDayLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%dategetDayLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%decodeURI", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%decodeURI")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%decodeURIComponent", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%decodeURIComponent")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%decodeURIComponentLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%decodeURIComponentLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%decodeURILambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%decodeURILambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%define15Property", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%define15Property")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineGlobalAccessors", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineGlobalAccessors")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineGlobalVar", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineGlobalVar")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineNYIProperty", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineNYIProperty")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineOwnProperty", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineOwnProperty")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineProperties", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineProperties")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%definePropertiesLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%definePropertiesLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%defineProperty", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%defineProperty")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%definePropertylambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%definePropertylambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%encodeURI", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%encodeURI")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%encodeURIComponent", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%encodeURIComponent")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%encodeURIComponentLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%encodeURIComponentLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%encodeURILambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%encodeURILambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%escape", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%escape")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%escapeLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%escapeLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%ets", property_data
                                                          (data_intro
                                                           (expr_id "%ets")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%etslambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%etslambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%eval", property_data
                                                           (data_intro
                                                            (expr_id "%eval")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%evallambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%evallambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%every", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%every")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%everylambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%everylambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%exp", property_data
                                                          (data_intro
                                                           (expr_id "%exp")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%explambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%explambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%filter", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%filter")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%filterlambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%filterlambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%foreach", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%foreach")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%foreachlambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%foreachlambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%freeze", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%freeze")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%freezelambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%freezelambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%fromCharCode", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%fromCharCode")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%fromcclambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%fromcclambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%functionToString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%functionToString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%functionToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%functionToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%getCurrentUTC", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%getCurrentUTC")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%getMonth", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%getMonth")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%getMonthlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%getMonthlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%getYear", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%getYear")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%getYearlambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%getYearlambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%global", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%global")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%globalContext", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%globalContext")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%gopd", property_data
                                                           (data_intro
                                                            (expr_id "%gopd")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%gopdLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%gopdLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%gopn", property_data
                                                           (data_intro
                                                            (expr_id "%gopn")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%gopnLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%gopnLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%gpo", property_data
                                                          (data_intro
                                                           (expr_id "%gpo")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%gpoLambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%gpoLambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%hasOwnProperty", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%hasOwnProperty")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%hasOwnPropertylambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%hasOwnPropertylambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%in", property_data
                                                         (data_intro
                                                          (expr_id "%in")
                                                          expr_true
                                                          expr_false
                                                          expr_false));
                                                 ("%instanceof", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%instanceof")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%isExtensible", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%isExtensible")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%isExtensibleLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%isExtensibleLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%isFinite", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%isFinite")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%isFiniteLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%isFiniteLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%isFrozen", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%isFrozen")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%isFrozenLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%isFrozenLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%isNaN", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%isNaN")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%isNaNlambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%isNaNlambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%isPrototypeOf", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%isPrototypeOf")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%isSealed", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%isSealed")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%isSealedLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%isSealedLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%isUnbound", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%isUnbound")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%join", property_data
                                                           (data_intro
                                                            (expr_id "%join")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%joinlambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%joinlambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%keys", property_data
                                                           (data_intro
                                                            (expr_id "%keys")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%keysLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%keysLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%len", property_data
                                                          (data_intro
                                                           (expr_id "%len")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%localeCompare", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%localeCompare")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%localeCompareLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%localeCompareLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%log", property_data
                                                          (data_intro
                                                           (expr_id "%log")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%logLambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%logLambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%makeContextVarDefiner", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%makeContextVarDefiner")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%makeEnvGetter", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%makeEnvGetter")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%makeEnvSetter", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%makeEnvSetter")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%makeGlobalEnv", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%makeGlobalEnv")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%makeWithContext", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%makeWithContext")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%map", property_data
                                                          (data_intro
                                                           (expr_id "%map")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%maplambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%maplambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%mathAbs", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%mathAbs")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%mathAbsLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mathAbsLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mathCeil", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%mathCeil")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%mathCeilLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%mathCeilLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%mathFloor", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%mathFloor")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%mathFloorLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%mathFloorLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%mathLog", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%mathLog")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%mathLogLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mathLogLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mathMax", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%mathMax")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%mathMaxLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mathMaxLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mathMin", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%mathMin")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%mathMinLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mathMinLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mathPow", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%mathPow")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%mathPowLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mathPowLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%max", property_data
                                                          (data_intro
                                                           (expr_id "%max")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%maybeDirectEval", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%maybeDirectEval")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%min", property_data
                                                          (data_intro
                                                           (expr_id "%min")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%minMaxLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%minMaxLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mkArgsObj", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%mkArgsObj")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%mkArgsObjBase", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%mkArgsObjBase")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%mkNewArgsObj", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%mkNewArgsObj")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%msPerDay", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%msPerDay")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%msPerHour", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%msPerHour")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%msPerMin", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%msPerMin")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%msPerSecond", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%msPerSecond")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%nonstrictContext", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%nonstrictContext")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%numTLS", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%numTLS")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%numTLSLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%numTLSLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%numToStringAbstract", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%numToStringAbstract")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%numValueOf", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%numValueOf")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%numberToString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%numberToString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%numberToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%numberToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%objectToString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%objectToString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%objectToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%objectToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%oneArgObj", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%oneArgObj")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%parse", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%parse")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%parseFloat", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%parseFloat")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%parseFloatLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%parseFloatLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%parseInt", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%parseInt")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%parseIntlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%parseIntlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%pop", property_data
                                                          (data_intro
                                                           (expr_id "%pop")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%poplambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%poplambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%preventExtensions", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%preventExtensions")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%preventExtensionsLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%preventExtensionsLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%primEach", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%primEach")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%print", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%print")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%printlambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%printlambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%propEnumlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%propEnumlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%propertyIsEnumerable", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%propertyIsEnumerable")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%propertyNames", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%propertyNames")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%protoOfField", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%protoOfField")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%push", property_data
                                                           (data_intro
                                                            (expr_id "%push")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%pushlambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%pushlambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%random", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%random")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%randomLambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%randomLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%reduce", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%reduce")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%reduceRight", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%reduceRight")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%reduceRightLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%reduceRightLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%reducelambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%reducelambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%replace", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%replace")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%replacelambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%replacelambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%resolveThis", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%resolveThis")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%reverse", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%reverse")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%reverselambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%reverselambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%round", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%round")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%roundLambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%roundLambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%seal", property_data
                                                           (data_intro
                                                            (expr_id "%seal")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%sealLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%sealLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%set-property", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%set-property")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%shift", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%shift")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%shiftlambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%shiftlambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%sin", property_data
                                                          (data_intro
                                                           (expr_id "%sin")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%sinLambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%sinLambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%slice", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%slice")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%slice_internal", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%slice_internal")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%slicelambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%slicelambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%sliolambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%sliolambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%some", property_data
                                                           (data_intro
                                                            (expr_id "%some")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%somelambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%somelambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%sort", property_data
                                                           (data_intro
                                                            (expr_id "%sort")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%sortlambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%sortlambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%splice", property_data
                                                             (data_intro
                                                              (expr_id
                                                               "%splice")
                                                              expr_true
                                                              expr_false
                                                              expr_false));
                                                 ("%splicelambda", property_data
                                                                   (data_intro
                                                                    (expr_id
                                                                    "%splicelambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%split", property_data
                                                            (data_intro
                                                             (expr_id
                                                              "%split")
                                                             expr_true
                                                             expr_false
                                                             expr_false));
                                                 ("%splitLambda", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%splitLambda")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%sqrt", property_data
                                                           (data_intro
                                                            (expr_id "%sqrt")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%sqrtLambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%sqrtLambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%strconcat", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%strconcat")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%strconcatlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%strconcatlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%strictContext", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%strictContext")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%stringSlice", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%stringSlice")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%stringSliceLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%stringSliceLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%stringToString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%stringToString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%stringToStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%stringToStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%stringValueOf", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%stringValueOf")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%substring", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%substring")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%substringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%substringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%tan", property_data
                                                          (data_intro
                                                           (expr_id "%tan")
                                                           expr_true
                                                           expr_false
                                                           expr_false));
                                                 ("%tanLambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%tanLambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%test", property_data
                                                           (data_intro
                                                            (expr_id "%test")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%testlambda", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "%testlambda")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("%this", property_data
                                                           (data_intro
                                                            (expr_id "%this")
                                                            expr_true
                                                            expr_false
                                                            expr_false));
                                                 ("%throwUnboundIDErrors", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%throwUnboundIDErrors")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%tlclambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%tlclambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%toExponential", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%toExponential")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%toExponentialLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%toExponentialLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%toFixed", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%toFixed")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%toFixedLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%toFixedLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%toLocaleString", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%toLocaleString")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%toLocaleStringlambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%toLocaleStringlambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%toLowerCase", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%toLowerCase")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%toPrecision", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%toPrecision")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%toPrecisionLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%toPrecisionLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%toUpperCase", property_data
                                                                  (data_intro
                                                                   (expr_id
                                                                    "%toUpperCase")
                                                                   expr_true
                                                                   expr_false
                                                                   expr_false));
                                                 ("%tuclambda", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%tuclambda")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%twoArgObj", property_data
                                                                (data_intro
                                                                 (expr_id
                                                                  "%twoArgObj")
                                                                 expr_true
                                                                 expr_false
                                                                 expr_false));
                                                 ("%unescape", property_data
                                                               (data_intro
                                                                (expr_id
                                                                 "%unescape")
                                                                expr_true
                                                                expr_false
                                                                expr_false));
                                                 ("%unescapeLambda", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "%unescapeLambda")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("%unshift", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%unshift")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%unshiftlambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%unshiftlambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%valueOf", property_data
                                                              (data_intro
                                                               (expr_id
                                                                "%valueOf")
                                                               expr_true
                                                               expr_false
                                                               expr_false));
                                                 ("%valueOfLambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%valueOfLambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("%valueOflambda", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "%valueOflambda")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("copy-access-desc", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "copy-access-desc")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("copy-data-desc", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "copy-data-desc")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false));
                                                 ("copy-when-defined", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "copy-when-defined")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("isAccessorDescriptor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "isAccessorDescriptor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("isAccessorField", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "isAccessorField")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("isDataDescriptor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "isDataDescriptor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("isDataField", property_data
                                                                 (data_intro
                                                                  (expr_id
                                                                   "isDataField")
                                                                  expr_true
                                                                  expr_false
                                                                  expr_false));
                                                 ("isGenericDescriptor", 
                                                   property_data
                                                   (data_intro
                                                    (expr_id
                                                     "isGenericDescriptor")
                                                    expr_true expr_false
                                                    expr_false));
                                                 ("isGenericField", property_data
                                                                    (data_intro
                                                                    (expr_id
                                                                    "isGenericField")
                                                                    expr_true
                                                                    expr_false
                                                                    expr_false))]));
                                              attributes_accessor_set :=
                                              value_undefined;
                                              attributes_accessor_enumerable :=
                                              false;
                                              attributes_accessor_configurable :=
                                              false|})]|});
(2, {|object_attrs :=
      {|oattrs_proto := value_null;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      Heap.of_list [("constructor", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 36;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("hasOwnProperty", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 45;
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("isPrototypeOf", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 46;
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("propertyIsEnumerable", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 42;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("toLocaleString", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 43;
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("toString", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 41;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("valueOf", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 44;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|})]|});
(3, {|object_attrs :=
      {|oattrs_proto := value_object 2;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      Heap.of_list [("Array", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 108;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Boolean", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 34;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Date", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 178;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Error", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 24;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("EvalError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 50;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Function", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 317;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Infinity", 
                     attributes_data_of {|attributes_data_value :=
                                          value_number (JsNumber.of_int 0);
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|});
                    ("Math", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 262;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("NaN", 
                     attributes_data_of {|attributes_data_value :=
                                          value_number (JsNumber.of_int 0);
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|});
                    ("Number", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 27;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("Object", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 36;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("RangeError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 52;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("ReferenceError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 54;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("RegExp", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 255;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("String", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 30;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("SyntaxError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 49;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("TypeError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 56;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("URIError", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 58;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("console", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 315;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := true;
                                          attributes_data_configurable :=
                                          true|});
                    ("decodeURI", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 257;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("decodeURIComponent", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 258;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("encodeURI", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 259;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("encodeURIComponent", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 260;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("escape", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 322;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("eval", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 316;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("isFinite", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 318;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("isNaN", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 23;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("parseFloat", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 320;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("parseInt", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 256;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("print", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 17;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := true;
                                          attributes_data_configurable :=
                                          true|});
                    ("undefined", 
                     attributes_data_of {|attributes_data_value :=
                                          value_undefined;
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|});
                    ("unescape", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 324;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("window", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 3;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := true;
                                          attributes_data_configurable :=
                                          true|})]|});
(4, {|object_attrs :=
      {|oattrs_proto := value_object 3;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties := Heap.of_list []|});
(5, {|object_attrs :=
      {|oattrs_proto := value_object 2;
        oattrs_class := "Function";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode1|};
      object_properties :=
      Heap.of_list [("apply", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 20;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("bind", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 157;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("call", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 19;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("constructor", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 317;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|});
                    ("length", 
                     attributes_data_of {|attributes_data_value :=
                                          value_number (JsNumber.of_int 0);
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|});
                    ("toString", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 6;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|})]|});
(6, {|object_attrs :=
      {|oattrs_proto := value_object 5;
        oattrs_class := "Function";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := privfunctionToStringlambda|};
      object_properties :=
      Heap.of_list [("length", 
                     attributes_data_of {|attributes_data_value :=
                                          value_number (JsNumber.of_int 0);
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|})]|});
(7, {|object_attrs :=
      {|oattrs_proto := value_object 2;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      Heap.of_list [("constructor", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 24;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := true;
                                          attributes_data_configurable :=
                                          true|});
                    ("toString", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 25;
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|})]|});
(8, {|object_attrs :=
      {|oattrs_proto := value_object 7;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      Heap.of_list [("constructor", 
                     attributes_data_of {|attributes_data_value :=
                                          value_object 56;
                                          attributes_data_writable := true;
                                          attributes_data_enumerable := true;
                                          attributes_data_configurable :=
                                          true|});
                    ("name", 
                     attributes_data_of {|attributes_data_value :=
                                          value_string "TypeError";
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          true|})]|});
(9, {|object_attrs :=
      {|oattrs_proto := value_object 5;
        oattrs_class := "Function";
        oattrs_extensible := false;
        oattrs_prim_value := value_undefined;
        oattrs_code := privThrowTypeErrorFun|};
      object_properties :=
      Heap.of_list [("length", 
                     attributes_data_of {|attributes_data_value :=
                                          value_number (JsNumber.of_int 0);
                                          attributes_data_writable := false;
                                          attributes_data_enumerable := false;
                                          attributes_data_configurable :=
                                          false|})]|});
(10, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 54;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("name", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "ReferenceError";
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(11, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 49;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("name", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "SyntaxError";
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(12, {|object_attrs :=
       {|oattrs_proto := value_object 2;
         oattrs_class := "Boolean";
         oattrs_extensible := true;
         oattrs_prim_value := value_false;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 34;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("toString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 31;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("valueOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 303;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(13, {|object_attrs :=
       {|oattrs_proto := value_object 2;
         oattrs_class := "Number";
         oattrs_extensible := true;
         oattrs_prim_value := value_number (JsNumber.of_int 0);
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 27;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("toExponential", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 310;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toFixed", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 305;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toLocaleString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 308;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toPrecision", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 312;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 160;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("valueOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 301;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(14, {|object_attrs :=
       {|oattrs_proto := value_object 2;
         oattrs_class := "String";
         oattrs_extensible := true;
         oattrs_prim_value := value_string "";
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("charAt", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 110;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("charCodeAt", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 113;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("concat", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 116;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 30;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("indexOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 163;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("lastIndexOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 165;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("localeCompare", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 166;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("replace", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 164;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("slice", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 167;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("split", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 170;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("substring", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 119;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toLocaleLowerCase", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 168;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("toLocaleUpperCase", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 169;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("toLowerCase", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 168;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("toString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 28;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toUpperCase", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 169;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("valueOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 299;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(15, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode2|};
       object_properties := Heap.of_list []|});
(16, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := false;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode3|};
       object_properties := Heap.of_list []|});
(17, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privprintlambda|};
       object_properties := Heap.of_list []|});
(18, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privdefinePropertylambda|};
       object_properties := Heap.of_list []|});
(19, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privcalllambda|};
       object_properties := Heap.of_list []|});
(20, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privapplylambda|};
       object_properties := Heap.of_list []|});
(21, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 19;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(22, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 20;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(23, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisNaNlambda|};
       object_properties := Heap.of_list []|});
(24, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 7;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(25, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privetslambda|};
       object_properties := Heap.of_list []|});
(26, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 25;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(27, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privNumberConstructor|};
       object_properties :=
       Heap.of_list [("MAX_VALUE", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("MIN_VALUE", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("NEGATIVE_INFINITY", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("NaN", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("POSITIVE_INFINITY", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 13;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(28, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privdateValueOfLambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(29, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 28;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(30, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privStringConstructor|};
       object_properties :=
       Heap.of_list [("fromCharCode", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 81;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 14;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(31, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privbooleanToStringlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(32, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(33, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 31;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(34, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privBooleanConstructor|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 12;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(35, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 12;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(36, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privObjectConstructor|};
       object_properties :=
       Heap.of_list [("create", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 65;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("defineProperties", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 63;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("defineProperty", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 18;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("freeze", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 69;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("getOwnPropertyDescriptor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 39;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("getOwnPropertyNames", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 60;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("getPrototypeOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 37;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("isExtensible", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 77;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("isFrozen", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 73;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("isSealed", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 75;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("keys", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 79;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("preventExtensions", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 71;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 2;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("seal", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 67;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(37, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgpoLambda|};
       object_properties := Heap.of_list []|});
(38, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 37;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(39, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgopdLambda|};
       object_properties := Heap.of_list []|});
(40, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 39;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(41, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privobjectToStringlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(42, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpropEnumlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(43, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privtoLocaleStringlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(44, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privvalueOflambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(45, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privhasOwnPropertylambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(46, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privIsPrototypeOflambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(47, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 50;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("name", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "EvalError";
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(48, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "SyntaxError";
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(49, {|object_attrs :=
       {|oattrs_proto := value_object 11;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privSyntaxErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 11;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(50, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privEvalErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 47;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(51, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 52;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("name", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "RangeError";
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(52, {|object_attrs :=
       {|oattrs_proto := value_object 51;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privRangeErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 51;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(53, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "ReferenceError";
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(54, {|object_attrs :=
       {|oattrs_proto := value_object 10;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privReferenceErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 10;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(55, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "TypeError";
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(56, {|object_attrs :=
       {|oattrs_proto := value_object 8;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privTypeErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 8;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(57, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 58;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable := true;
                                           attributes_data_configurable :=
                                           true|});
                     ("name", 
                      attributes_data_of {|attributes_data_value :=
                                           value_string "URIError";
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(58, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privURIErrorConstructor|};
       object_properties :=
       Heap.of_list [("prototype", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 57;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(59, {|object_attrs :=
       {|oattrs_proto := value_object 2;
         oattrs_class := "Array";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("concat", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 102;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("constructor", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 108;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("every", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 145;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("filter", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 140;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("forEach", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 134;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("indexOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 128;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("join", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 83;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("lastIndexOf", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 131;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("map", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 137;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("pop", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 85;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("push", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 88;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("reduce", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 142;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("reduceRight", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 151;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("reverse", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 91;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("shift", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 94;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("slice", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 154;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("some", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 148;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("sort", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 105;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("splice", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 122;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toLocaleString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 100;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("toString", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 97;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|});
                     ("unshift", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 125;
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           true|})]|});
(60, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgopnLambda|};
       object_properties := Heap.of_list []|});
(61, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 60;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(62, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 18;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(63, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privdefinePropertiesLambda|};
       object_properties := Heap.of_list []|});
(64, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 63;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(65, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privcreateLambda|};
       object_properties := Heap.of_list []|});
(66, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 65;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(67, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privsealLambda|};
       object_properties := Heap.of_list []|});
(68, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 67;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(69, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privfreezelambda|};
       object_properties := Heap.of_list []|});
(70, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 69;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(71, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpreventExtensionsLambda|};
       object_properties := Heap.of_list []|});
(72, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 71;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(73, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisFrozenLambda|};
       object_properties := Heap.of_list []|});
(74, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 73;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(75, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisSealedLambda|};
       object_properties := Heap.of_list []|});
(76, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 75;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(77, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisExtensibleLambda|};
       object_properties := Heap.of_list []|});
(78, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 77;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(79, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privkeysLambda|};
       object_properties := Heap.of_list []|});
(80, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 79;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(81, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privfromcclambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(82, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 81;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(83, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privjoinlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(84, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("enumerable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(85, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpoplambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(86, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(87, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 85;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(88, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpushlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(89, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 1);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(90, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 88;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(91, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privreverselambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(92, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(93, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 91;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(94, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privshiftlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(95, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_false;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(96, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 94;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(97, {|object_attrs :=
       {|oattrs_proto := value_object 5;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privarrayToStringlambda|};
       object_properties :=
       Heap.of_list [("length", 
                      attributes_data_of {|attributes_data_value :=
                                           value_number (JsNumber.of_int 0);
                                           attributes_data_writable := false;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(98, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 97;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("writable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(99, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       Heap.of_list [("configurable", 
                      attributes_data_of {|attributes_data_value :=
                                           value_true;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|});
                     ("value", 
                      attributes_data_of {|attributes_data_value :=
                                           value_object 83;
                                           attributes_data_writable := true;
                                           attributes_data_enumerable :=
                                           false;
                                           attributes_data_configurable :=
                                           false|})]|});
(100, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privarrayTLSlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 0);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(101, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 100;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(102, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privconcatLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(103, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(104, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 102;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(105, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsortlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(106, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(107, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 105;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(108, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privArrayConstructor|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("notinspec", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 69;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            true;
                                            attributes_data_configurable :=
                                            true|});
                      ("prototype", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 59;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(109, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 108;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(110, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcharatlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(111, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(112, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 110;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(113, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcharcodeatlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(114, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(115, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 113;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(116, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privstrconcatlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(117, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(118, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 116;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(119, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsubstringlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(120, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(121, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 119;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(122, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsplicelambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(123, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(124, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 122;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(125, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privunshiftlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(126, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(127, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 125;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(128, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privaiolambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(129, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(130, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 128;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(131, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privaliolambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(132, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(133, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 131;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(134, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privforeachlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(135, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(136, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 134;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(137, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmaplambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(138, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(139, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 137;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(140, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privfilterlambda|};
        object_properties := Heap.of_list []|});
(141, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 140;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(142, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreducelambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(143, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(144, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 142;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(145, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := priveverylambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(146, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(147, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 145;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(148, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsomelambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(149, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(150, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 148;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(151, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreduceRightLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(152, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(153, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 151;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(154, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privslicelambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(155, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(156, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 154;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(157, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privbindLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(158, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(159, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 157;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(160, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privnumberToStringlambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(161, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(162, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 160;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(163, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privStringIndexOflambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(164, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreplacelambda|};
        object_properties := Heap.of_list []|});
(165, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsliolambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(166, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privlocaleCompareLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(167, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privstringSliceLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(168, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtlclambda|};
        object_properties := Heap.of_list []|});
(169, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtuclambda|};
        object_properties := Heap.of_list []|});
(170, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsplitLambda|};
        object_properties := Heap.of_list []|});
(171, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 170;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(172, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privgetYearlambda|};
        object_properties := Heap.of_list []|});
(173, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privgetMonthlambda|};
        object_properties := Heap.of_list []|});
(174, {|object_attrs :=
        {|oattrs_proto := value_object 2;
          oattrs_class := "Date";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("getDate", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 183;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getDay", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 181;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getFullYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 191;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getHours", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 201;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getMilliseconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 213;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getMinutes", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 205;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getMonth", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 173;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("getSeconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 209;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getTime", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 189;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getTimezoneOffset", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 179;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCDate", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 197;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCDay", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 199;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCFullYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 193;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCHours", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 203;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCMilliseconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 215;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCMinutes", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 207;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCMonth", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 195;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getUTCSeconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 211;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("getYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 172;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("setDate", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 235;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setFullYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 243;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setHours", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 231;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setMilliseconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 219;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setMinutes", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 227;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setMonth", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 239;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setSeconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 223;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setTime", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 217;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCDate", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 237;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCFullYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 245;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCHours", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 233;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCMilliseconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 221;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCMinutes", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 229;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCMonth", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 241;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setUTCSeconds", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 225;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("setYear", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 251;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("toGMTString", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 249;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("toString", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 175;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("toUTCString", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 247;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("valueOf", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 177;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            true;
                                            attributes_data_configurable :=
                                            true|})]|});
(175, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateToStringLambda|};
        object_properties := Heap.of_list []|});
(176, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 175;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(177, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateValueOfLambda|};
        object_properties := Heap.of_list []|});
(178, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privDateConstructor|};
        object_properties :=
        Heap.of_list [("UTC", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 187;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("parse", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 185;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("prototype", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 174;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(179, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateGetTimezoneOffsetLambda|};
        object_properties := Heap.of_list []|});
(180, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 179;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(181, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdategetDayLambda|};
        object_properties := Heap.of_list []|});
(182, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 181;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(183, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdategetDateLambda|};
        object_properties := Heap.of_list []|});
(184, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 183;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(185, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode4|};
        object_properties := Heap.of_list []|});
(186, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 185;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(187, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode5|};
        object_properties := Heap.of_list []|});
(188, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 187;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(189, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode6|};
        object_properties := Heap.of_list []|});
(190, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 189;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(191, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode7|};
        object_properties := Heap.of_list []|});
(192, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 191;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(193, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode8|};
        object_properties := Heap.of_list []|});
(194, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 193;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(195, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode9|};
        object_properties := Heap.of_list []|});
(196, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 195;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(197, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode10|};
        object_properties := Heap.of_list []|});
(198, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 197;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(199, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode11|};
        object_properties := Heap.of_list []|});
(200, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 199;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(201, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode12|};
        object_properties := Heap.of_list []|});
(202, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 201;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(203, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode13|};
        object_properties := Heap.of_list []|});
(204, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 203;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(205, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode14|};
        object_properties := Heap.of_list []|});
(206, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 205;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(207, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode15|};
        object_properties := Heap.of_list []|});
(208, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 207;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(209, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode16|};
        object_properties := Heap.of_list []|});
(210, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 209;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(211, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode17|};
        object_properties := Heap.of_list []|});
(212, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 211;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(213, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode18|};
        object_properties := Heap.of_list []|});
(214, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 213;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(215, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode19|};
        object_properties := Heap.of_list []|});
(216, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 215;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(217, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode20|};
        object_properties := Heap.of_list []|});
(218, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 217;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(219, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode21|};
        object_properties := Heap.of_list []|});
(220, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 219;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(221, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode22|};
        object_properties := Heap.of_list []|});
(222, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 221;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(223, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode23|};
        object_properties := Heap.of_list []|});
(224, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 223;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(225, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode24|};
        object_properties := Heap.of_list []|});
(226, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 225;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(227, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode25|};
        object_properties := Heap.of_list []|});
(228, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 227;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(229, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode26|};
        object_properties := Heap.of_list []|});
(230, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 229;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(231, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode27|};
        object_properties := Heap.of_list []|});
(232, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 231;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(233, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode28|};
        object_properties := Heap.of_list []|});
(234, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 233;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(235, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode29|};
        object_properties := Heap.of_list []|});
(236, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 235;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(237, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode30|};
        object_properties := Heap.of_list []|});
(238, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 237;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(239, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode31|};
        object_properties := Heap.of_list []|});
(240, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 239;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(241, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode32|};
        object_properties := Heap.of_list []|});
(242, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 241;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(243, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode33|};
        object_properties := Heap.of_list []|});
(244, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 243;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(245, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode34|};
        object_properties := Heap.of_list []|});
(246, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 245;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(247, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode35|};
        object_properties := Heap.of_list []|});
(248, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 247;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(249, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode36|};
        object_properties := Heap.of_list []|});
(250, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 249;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(251, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode37|};
        object_properties := Heap.of_list []|});
(252, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 251;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(253, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtestlambda|};
        object_properties := Heap.of_list []|});
(254, {|object_attrs :=
        {|oattrs_proto := value_object 2;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("constructor", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 255;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            true;
                                            attributes_data_configurable :=
                                            true|});
                      ("test", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 253;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(255, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privRegExpConstructor|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("prototype", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 254;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(256, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privparseIntlambda|};
        object_properties := Heap.of_list []|});
(257, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdecodeURILambda|};
        object_properties := Heap.of_list []|});
(258, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdecodeURIComponentLambda|};
        object_properties := Heap.of_list []|});
(259, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privencodeURILambda|};
        object_properties := Heap.of_list []|});
(260, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privencodeURIComponentLambda|};
        object_properties := Heap.of_list []|});
(261, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privexplambda|};
        object_properties := Heap.of_list []|});
(262, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("E", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("LN10", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("LN2", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 0);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("LOG10E", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 0);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("LOG2E", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("PI", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 3);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("SQRT1_2", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 0);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("SQRT2", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("abs", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 269;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("acos", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 271;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("asin", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 273;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("atan", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 275;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("atan2", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 277;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("ceil", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 293;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("cos", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 279;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("exp", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 261;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("floor", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 295;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("log", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 291;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("max", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 266;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("min", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 263;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("pow", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 297;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("random", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 281;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("round", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 283;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("sin", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 285;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("sqrt", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 287;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|});
                      ("tan", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 289;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|})]|});
(263, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathMinLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(264, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(265, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 263;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(266, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathMaxLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(267, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 2);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(268, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 266;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(269, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathAbsLambda|};
        object_properties := Heap.of_list []|});
(270, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 269;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(271, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privacosLambda|};
        object_properties := Heap.of_list []|});
(272, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 271;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(273, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privasinLambda|};
        object_properties := Heap.of_list []|});
(274, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 273;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(275, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privatanLambda|};
        object_properties := Heap.of_list []|});
(276, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 275;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(277, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privatan2Lambda|};
        object_properties := Heap.of_list []|});
(278, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 277;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(279, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcosLambda|};
        object_properties := Heap.of_list []|});
(280, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 279;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(281, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privrandomLambda|};
        object_properties := Heap.of_list []|});
(282, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 281;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(283, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privroundLambda|};
        object_properties := Heap.of_list []|});
(284, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 283;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(285, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsinLambda|};
        object_properties := Heap.of_list []|});
(286, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 285;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(287, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsqrtLambda|};
        object_properties := Heap.of_list []|});
(288, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 287;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(289, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtanLambda|};
        object_properties := Heap.of_list []|});
(290, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 289;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(291, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathLogLambda|};
        object_properties := Heap.of_list []|});
(292, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 291;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(293, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathCeilLambda|};
        object_properties := Heap.of_list []|});
(294, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 293;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(295, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathFloorLambda|};
        object_properties := Heap.of_list []|});
(296, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 295;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(297, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathPowLambda|};
        object_properties := Heap.of_list []|});
(298, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 297;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(299, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode38|};
        object_properties := Heap.of_list []|});
(300, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 299;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(301, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode39|};
        object_properties := Heap.of_list []|});
(302, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 301;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(303, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode40|};
        object_properties := Heap.of_list []|});
(304, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 303;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(305, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoFixedLambda|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            true|})]|});
(306, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 1);
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(307, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 305;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(308, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privnumTLSLambda|};
        object_properties := Heap.of_list []|});
(309, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 308;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(310, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoExponentialLambda|};
        object_properties := Heap.of_list []|});
(311, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 310;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(312, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoPrecisionLambda|};
        object_properties := Heap.of_list []|});
(313, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 312;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(314, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privlogLambda|};
        object_properties := Heap.of_list []|});
(315, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("error", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 314;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("info", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 314;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("log", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 314;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("warn", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 314;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(316, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privevallambda|};
        object_properties := Heap.of_list []|});
(317, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privFunctionConstructor|};
        object_properties :=
        Heap.of_list [("length", 
                       attributes_data_of {|attributes_data_value :=
                                            value_number (JsNumber.of_int 0);
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("prototype", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 5;
                                            attributes_data_writable := false;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(318, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privisFiniteLambda|};
        object_properties := Heap.of_list []|});
(319, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 318;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(320, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privparseFloatLambda|};
        object_properties := Heap.of_list []|});
(321, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 320;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(322, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privescapeLambda|};
        object_properties := Heap.of_list []|});
(323, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 322;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|});
(324, {|object_attrs :=
        {|oattrs_proto := value_object 5;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privunescapeLambda|};
        object_properties := Heap.of_list []|});
(325, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        Heap.of_list [("configurable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("enumerable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_false;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("value", 
                       attributes_data_of {|attributes_data_value :=
                                            value_object 324;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|});
                      ("writable", 
                       attributes_data_of {|attributes_data_value :=
                                            value_true;
                                            attributes_data_writable := true;
                                            attributes_data_enumerable :=
                                            false;
                                            attributes_data_configurable :=
                                            false|})]|})
].