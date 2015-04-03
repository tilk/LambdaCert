Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import String.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Definition ex_copy_access_desc := 
expr_seq
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
    (expr_delete_field (expr_id "obj1") (expr_string "writable"))))))
.
Definition ex_copy_data_desc := 
expr_seq
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
    (expr_delete_field (expr_id "obj1") (expr_string "set"))))))
.
Definition ex_copy_when_defined := 
expr_if
(expr_if
 (expr_op2 binary_op_stx_eq (expr_get_field (expr_id "obj2") (expr_id "s"))
  expr_undefined) expr_false expr_true)
(expr_let "$newVal" (expr_get_field (expr_id "obj2") (expr_id "s"))
 (expr_set_field (expr_id "obj1") (expr_id "s") (expr_id "$newVal")))
expr_undefined
.
Definition ex_getter := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_null
 expr_undefined)
[("%AppExprCheck", property_data
                   (data_intro (expr_id "%AppExprCheck") expr_true expr_false
                    expr_false));
 ("%ArrayConstructor", property_data
                       (data_intro (expr_id "%ArrayConstructor") expr_true
                        expr_false expr_false));
 ("%ArrayGlobalFuncObj", property_data
                         (data_intro (expr_id "%ArrayGlobalFuncObj")
                          expr_true expr_false expr_false));
 ("%ArrayLengthChange", property_data
                        (data_intro (expr_id "%ArrayLengthChange") expr_true
                         expr_false expr_false));
 ("%ArrayProto", property_data
                 (data_intro (expr_id "%ArrayProto") expr_true expr_false
                  expr_false));
 ("%BitwiseAnd", property_data
                 (data_intro (expr_id "%BitwiseAnd") expr_true expr_false
                  expr_false));
 ("%BitwiseInfix", property_data
                   (data_intro (expr_id "%BitwiseInfix") expr_true expr_false
                    expr_false));
 ("%BitwiseNot", property_data
                 (data_intro (expr_id "%BitwiseNot") expr_true expr_false
                  expr_false));
 ("%BooleanConstructor", property_data
                         (data_intro (expr_id "%BooleanConstructor")
                          expr_true expr_false expr_false));
 ("%BooleanGlobalFuncObj", property_data
                           (data_intro (expr_id "%BooleanGlobalFuncObj")
                            expr_true expr_false expr_false));
 ("%BooleanProto", property_data
                   (data_intro (expr_id "%BooleanProto") expr_true expr_false
                    expr_false));
 ("%CheckObjectCoercible", property_data
                           (data_intro (expr_id "%CheckObjectCoercible")
                            expr_true expr_false expr_false));
 ("%CompareOp", property_data
                (data_intro (expr_id "%CompareOp") expr_true expr_false
                 expr_false));
 ("%DateConstructor", property_data
                      (data_intro (expr_id "%DateConstructor") expr_true
                       expr_false expr_false));
 ("%DateFromTime", property_data
                   (data_intro (expr_id "%DateFromTime") expr_true expr_false
                    expr_false));
 ("%DateGlobalFuncObj", property_data
                        (data_intro (expr_id "%DateGlobalFuncObj") expr_true
                         expr_false expr_false));
 ("%DateProto", property_data
                (data_intro (expr_id "%DateProto") expr_true expr_false
                 expr_false));
 ("%Day", property_data
          (data_intro (expr_id "%Day") expr_true expr_false expr_false));
 ("%DayFromYear", property_data
                  (data_intro (expr_id "%DayFromYear") expr_true expr_false
                   expr_false));
 ("%DayWithinYear", property_data
                    (data_intro (expr_id "%DayWithinYear") expr_true
                     expr_false expr_false));
 ("%DaysInMonth", property_data
                  (data_intro (expr_id "%DaysInMonth") expr_true expr_false
                   expr_false));
 ("%DaysInYear", property_data
                 (data_intro (expr_id "%DaysInYear") expr_true expr_false
                  expr_false));
 ("%EnvCheckAssign", property_data
                     (data_intro (expr_id "%EnvCheckAssign") expr_true
                      expr_false expr_false));
 ("%EnvGet", property_data
             (data_intro (expr_id "%EnvGet") expr_true expr_false expr_false));
 ("%EqEq", property_data
           (data_intro (expr_id "%EqEq") expr_true expr_false expr_false));
 ("%ErrorConstructor", property_data
                       (data_intro (expr_id "%ErrorConstructor") expr_true
                        expr_false expr_false));
 ("%ErrorDispatch", property_data
                    (data_intro (expr_id "%ErrorDispatch") expr_true
                     expr_false expr_false));
 ("%ErrorGlobalFuncObj", property_data
                         (data_intro (expr_id "%ErrorGlobalFuncObj")
                          expr_true expr_false expr_false));
 ("%ErrorProto", property_data
                 (data_intro (expr_id "%ErrorProto") expr_true expr_false
                  expr_false));
 ("%EvalErrorConstructor", property_data
                           (data_intro (expr_id "%EvalErrorConstructor")
                            expr_true expr_false expr_false));
 ("%EvalErrorGlobalFuncObj", property_data
                             (data_intro (expr_id "%EvalErrorGlobalFuncObj")
                              expr_true expr_false expr_false));
 ("%EvalErrorProto", property_data
                     (data_intro (expr_id "%EvalErrorProto") expr_true
                      expr_false expr_false));
 ("%FunctionConstructor", property_data
                          (data_intro (expr_id "%FunctionConstructor")
                           expr_true expr_false expr_false));
 ("%FunctionGlobalFuncObj", property_data
                            (data_intro (expr_id "%FunctionGlobalFuncObj")
                             expr_true expr_false expr_false));
 ("%FunctionProto", property_data
                    (data_intro (expr_id "%FunctionProto") expr_true
                     expr_false expr_false));
 ("%GetterValue", property_data
                  (data_intro (expr_id "%GetterValue") expr_true expr_false
                   expr_false));
 ("%GreaterEqual", property_data
                   (data_intro (expr_id "%GreaterEqual") expr_true expr_false
                    expr_false));
 ("%GreaterThan", property_data
                  (data_intro (expr_id "%GreaterThan") expr_true expr_false
                   expr_false));
 ("%Immut", property_data
            (data_intro (expr_id "%Immut") expr_true expr_false expr_false));
 ("%InLeapYear", property_data
                 (data_intro (expr_id "%InLeapYear") expr_true expr_false
                  expr_false));
 ("%IsFinite", property_data
               (data_intro (expr_id "%IsFinite") expr_true expr_false
                expr_false));
 ("%IsJSError", property_data
                (data_intro (expr_id "%IsJSError") expr_true expr_false
                 expr_false));
 ("%IsObject", property_data
               (data_intro (expr_id "%IsObject") expr_true expr_false
                expr_false));
 ("%IsPrototypeOflambda", property_data
                          (data_intro (expr_id "%IsPrototypeOflambda")
                           expr_true expr_false expr_false));
 ("%JSError", property_data
              (data_intro (expr_id "%JSError") expr_true expr_false
               expr_false));
 ("%LeftShift", property_data
                (data_intro (expr_id "%LeftShift") expr_true expr_false
                 expr_false));
 ("%LessEqual", property_data
                (data_intro (expr_id "%LessEqual") expr_true expr_false
                 expr_false));
 ("%LessThan", property_data
               (data_intro (expr_id "%LessThan") expr_true expr_false
                expr_false));
 ("%LocalTime", property_data
                (data_intro (expr_id "%LocalTime") expr_true expr_false
                 expr_false));
 ("%MakeDate", property_data
               (data_intro (expr_id "%MakeDate") expr_true expr_false
                expr_false));
 ("%MakeDay", property_data
              (data_intro (expr_id "%MakeDay") expr_true expr_false
               expr_false));
 ("%MakeGetter", property_data
                 (data_intro (expr_id "%MakeGetter") expr_true expr_false
                  expr_false));
 ("%MakeSetter", property_data
                 (data_intro (expr_id "%MakeSetter") expr_true expr_false
                  expr_false));
 ("%MakeTime", property_data
               (data_intro (expr_id "%MakeTime") expr_true expr_false
                expr_false));
 ("%MakeTypeError", property_data
                    (data_intro (expr_id "%MakeTypeError") expr_true
                     expr_false expr_false));
 ("%Math", property_data
           (data_intro (expr_id "%Math") expr_true expr_false expr_false));
 ("%MonthFromTime", property_data
                    (data_intro (expr_id "%MonthFromTime") expr_true
                     expr_false expr_false));
 ("%NativeErrorConstructor", property_data
                             (data_intro (expr_id "%NativeErrorConstructor")
                              expr_true expr_false expr_false));
 ("%NumberConstructor", property_data
                        (data_intro (expr_id "%NumberConstructor") expr_true
                         expr_false expr_false));
 ("%NumberGlobalFuncObj", property_data
                          (data_intro (expr_id "%NumberGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%NumberProto", property_data
                  (data_intro (expr_id "%NumberProto") expr_true expr_false
                   expr_false));
 ("%ObjectConstructor", property_data
                        (data_intro (expr_id "%ObjectConstructor") expr_true
                         expr_false expr_false));
 ("%ObjectGlobalFuncObj", property_data
                          (data_intro (expr_id "%ObjectGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%ObjectProto", property_data
                  (data_intro (expr_id "%ObjectProto") expr_true expr_false
                   expr_false));
 ("%ObjectTypeCheck", property_data
                      (data_intro (expr_id "%ObjectTypeCheck") expr_true
                       expr_false expr_false));
 ("%PostDecrement", property_data
                    (data_intro (expr_id "%PostDecrement") expr_true
                     expr_false expr_false));
 ("%PostIncrement", property_data
                    (data_intro (expr_id "%PostIncrement") expr_true
                     expr_false expr_false));
 ("%PostfixOp", property_data
                (data_intro (expr_id "%PostfixOp") expr_true expr_false
                 expr_false));
 ("%PrefixDecrement", property_data
                      (data_intro (expr_id "%PrefixDecrement") expr_true
                       expr_false expr_false));
 ("%PrefixIncrement", property_data
                      (data_intro (expr_id "%PrefixIncrement") expr_true
                       expr_false expr_false));
 ("%PrefixOp", property_data
               (data_intro (expr_id "%PrefixOp") expr_true expr_false
                expr_false));
 ("%PrimAdd", property_data
              (data_intro (expr_id "%PrimAdd") expr_true expr_false
               expr_false));
 ("%PrimMultOp", property_data
                 (data_intro (expr_id "%PrimMultOp") expr_true expr_false
                  expr_false));
 ("%PrimNew", property_data
              (data_intro (expr_id "%PrimNew") expr_true expr_false
               expr_false));
 ("%PrimSub", property_data
              (data_intro (expr_id "%PrimSub") expr_true expr_false
               expr_false));
 ("%PropAccessorCheck", property_data
                        (data_intro (expr_id "%PropAccessorCheck") expr_true
                         expr_false expr_false));
 ("%RangeErrorConstructor", property_data
                            (data_intro (expr_id "%RangeErrorConstructor")
                             expr_true expr_false expr_false));
 ("%RangeErrorGlobalFuncObj", property_data
                              (data_intro
                               (expr_id "%RangeErrorGlobalFuncObj") expr_true
                               expr_false expr_false));
 ("%RangeErrorProto", property_data
                      (data_intro (expr_id "%RangeErrorProto") expr_true
                       expr_false expr_false));
 ("%ReferenceErrorConstructor", property_data
                                (data_intro
                                 (expr_id "%ReferenceErrorConstructor")
                                 expr_true expr_false expr_false));
 ("%ReferenceErrorGlobalFuncObj", property_data
                                  (data_intro
                                   (expr_id "%ReferenceErrorGlobalFuncObj")
                                   expr_true expr_false expr_false));
 ("%ReferenceErrorProto", property_data
                          (data_intro (expr_id "%ReferenceErrorProto")
                           expr_true expr_false expr_false));
 ("%RegExpConstructor", property_data
                        (data_intro (expr_id "%RegExpConstructor") expr_true
                         expr_false expr_false));
 ("%RegExpGlobalFuncObj", property_data
                          (data_intro (expr_id "%RegExpGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%RegExpProto", property_data
                  (data_intro (expr_id "%RegExpProto") expr_true expr_false
                   expr_false));
 ("%SetterValue", property_data
                  (data_intro (expr_id "%SetterValue") expr_true expr_false
                   expr_false));
 ("%SignedRightShift", property_data
                       (data_intro (expr_id "%SignedRightShift") expr_true
                        expr_false expr_false));
 ("%StringConstructor", property_data
                        (data_intro (expr_id "%StringConstructor") expr_true
                         expr_false expr_false));
 ("%StringGlobalFuncObj", property_data
                          (data_intro (expr_id "%StringGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%StringIndexOf", property_data
                    (data_intro (expr_id "%StringIndexOf") expr_true
                     expr_false expr_false));
 ("%StringIndexOflambda", property_data
                          (data_intro (expr_id "%StringIndexOflambda")
                           expr_true expr_false expr_false));
 ("%StringIndices", property_data
                    (data_intro (expr_id "%StringIndices") expr_true
                     expr_false expr_false));
 ("%StringLastIndexOf", property_data
                        (data_intro (expr_id "%StringLastIndexOf") expr_true
                         expr_false expr_false));
 ("%StringProto", property_data
                  (data_intro (expr_id "%StringProto") expr_true expr_false
                   expr_false));
 ("%SyntaxError", property_data
                  (data_intro (expr_id "%SyntaxError") expr_true expr_false
                   expr_false));
 ("%SyntaxErrorConstructor", property_data
                             (data_intro (expr_id "%SyntaxErrorConstructor")
                              expr_true expr_false expr_false));
 ("%SyntaxErrorGlobalFuncObj", property_data
                               (data_intro
                                (expr_id "%SyntaxErrorGlobalFuncObj")
                                expr_true expr_false expr_false));
 ("%SyntaxErrorProto", property_data
                       (data_intro (expr_id "%SyntaxErrorProto") expr_true
                        expr_false expr_false));
 ("%ThrowReferenceError", property_data
                          (data_intro (expr_id "%ThrowReferenceError")
                           expr_true expr_false expr_false));
 ("%ThrowSyntaxError", property_data
                       (data_intro (expr_id "%ThrowSyntaxError") expr_true
                        expr_false expr_false));
 ("%ThrowTypeError", property_data
                     (data_intro (expr_id "%ThrowTypeError") expr_true
                      expr_false expr_false));
 ("%ThrowTypeErrorFun", property_data
                        (data_intro (expr_id "%ThrowTypeErrorFun") expr_true
                         expr_false expr_false));
 ("%TimeClip", property_data
               (data_intro (expr_id "%TimeClip") expr_true expr_false
                expr_false));
 ("%TimeFromYear", property_data
                   (data_intro (expr_id "%TimeFromYear") expr_true expr_false
                    expr_false));
 ("%TimeWithinDay", property_data
                    (data_intro (expr_id "%TimeWithinDay") expr_true
                     expr_false expr_false));
 ("%ToBoolean", property_data
                (data_intro (expr_id "%ToBoolean") expr_true expr_false
                 expr_false));
 ("%ToInt32", property_data
              (data_intro (expr_id "%ToInt32") expr_true expr_false
               expr_false));
 ("%ToInteger", property_data
                (data_intro (expr_id "%ToInteger") expr_true expr_false
                 expr_false));
 ("%ToJSError", property_data
                (data_intro (expr_id "%ToJSError") expr_true expr_false
                 expr_false));
 ("%ToNumber", property_data
               (data_intro (expr_id "%ToNumber") expr_true expr_false
                expr_false));
 ("%ToObject", property_data
               (data_intro (expr_id "%ToObject") expr_true expr_false
                expr_false));
 ("%ToPrimitive", property_data
                  (data_intro (expr_id "%ToPrimitive") expr_true expr_false
                   expr_false));
 ("%ToPrimitiveHint", property_data
                      (data_intro (expr_id "%ToPrimitiveHint") expr_true
                       expr_false expr_false));
 ("%ToPrimitiveNum", property_data
                     (data_intro (expr_id "%ToPrimitiveNum") expr_true
                      expr_false expr_false));
 ("%ToPrimitiveStr", property_data
                     (data_intro (expr_id "%ToPrimitiveStr") expr_true
                      expr_false expr_false));
 ("%ToString", property_data
               (data_intro (expr_id "%ToString") expr_true expr_false
                expr_false));
 ("%ToUint", property_data
             (data_intro (expr_id "%ToUint") expr_true expr_false expr_false));
 ("%ToUint16", property_data
               (data_intro (expr_id "%ToUint16") expr_true expr_false
                expr_false));
 ("%ToUint32", property_data
               (data_intro (expr_id "%ToUint32") expr_true expr_false
                expr_false));
 ("%TypeError", property_data
                (data_intro (expr_id "%TypeError") expr_true expr_false
                 expr_false));
 ("%TypeErrorConstructor", property_data
                           (data_intro (expr_id "%TypeErrorConstructor")
                            expr_true expr_false expr_false));
 ("%TypeErrorGlobalFuncObj", property_data
                             (data_intro (expr_id "%TypeErrorGlobalFuncObj")
                              expr_true expr_false expr_false));
 ("%TypeErrorProto", property_data
                     (data_intro (expr_id "%TypeErrorProto") expr_true
                      expr_false expr_false));
 ("%Typeof", property_data
             (data_intro (expr_id "%Typeof") expr_true expr_false expr_false));
 ("%URIErrorConstructor", property_data
                          (data_intro (expr_id "%URIErrorConstructor")
                           expr_true expr_false expr_false));
 ("%URIErrorGlobalFuncObj", property_data
                            (data_intro (expr_id "%URIErrorGlobalFuncObj")
                             expr_true expr_false expr_false));
 ("%URIErrorProto", property_data
                    (data_intro (expr_id "%URIErrorProto") expr_true
                     expr_false expr_false));
 ("%UTC", property_data
          (data_intro (expr_id "%UTC") expr_true expr_false expr_false));
 ("%UnaryNeg", property_data
               (data_intro (expr_id "%UnaryNeg") expr_true expr_false
                expr_false));
 ("%UnaryPlus", property_data
                (data_intro (expr_id "%UnaryPlus") expr_true expr_false
                 expr_false));
 ("%UnboundId", property_data
                (data_intro (expr_id "%UnboundId") expr_true expr_false
                 expr_false));
 ("%UnsignedRightShift", property_data
                         (data_intro (expr_id "%UnsignedRightShift")
                          expr_true expr_false expr_false));
 ("%UnwritableDispatch", property_data
                         (data_intro (expr_id "%UnwritableDispatch")
                          expr_true expr_false expr_false));
 ("%YearFromTime", property_data
                   (data_intro (expr_id "%YearFromTime") expr_true expr_false
                    expr_false));
 ("%acos", property_data
           (data_intro (expr_id "%acos") expr_true expr_false expr_false));
 ("%acosLambda", property_data
                 (data_intro (expr_id "%acosLambda") expr_true expr_false
                  expr_false));
 ("%aiolambda", property_data
                (data_intro (expr_id "%aiolambda") expr_true expr_false
                 expr_false));
 ("%aliolambda", property_data
                 (data_intro (expr_id "%aliolambda") expr_true expr_false
                  expr_false));
 ("%apply", property_data
            (data_intro (expr_id "%apply") expr_true expr_false expr_false));
 ("%applylambda", property_data
                  (data_intro (expr_id "%applylambda") expr_true expr_false
                   expr_false));
 ("%arrayIndexOf", property_data
                   (data_intro (expr_id "%arrayIndexOf") expr_true expr_false
                    expr_false));
 ("%arrayLastIndexOf", property_data
                       (data_intro (expr_id "%arrayLastIndexOf") expr_true
                        expr_false expr_false));
 ("%arrayTLSlambda", property_data
                     (data_intro (expr_id "%arrayTLSlambda") expr_true
                      expr_false expr_false));
 ("%arrayToLocaleString", property_data
                          (data_intro (expr_id "%arrayToLocaleString")
                           expr_true expr_false expr_false));
 ("%arrayToString", property_data
                    (data_intro (expr_id "%arrayToString") expr_true
                     expr_false expr_false));
 ("%arrayToStringlambda", property_data
                          (data_intro (expr_id "%arrayToStringlambda")
                           expr_true expr_false expr_false));
 ("%asin", property_data
           (data_intro (expr_id "%asin") expr_true expr_false expr_false));
 ("%asinLambda", property_data
                 (data_intro (expr_id "%asinLambda") expr_true expr_false
                  expr_false));
 ("%atan", property_data
           (data_intro (expr_id "%atan") expr_true expr_false expr_false));
 ("%atan2", property_data
            (data_intro (expr_id "%atan2") expr_true expr_false expr_false));
 ("%atan2Lambda", property_data
                  (data_intro (expr_id "%atan2Lambda") expr_true expr_false
                   expr_false));
 ("%atanLambda", property_data
                 (data_intro (expr_id "%atanLambda") expr_true expr_false
                  expr_false));
 ("%bind", property_data
           (data_intro (expr_id "%bind") expr_true expr_false expr_false));
 ("%bindLambda", property_data
                 (data_intro (expr_id "%bindLambda") expr_true expr_false
                  expr_false));
 ("%booleanToString", property_data
                      (data_intro (expr_id "%booleanToString") expr_true
                       expr_false expr_false));
 ("%booleanToStringlambda", property_data
                            (data_intro (expr_id "%booleanToStringlambda")
                             expr_true expr_false expr_false));
 ("%booleanValueOf", property_data
                     (data_intro (expr_id "%booleanValueOf") expr_true
                      expr_false expr_false));
 ("%call", property_data
           (data_intro (expr_id "%call") expr_true expr_false expr_false));
 ("%calllambda", property_data
                 (data_intro (expr_id "%calllambda") expr_true expr_false
                  expr_false));
 ("%charat", property_data
             (data_intro (expr_id "%charat") expr_true expr_false expr_false));
 ("%charatlambda", property_data
                   (data_intro (expr_id "%charatlambda") expr_true expr_false
                    expr_false));
 ("%charcodeat", property_data
                 (data_intro (expr_id "%charcodeat") expr_true expr_false
                  expr_false));
 ("%charcodeatlambda", property_data
                       (data_intro (expr_id "%charcodeatlambda") expr_true
                        expr_false expr_false));
 ("%concat", property_data
             (data_intro (expr_id "%concat") expr_true expr_false expr_false));
 ("%concatLambda", property_data
                   (data_intro (expr_id "%concatLambda") expr_true expr_false
                    expr_false));
 ("%configurableEval", property_data
                       (data_intro (expr_id "%configurableEval") expr_true
                        expr_false expr_false));
 ("%console", property_data
              (data_intro (expr_id "%console") expr_true expr_false
               expr_false));
 ("%cos", property_data
          (data_intro (expr_id "%cos") expr_true expr_false expr_false));
 ("%cosLambda", property_data
                (data_intro (expr_id "%cosLambda") expr_true expr_false
                 expr_false));
 ("%create", property_data
             (data_intro (expr_id "%create") expr_true expr_false expr_false));
 ("%createLambda", property_data
                   (data_intro (expr_id "%createLambda") expr_true expr_false
                    expr_false));
 ("%dateGetTimezoneOffset", property_data
                            (data_intro (expr_id "%dateGetTimezoneOffset")
                             expr_true expr_false expr_false));
 ("%dateGetTimezoneOffsetLambda", property_data
                                  (data_intro
                                   (expr_id "%dateGetTimezoneOffsetLambda")
                                   expr_true expr_false expr_false));
 ("%dateToString", property_data
                   (data_intro (expr_id "%dateToString") expr_true expr_false
                    expr_false));
 ("%dateToStringLambda", property_data
                         (data_intro (expr_id "%dateToStringLambda")
                          expr_true expr_false expr_false));
 ("%dateValueOf", property_data
                  (data_intro (expr_id "%dateValueOf") expr_true expr_false
                   expr_false));
 ("%dateValueOfLambda", property_data
                        (data_intro (expr_id "%dateValueOfLambda") expr_true
                         expr_false expr_false));
 ("%dategetDate", property_data
                  (data_intro (expr_id "%dategetDate") expr_true expr_false
                   expr_false));
 ("%dategetDateLambda", property_data
                        (data_intro (expr_id "%dategetDateLambda") expr_true
                         expr_false expr_false));
 ("%dategetDay", property_data
                 (data_intro (expr_id "%dategetDay") expr_true expr_false
                  expr_false));
 ("%dategetDayLambda", property_data
                       (data_intro (expr_id "%dategetDayLambda") expr_true
                        expr_false expr_false));
 ("%decodeURI", property_data
                (data_intro (expr_id "%decodeURI") expr_true expr_false
                 expr_false));
 ("%decodeURIComponent", property_data
                         (data_intro (expr_id "%decodeURIComponent")
                          expr_true expr_false expr_false));
 ("%decodeURIComponentLambda", property_data
                               (data_intro
                                (expr_id "%decodeURIComponentLambda")
                                expr_true expr_false expr_false));
 ("%decodeURILambda", property_data
                      (data_intro (expr_id "%decodeURILambda") expr_true
                       expr_false expr_false));
 ("%define15Property", property_data
                       (data_intro (expr_id "%define15Property") expr_true
                        expr_false expr_false));
 ("%defineGlobalAccessors", property_data
                            (data_intro (expr_id "%defineGlobalAccessors")
                             expr_true expr_false expr_false));
 ("%defineGlobalVar", property_data
                      (data_intro (expr_id "%defineGlobalVar") expr_true
                       expr_false expr_false));
 ("%defineNYIProperty", property_data
                        (data_intro (expr_id "%defineNYIProperty") expr_true
                         expr_false expr_false));
 ("%defineOwnProperty", property_data
                        (data_intro (expr_id "%defineOwnProperty") expr_true
                         expr_false expr_false));
 ("%defineProperties", property_data
                       (data_intro (expr_id "%defineProperties") expr_true
                        expr_false expr_false));
 ("%definePropertiesLambda", property_data
                             (data_intro (expr_id "%definePropertiesLambda")
                              expr_true expr_false expr_false));
 ("%defineProperty", property_data
                     (data_intro (expr_id "%defineProperty") expr_true
                      expr_false expr_false));
 ("%definePropertylambda", property_data
                           (data_intro (expr_id "%definePropertylambda")
                            expr_true expr_false expr_false));
 ("%encodeURI", property_data
                (data_intro (expr_id "%encodeURI") expr_true expr_false
                 expr_false));
 ("%encodeURIComponent", property_data
                         (data_intro (expr_id "%encodeURIComponent")
                          expr_true expr_false expr_false));
 ("%encodeURIComponentLambda", property_data
                               (data_intro
                                (expr_id "%encodeURIComponentLambda")
                                expr_true expr_false expr_false));
 ("%encodeURILambda", property_data
                      (data_intro (expr_id "%encodeURILambda") expr_true
                       expr_false expr_false));
 ("%escape", property_data
             (data_intro (expr_id "%escape") expr_true expr_false expr_false));
 ("%escapeLambda", property_data
                   (data_intro (expr_id "%escapeLambda") expr_true expr_false
                    expr_false));
 ("%ets", property_data
          (data_intro (expr_id "%ets") expr_true expr_false expr_false));
 ("%etslambda", property_data
                (data_intro (expr_id "%etslambda") expr_true expr_false
                 expr_false));
 ("%eval", property_data
           (data_intro (expr_id "%eval") expr_true expr_false expr_false));
 ("%evallambda", property_data
                 (data_intro (expr_id "%evallambda") expr_true expr_false
                  expr_false));
 ("%every", property_data
            (data_intro (expr_id "%every") expr_true expr_false expr_false));
 ("%everylambda", property_data
                  (data_intro (expr_id "%everylambda") expr_true expr_false
                   expr_false));
 ("%exp", property_data
          (data_intro (expr_id "%exp") expr_true expr_false expr_false));
 ("%explambda", property_data
                (data_intro (expr_id "%explambda") expr_true expr_false
                 expr_false));
 ("%filter", property_data
             (data_intro (expr_id "%filter") expr_true expr_false expr_false));
 ("%filterlambda", property_data
                   (data_intro (expr_id "%filterlambda") expr_true expr_false
                    expr_false));
 ("%foreach", property_data
              (data_intro (expr_id "%foreach") expr_true expr_false
               expr_false));
 ("%foreachlambda", property_data
                    (data_intro (expr_id "%foreachlambda") expr_true
                     expr_false expr_false));
 ("%freeze", property_data
             (data_intro (expr_id "%freeze") expr_true expr_false expr_false));
 ("%freezelambda", property_data
                   (data_intro (expr_id "%freezelambda") expr_true expr_false
                    expr_false));
 ("%fromCharCode", property_data
                   (data_intro (expr_id "%fromCharCode") expr_true expr_false
                    expr_false));
 ("%fromcclambda", property_data
                   (data_intro (expr_id "%fromcclambda") expr_true expr_false
                    expr_false));
 ("%functionToString", property_data
                       (data_intro (expr_id "%functionToString") expr_true
                        expr_false expr_false));
 ("%functionToStringlambda", property_data
                             (data_intro (expr_id "%functionToStringlambda")
                              expr_true expr_false expr_false));
 ("%getCurrentUTC", property_data
                    (data_intro (expr_id "%getCurrentUTC") expr_true
                     expr_false expr_false));
 ("%getMonth", property_data
               (data_intro (expr_id "%getMonth") expr_true expr_false
                expr_false));
 ("%getMonthlambda", property_data
                     (data_intro (expr_id "%getMonthlambda") expr_true
                      expr_false expr_false));
 ("%getYear", property_data
              (data_intro (expr_id "%getYear") expr_true expr_false
               expr_false));
 ("%getYearlambda", property_data
                    (data_intro (expr_id "%getYearlambda") expr_true
                     expr_false expr_false));
 ("%global", property_data
             (data_intro (expr_id "%global") expr_true expr_false expr_false));
 ("%globalContext", property_data
                    (data_intro (expr_id "%globalContext") expr_true
                     expr_false expr_false));
 ("%gopd", property_data
           (data_intro (expr_id "%gopd") expr_true expr_false expr_false));
 ("%gopdLambda", property_data
                 (data_intro (expr_id "%gopdLambda") expr_true expr_false
                  expr_false));
 ("%gopn", property_data
           (data_intro (expr_id "%gopn") expr_true expr_false expr_false));
 ("%gopnLambda", property_data
                 (data_intro (expr_id "%gopnLambda") expr_true expr_false
                  expr_false));
 ("%gpo", property_data
          (data_intro (expr_id "%gpo") expr_true expr_false expr_false));
 ("%gpoLambda", property_data
                (data_intro (expr_id "%gpoLambda") expr_true expr_false
                 expr_false));
 ("%hasOwnProperty", property_data
                     (data_intro (expr_id "%hasOwnProperty") expr_true
                      expr_false expr_false));
 ("%hasOwnPropertylambda", property_data
                           (data_intro (expr_id "%hasOwnPropertylambda")
                            expr_true expr_false expr_false));
 ("%in", property_data
         (data_intro (expr_id "%in") expr_true expr_false expr_false));
 ("%instanceof", property_data
                 (data_intro (expr_id "%instanceof") expr_true expr_false
                  expr_false));
 ("%isExtensible", property_data
                   (data_intro (expr_id "%isExtensible") expr_true expr_false
                    expr_false));
 ("%isExtensibleLambda", property_data
                         (data_intro (expr_id "%isExtensibleLambda")
                          expr_true expr_false expr_false));
 ("%isFinite", property_data
               (data_intro (expr_id "%isFinite") expr_true expr_false
                expr_false));
 ("%isFiniteLambda", property_data
                     (data_intro (expr_id "%isFiniteLambda") expr_true
                      expr_false expr_false));
 ("%isFrozen", property_data
               (data_intro (expr_id "%isFrozen") expr_true expr_false
                expr_false));
 ("%isFrozenLambda", property_data
                     (data_intro (expr_id "%isFrozenLambda") expr_true
                      expr_false expr_false));
 ("%isNaN", property_data
            (data_intro (expr_id "%isNaN") expr_true expr_false expr_false));
 ("%isNaNlambda", property_data
                  (data_intro (expr_id "%isNaNlambda") expr_true expr_false
                   expr_false));
 ("%isPrototypeOf", property_data
                    (data_intro (expr_id "%isPrototypeOf") expr_true
                     expr_false expr_false));
 ("%isSealed", property_data
               (data_intro (expr_id "%isSealed") expr_true expr_false
                expr_false));
 ("%isSealedLambda", property_data
                     (data_intro (expr_id "%isSealedLambda") expr_true
                      expr_false expr_false));
 ("%isUnbound", property_data
                (data_intro (expr_id "%isUnbound") expr_true expr_false
                 expr_false));
 ("%join", property_data
           (data_intro (expr_id "%join") expr_true expr_false expr_false));
 ("%joinlambda", property_data
                 (data_intro (expr_id "%joinlambda") expr_true expr_false
                  expr_false));
 ("%keys", property_data
           (data_intro (expr_id "%keys") expr_true expr_false expr_false));
 ("%keysLambda", property_data
                 (data_intro (expr_id "%keysLambda") expr_true expr_false
                  expr_false));
 ("%len", property_data
          (data_intro (expr_id "%len") expr_true expr_false expr_false));
 ("%localeCompare", property_data
                    (data_intro (expr_id "%localeCompare") expr_true
                     expr_false expr_false));
 ("%localeCompareLambda", property_data
                          (data_intro (expr_id "%localeCompareLambda")
                           expr_true expr_false expr_false));
 ("%log", property_data
          (data_intro (expr_id "%log") expr_true expr_false expr_false));
 ("%logLambda", property_data
                (data_intro (expr_id "%logLambda") expr_true expr_false
                 expr_false));
 ("%makeContextVarDefiner", property_data
                            (data_intro (expr_id "%makeContextVarDefiner")
                             expr_true expr_false expr_false));
 ("%makeEnvGetter", property_data
                    (data_intro (expr_id "%makeEnvGetter") expr_true
                     expr_false expr_false));
 ("%makeEnvSetter", property_data
                    (data_intro (expr_id "%makeEnvSetter") expr_true
                     expr_false expr_false));
 ("%makeGlobalEnv", property_data
                    (data_intro (expr_id "%makeGlobalEnv") expr_true
                     expr_false expr_false));
 ("%makeWithContext", property_data
                      (data_intro (expr_id "%makeWithContext") expr_true
                       expr_false expr_false));
 ("%map", property_data
          (data_intro (expr_id "%map") expr_true expr_false expr_false));
 ("%maplambda", property_data
                (data_intro (expr_id "%maplambda") expr_true expr_false
                 expr_false));
 ("%mathAbs", property_data
              (data_intro (expr_id "%mathAbs") expr_true expr_false
               expr_false));
 ("%mathAbsLambda", property_data
                    (data_intro (expr_id "%mathAbsLambda") expr_true
                     expr_false expr_false));
 ("%mathCeil", property_data
               (data_intro (expr_id "%mathCeil") expr_true expr_false
                expr_false));
 ("%mathCeilLambda", property_data
                     (data_intro (expr_id "%mathCeilLambda") expr_true
                      expr_false expr_false));
 ("%mathFloor", property_data
                (data_intro (expr_id "%mathFloor") expr_true expr_false
                 expr_false));
 ("%mathFloorLambda", property_data
                      (data_intro (expr_id "%mathFloorLambda") expr_true
                       expr_false expr_false));
 ("%mathLog", property_data
              (data_intro (expr_id "%mathLog") expr_true expr_false
               expr_false));
 ("%mathLogLambda", property_data
                    (data_intro (expr_id "%mathLogLambda") expr_true
                     expr_false expr_false));
 ("%mathMax", property_data
              (data_intro (expr_id "%mathMax") expr_true expr_false
               expr_false));
 ("%mathMaxLambda", property_data
                    (data_intro (expr_id "%mathMaxLambda") expr_true
                     expr_false expr_false));
 ("%mathMin", property_data
              (data_intro (expr_id "%mathMin") expr_true expr_false
               expr_false));
 ("%mathMinLambda", property_data
                    (data_intro (expr_id "%mathMinLambda") expr_true
                     expr_false expr_false));
 ("%mathPow", property_data
              (data_intro (expr_id "%mathPow") expr_true expr_false
               expr_false));
 ("%mathPowLambda", property_data
                    (data_intro (expr_id "%mathPowLambda") expr_true
                     expr_false expr_false));
 ("%max", property_data
          (data_intro (expr_id "%max") expr_true expr_false expr_false));
 ("%maybeDirectEval", property_data
                      (data_intro (expr_id "%maybeDirectEval") expr_true
                       expr_false expr_false));
 ("%min", property_data
          (data_intro (expr_id "%min") expr_true expr_false expr_false));
 ("%minMaxLambda", property_data
                   (data_intro (expr_id "%minMaxLambda") expr_true expr_false
                    expr_false));
 ("%mkArgsObj", property_data
                (data_intro (expr_id "%mkArgsObj") expr_true expr_false
                 expr_false));
 ("%mkArgsObjBase", property_data
                    (data_intro (expr_id "%mkArgsObjBase") expr_true
                     expr_false expr_false));
 ("%mkNewArgsObj", property_data
                   (data_intro (expr_id "%mkNewArgsObj") expr_true expr_false
                    expr_false));
 ("%msPerDay", property_data
               (data_intro (expr_id "%msPerDay") expr_true expr_false
                expr_false));
 ("%msPerHour", property_data
                (data_intro (expr_id "%msPerHour") expr_true expr_false
                 expr_false));
 ("%msPerMin", property_data
               (data_intro (expr_id "%msPerMin") expr_true expr_false
                expr_false));
 ("%msPerSecond", property_data
                  (data_intro (expr_id "%msPerSecond") expr_true expr_false
                   expr_false));
 ("%nonstrictContext", property_data
                       (data_intro (expr_id "%nonstrictContext") expr_true
                        expr_false expr_false));
 ("%numTLS", property_data
             (data_intro (expr_id "%numTLS") expr_true expr_false expr_false));
 ("%numTLSLambda", property_data
                   (data_intro (expr_id "%numTLSLambda") expr_true expr_false
                    expr_false));
 ("%numToStringAbstract", property_data
                          (data_intro (expr_id "%numToStringAbstract")
                           expr_true expr_false expr_false));
 ("%numValueOf", property_data
                 (data_intro (expr_id "%numValueOf") expr_true expr_false
                  expr_false));
 ("%numberToString", property_data
                     (data_intro (expr_id "%numberToString") expr_true
                      expr_false expr_false));
 ("%numberToStringlambda", property_data
                           (data_intro (expr_id "%numberToStringlambda")
                            expr_true expr_false expr_false));
 ("%objectToString", property_data
                     (data_intro (expr_id "%objectToString") expr_true
                      expr_false expr_false));
 ("%objectToStringlambda", property_data
                           (data_intro (expr_id "%objectToStringlambda")
                            expr_true expr_false expr_false));
 ("%oneArgObj", property_data
                (data_intro (expr_id "%oneArgObj") expr_true expr_false
                 expr_false));
 ("%parse", property_data
            (data_intro (expr_id "%parse") expr_true expr_false expr_false));
 ("%parseFloat", property_data
                 (data_intro (expr_id "%parseFloat") expr_true expr_false
                  expr_false));
 ("%parseFloatLambda", property_data
                       (data_intro (expr_id "%parseFloatLambda") expr_true
                        expr_false expr_false));
 ("%parseInt", property_data
               (data_intro (expr_id "%parseInt") expr_true expr_false
                expr_false));
 ("%parseIntlambda", property_data
                     (data_intro (expr_id "%parseIntlambda") expr_true
                      expr_false expr_false));
 ("%pop", property_data
          (data_intro (expr_id "%pop") expr_true expr_false expr_false));
 ("%poplambda", property_data
                (data_intro (expr_id "%poplambda") expr_true expr_false
                 expr_false));
 ("%preventExtensions", property_data
                        (data_intro (expr_id "%preventExtensions") expr_true
                         expr_false expr_false));
 ("%preventExtensionsLambda", property_data
                              (data_intro
                               (expr_id "%preventExtensionsLambda") expr_true
                               expr_false expr_false));
 ("%primEach", property_data
               (data_intro (expr_id "%primEach") expr_true expr_false
                expr_false));
 ("%print", property_data
            (data_intro (expr_id "%print") expr_true expr_false expr_false));
 ("%printlambda", property_data
                  (data_intro (expr_id "%printlambda") expr_true expr_false
                   expr_false));
 ("%propEnumlambda", property_data
                     (data_intro (expr_id "%propEnumlambda") expr_true
                      expr_false expr_false));
 ("%propertyIsEnumerable", property_data
                           (data_intro (expr_id "%propertyIsEnumerable")
                            expr_true expr_false expr_false));
 ("%propertyNames", property_data
                    (data_intro (expr_id "%propertyNames") expr_true
                     expr_false expr_false));
 ("%protoOfField", property_data
                   (data_intro (expr_id "%protoOfField") expr_true expr_false
                    expr_false));
 ("%push", property_data
           (data_intro (expr_id "%push") expr_true expr_false expr_false));
 ("%pushlambda", property_data
                 (data_intro (expr_id "%pushlambda") expr_true expr_false
                  expr_false));
 ("%random", property_data
             (data_intro (expr_id "%random") expr_true expr_false expr_false));
 ("%randomLambda", property_data
                   (data_intro (expr_id "%randomLambda") expr_true expr_false
                    expr_false));
 ("%reduce", property_data
             (data_intro (expr_id "%reduce") expr_true expr_false expr_false));
 ("%reduceRight", property_data
                  (data_intro (expr_id "%reduceRight") expr_true expr_false
                   expr_false));
 ("%reduceRightLambda", property_data
                        (data_intro (expr_id "%reduceRightLambda") expr_true
                         expr_false expr_false));
 ("%reducelambda", property_data
                   (data_intro (expr_id "%reducelambda") expr_true expr_false
                    expr_false));
 ("%replace", property_data
              (data_intro (expr_id "%replace") expr_true expr_false
               expr_false));
 ("%replacelambda", property_data
                    (data_intro (expr_id "%replacelambda") expr_true
                     expr_false expr_false));
 ("%resolveThis", property_data
                  (data_intro (expr_id "%resolveThis") expr_true expr_false
                   expr_false));
 ("%reverse", property_data
              (data_intro (expr_id "%reverse") expr_true expr_false
               expr_false));
 ("%reverselambda", property_data
                    (data_intro (expr_id "%reverselambda") expr_true
                     expr_false expr_false));
 ("%round", property_data
            (data_intro (expr_id "%round") expr_true expr_false expr_false));
 ("%roundLambda", property_data
                  (data_intro (expr_id "%roundLambda") expr_true expr_false
                   expr_false));
 ("%seal", property_data
           (data_intro (expr_id "%seal") expr_true expr_false expr_false));
 ("%sealLambda", property_data
                 (data_intro (expr_id "%sealLambda") expr_true expr_false
                  expr_false));
 ("%set-property", property_data
                   (data_intro (expr_id "%set-property") expr_true expr_false
                    expr_false));
 ("%shift", property_data
            (data_intro (expr_id "%shift") expr_true expr_false expr_false));
 ("%shiftlambda", property_data
                  (data_intro (expr_id "%shiftlambda") expr_true expr_false
                   expr_false));
 ("%sin", property_data
          (data_intro (expr_id "%sin") expr_true expr_false expr_false));
 ("%sinLambda", property_data
                (data_intro (expr_id "%sinLambda") expr_true expr_false
                 expr_false));
 ("%slice", property_data
            (data_intro (expr_id "%slice") expr_true expr_false expr_false));
 ("%slice_internal", property_data
                     (data_intro (expr_id "%slice_internal") expr_true
                      expr_false expr_false));
 ("%slicelambda", property_data
                  (data_intro (expr_id "%slicelambda") expr_true expr_false
                   expr_false));
 ("%sliolambda", property_data
                 (data_intro (expr_id "%sliolambda") expr_true expr_false
                  expr_false));
 ("%some", property_data
           (data_intro (expr_id "%some") expr_true expr_false expr_false));
 ("%somelambda", property_data
                 (data_intro (expr_id "%somelambda") expr_true expr_false
                  expr_false));
 ("%sort", property_data
           (data_intro (expr_id "%sort") expr_true expr_false expr_false));
 ("%sortlambda", property_data
                 (data_intro (expr_id "%sortlambda") expr_true expr_false
                  expr_false));
 ("%splice", property_data
             (data_intro (expr_id "%splice") expr_true expr_false expr_false));
 ("%splicelambda", property_data
                   (data_intro (expr_id "%splicelambda") expr_true expr_false
                    expr_false));
 ("%split", property_data
            (data_intro (expr_id "%split") expr_true expr_false expr_false));
 ("%splitLambda", property_data
                  (data_intro (expr_id "%splitLambda") expr_true expr_false
                   expr_false));
 ("%sqrt", property_data
           (data_intro (expr_id "%sqrt") expr_true expr_false expr_false));
 ("%sqrtLambda", property_data
                 (data_intro (expr_id "%sqrtLambda") expr_true expr_false
                  expr_false));
 ("%strconcat", property_data
                (data_intro (expr_id "%strconcat") expr_true expr_false
                 expr_false));
 ("%strconcatlambda", property_data
                      (data_intro (expr_id "%strconcatlambda") expr_true
                       expr_false expr_false));
 ("%strictContext", property_data
                    (data_intro (expr_id "%strictContext") expr_true
                     expr_false expr_false));
 ("%stringSlice", property_data
                  (data_intro (expr_id "%stringSlice") expr_true expr_false
                   expr_false));
 ("%stringSliceLambda", property_data
                        (data_intro (expr_id "%stringSliceLambda") expr_true
                         expr_false expr_false));
 ("%stringToString", property_data
                     (data_intro (expr_id "%stringToString") expr_true
                      expr_false expr_false));
 ("%stringToStringlambda", property_data
                           (data_intro (expr_id "%stringToStringlambda")
                            expr_true expr_false expr_false));
 ("%stringValueOf", property_data
                    (data_intro (expr_id "%stringValueOf") expr_true
                     expr_false expr_false));
 ("%substring", property_data
                (data_intro (expr_id "%substring") expr_true expr_false
                 expr_false));
 ("%substringlambda", property_data
                      (data_intro (expr_id "%substringlambda") expr_true
                       expr_false expr_false));
 ("%tan", property_data
          (data_intro (expr_id "%tan") expr_true expr_false expr_false));
 ("%tanLambda", property_data
                (data_intro (expr_id "%tanLambda") expr_true expr_false
                 expr_false));
 ("%test", property_data
           (data_intro (expr_id "%test") expr_true expr_false expr_false));
 ("%testlambda", property_data
                 (data_intro (expr_id "%testlambda") expr_true expr_false
                  expr_false));
 ("%this", property_data
           (data_intro (expr_id "%this") expr_true expr_false expr_false));
 ("%throwUnboundIDErrors", property_data
                           (data_intro (expr_id "%throwUnboundIDErrors")
                            expr_true expr_false expr_false));
 ("%tlclambda", property_data
                (data_intro (expr_id "%tlclambda") expr_true expr_false
                 expr_false));
 ("%toExponential", property_data
                    (data_intro (expr_id "%toExponential") expr_true
                     expr_false expr_false));
 ("%toExponentialLambda", property_data
                          (data_intro (expr_id "%toExponentialLambda")
                           expr_true expr_false expr_false));
 ("%toFixed", property_data
              (data_intro (expr_id "%toFixed") expr_true expr_false
               expr_false));
 ("%toFixedLambda", property_data
                    (data_intro (expr_id "%toFixedLambda") expr_true
                     expr_false expr_false));
 ("%toLocaleString", property_data
                     (data_intro (expr_id "%toLocaleString") expr_true
                      expr_false expr_false));
 ("%toLocaleStringlambda", property_data
                           (data_intro (expr_id "%toLocaleStringlambda")
                            expr_true expr_false expr_false));
 ("%toLowerCase", property_data
                  (data_intro (expr_id "%toLowerCase") expr_true expr_false
                   expr_false));
 ("%toPrecision", property_data
                  (data_intro (expr_id "%toPrecision") expr_true expr_false
                   expr_false));
 ("%toPrecisionLambda", property_data
                        (data_intro (expr_id "%toPrecisionLambda") expr_true
                         expr_false expr_false));
 ("%toUpperCase", property_data
                  (data_intro (expr_id "%toUpperCase") expr_true expr_false
                   expr_false));
 ("%tuclambda", property_data
                (data_intro (expr_id "%tuclambda") expr_true expr_false
                 expr_false));
 ("%twoArgObj", property_data
                (data_intro (expr_id "%twoArgObj") expr_true expr_false
                 expr_false));
 ("%unescape", property_data
               (data_intro (expr_id "%unescape") expr_true expr_false
                expr_false));
 ("%unescapeLambda", property_data
                     (data_intro (expr_id "%unescapeLambda") expr_true
                      expr_false expr_false));
 ("%unshift", property_data
              (data_intro (expr_id "%unshift") expr_true expr_false
               expr_false));
 ("%unshiftlambda", property_data
                    (data_intro (expr_id "%unshiftlambda") expr_true
                     expr_false expr_false));
 ("%valueOf", property_data
              (data_intro (expr_id "%valueOf") expr_true expr_false
               expr_false));
 ("%valueOfLambda", property_data
                    (data_intro (expr_id "%valueOfLambda") expr_true
                     expr_false expr_false));
 ("%valueOflambda", property_data
                    (data_intro (expr_id "%valueOflambda") expr_true
                     expr_false expr_false));
 ("copy-access-desc", property_data
                      (data_intro (expr_id "copy-access-desc") expr_true
                       expr_false expr_false));
 ("copy-data-desc", property_data
                    (data_intro (expr_id "copy-data-desc") expr_true
                     expr_false expr_false));
 ("copy-when-defined", property_data
                       (data_intro (expr_id "copy-when-defined") expr_true
                        expr_false expr_false));
 ("isAccessorDescriptor", property_data
                          (data_intro (expr_id "isAccessorDescriptor")
                           expr_true expr_false expr_false));
 ("isAccessorField", property_data
                     (data_intro (expr_id "isAccessorField") expr_true
                      expr_false expr_false));
 ("isDataDescriptor", property_data
                      (data_intro (expr_id "isDataDescriptor") expr_true
                       expr_false expr_false));
 ("isDataField", property_data
                 (data_intro (expr_id "isDataField") expr_true expr_false
                  expr_false));
 ("isGenericDescriptor", property_data
                         (data_intro (expr_id "isGenericDescriptor")
                          expr_true expr_false expr_false));
 ("isGenericField", property_data
                    (data_intro (expr_id "isGenericField") expr_true
                     expr_false expr_false))]
.
Definition ex_isAccessorDescriptor := 
expr_let "%or"
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
   (expr_string "undefined")) expr_false expr_true))
.
Definition ex_isAccessorField := 
expr_let "%or"
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_setter (expr_id "obj") (expr_id "field"))
  expr_undefined) expr_false expr_true)
(expr_if (expr_id "%or") (expr_id "%or")
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_attr pattr_getter (expr_id "obj") (expr_id "field"))
   expr_undefined) expr_false expr_true))
.
Definition ex_isDataDescriptor := 
expr_let "%or"
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
   (expr_string "undefined")) expr_false expr_true))
.
Definition ex_isDataField := 
expr_let "%or"
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "obj") (expr_id "field"))
  expr_undefined) expr_false expr_true)
(expr_if (expr_id "%or") (expr_id "%or")
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_attr pattr_writable (expr_id "obj") (expr_id "field"))
   expr_undefined) expr_false expr_true))
.
Definition ex_isGenericDescriptor := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "isAccessorDescriptor") [expr_id "attr-obj"]) expr_false)
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"]) expr_false)
expr_false
.
Definition ex_isGenericField := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "isDataField") [expr_id "obj"; expr_id "field"])
 expr_false)
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "isAccessorField") [expr_id "obj"; expr_id "field"])
 expr_false) expr_false
.
Definition ex_objCode1 :=  expr_undefined .
Definition ex_objCode10 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode11 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode12 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode13 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode14 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode15 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode16 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode17 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode18 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode19 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode2 := 
expr_throw
(expr_app (expr_id "%JSError")
 [expr_object
  (objattrs_intro (expr_string "Object") expr_true
   (expr_id "%ReferenceErrorProto") expr_null expr_undefined) []])
.
Definition ex_objCode20 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode21 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode22 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode23 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode24 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode25 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode26 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode27 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode28 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode29 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode3 := 
expr_throw
(expr_app (expr_id "%JSError")
 [expr_object
  (objattrs_intro (expr_string "Object") expr_true
   (expr_id "%SyntaxErrorProto") expr_null expr_undefined) []])
.
Definition ex_objCode30 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode31 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode32 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode33 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode34 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode35 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode36 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode37 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode38 := 
expr_app (expr_id "%valueOfLambda")
[expr_id "this"; expr_id "args"; expr_id "%StringProto"; expr_string "string"]
.
Definition ex_objCode39 := 
expr_app (expr_id "%valueOfLambda")
[expr_id "this"; expr_id "args"; expr_id "%NumberProto"; expr_string "number"]
.
Definition ex_objCode4 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode40 := 
expr_app (expr_id "%valueOfLambda")
[expr_id "this";
 expr_id "args";
 expr_id "%BooleanProto";
 expr_string "boolean"]
.
Definition ex_objCode5 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode6 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode7 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode8 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_objCode9 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
Definition ex_privAppExprCheck := 
expr_if
(expr_if
 (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "fun"))
  (expr_string "function")) expr_false expr_true)
(expr_app (expr_id "%TypeError") [expr_string "Not a function"])
(expr_app (expr_id "fun") [expr_id "this"; expr_id "args"])
.
Definition ex_privArrayConstructor := 
expr_label "ret"
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
       (expr_op2 binary_op_gt (expr_id "n") (expr_number (JsNumber.of_int 0)))
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
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined)
         [("value", property_data
                    (data_intro
                     (expr_get_field (expr_id "args") (expr_string "0"))
                     expr_true expr_false expr_false));
          ("writable", property_data
                       (data_intro expr_true expr_true expr_false expr_false));
          ("enumerable", property_data
                         (data_intro expr_true expr_true expr_false
                          expr_false));
          ("configurable", property_data
                           (data_intro expr_true expr_true expr_false
                            expr_false))]])
       (expr_break "ret" (expr_id "rtn")))))))))
.
Definition ex_privArrayLengthChange := 
expr_let "oldlen"
(expr_app (expr_id "%ToUint32")
 [expr_get_field (expr_id "arr") (expr_string "length")])
(expr_recc "fix"
 (expr_lambda ["i"]
  (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "oldlen"))
   (expr_seq
    (expr_delete_field (expr_id "arr")
     (expr_op1 unary_op_prim_to_str (expr_id "i")))
    (expr_app (expr_id "fix")
     [expr_op2 binary_op_add (expr_id "i") (expr_number (JsNumber.of_int 1))]))
   expr_undefined)) (expr_app (expr_id "fix") [expr_id "newlen"]))
.
Definition ex_privBitwiseAnd := 
expr_op2 binary_op_band (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_app (expr_id "%ToInt32") [expr_id "r"])
.
Definition ex_privBitwiseInfix := 
expr_let "lnum" (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_let "rnum" (expr_app (expr_id "%ToInt32") [expr_id "r"])
 (expr_app (expr_id "op") [expr_id "lnum"; expr_id "rnum"]))
.
Definition ex_privBitwiseNot := 
expr_let "oldValue" (expr_app (expr_id "%ToInt32") [expr_id "expr"])
(expr_op1 unary_op_bnot (expr_id "oldValue"))
.
Definition ex_privBooleanConstructor := 
expr_let "b"
(expr_app (expr_id "%ToBoolean")
 [expr_get_field (expr_id "args") (expr_string "0")])
(expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
 (expr_id "b")
 (expr_object
  (objattrs_intro (expr_string "Boolean") expr_true (expr_id "%BooleanProto")
   expr_null (expr_id "b")) []))
.
Definition ex_privCheckObjectCoercible := 
expr_if
(expr_let "%or" (expr_op2 binary_op_stx_eq (expr_id "o") expr_undefined)
 (expr_if (expr_id "%or") (expr_id "%or")
  (expr_op2 binary_op_stx_eq (expr_id "o") expr_null)))
(expr_app (expr_id "%TypeError") [expr_string "Not object coercible"])
expr_undefined
.
Definition ex_privCompareOp := 
expr_let "rest"
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
        (expr_op2 binary_op_stx_eq (expr_id "pytype") (expr_string "string"))
        expr_false expr_true)))
     (expr_let "nx" (expr_app (expr_id "%ToNumber") [expr_id "px"])
      (expr_let "ny" (expr_app (expr_id "%ToNumber") [expr_id "py"])
       (expr_seq
        (expr_if
         (expr_let "%or"
          (expr_if (expr_op2 binary_op_stx_eq (expr_id "nx") (expr_id "nx"))
           expr_false expr_true)
          (expr_if (expr_id "%or") (expr_id "%or")
           (expr_if (expr_op2 binary_op_stx_eq (expr_id "ny") (expr_id "ny"))
            expr_false expr_true))) (expr_break "ret" expr_undefined)
         expr_null)
        (expr_seq
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "nx") (expr_id "ny"))
          (expr_break "ret" expr_false) expr_null)
         (expr_seq
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "nx")
            (expr_number (JsNumber.of_int 0))) (expr_break "ret" expr_false)
           expr_null)
          (expr_seq
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "ny")
             (expr_number (JsNumber.of_int 0))) (expr_break "ret" expr_true)
            expr_null)
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
  (expr_app (expr_id "%ToPrimitiveHint") [expr_id "l"; expr_string "number"])
  (expr_let "py"
   (expr_app (expr_id "%ToPrimitiveHint") [expr_id "r"; expr_string "number"])
   (expr_app (expr_id "rest") [expr_id "px"; expr_id "py"])))
 (expr_let "py"
  (expr_app (expr_id "%ToPrimitiveHint") [expr_id "r"; expr_string "number"])
  (expr_let "px"
   (expr_app (expr_id "%ToPrimitiveHint") [expr_id "l"; expr_string "number"])
   (expr_app (expr_id "rest") [expr_id "px"; expr_id "py"]))))
.
Definition ex_privDateConstructor := 
expr_let "calledAsFunction"
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
        (objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
         expr_null (expr_id "clipped")) []))))
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
          (expr_get_field (expr_id "args") (expr_string "3")) expr_undefined)
         (expr_number (JsNumber.of_int 0))
         (expr_app (expr_id "%ToNumber")
          [expr_get_field (expr_id "args") (expr_string "3")]))
        (expr_let "min"
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_field (expr_id "args") (expr_string "4")) expr_undefined)
          (expr_number (JsNumber.of_int 0))
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
                (expr_op2 binary_op_stx_eq (expr_number (JsNumber.of_int 0))
                 (expr_id "tiy"))))
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
                (expr_op2 binary_op_add (expr_number (JsNumber.of_int 1900))
                 (expr_id "tiy")) (expr_id "y")))))
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
               [])))))))))))))))
.
Definition ex_privDateFromTime := 
expr_let "mft" (expr_app (expr_id "%MonthFromTime") [expr_id "t"])
(expr_let "CalcDay"
 (expr_lambda ["offset"]
  (expr_op2 binary_op_sub
   (expr_op2 binary_op_sub
    (expr_app (expr_id "%DayWithinYear") [expr_id "t"]) (expr_id "offset"))
   (expr_app (expr_id "%InLeapYear") [expr_id "t"])))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "mft")
   (expr_number (JsNumber.of_int 0)))
  (expr_op2 binary_op_add (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
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
           (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 272)])
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "mft")
             (expr_number (JsNumber.of_int 10)))
            (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int 303)])
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "mft")
              (expr_number (JsNumber.of_int 11)))
             (expr_app (expr_id "CalcDay")
              [expr_number (JsNumber.of_int 333)])
             (expr_app (expr_id "%TypeError")
              [expr_string "Something terrible happened in %DateFromTime"]))))))))))))))
.
Definition ex_privDay := 
expr_op1 unary_op_floor
(expr_op2 binary_op_div (expr_id "t") (expr_id "%msPerDay"))
.
Definition ex_privDayFromYear := 
expr_let "fragment"
(expr_lambda ["offset"; "coefficient"]
 (expr_op1 unary_op_floor
  (expr_op2 binary_op_div
   (expr_op2 binary_op_sub (expr_id "y") (expr_id "offset"))
   (expr_id "coefficient"))))
(expr_let "base"
 (expr_op2 binary_op_mul (expr_number (JsNumber.of_int 365))
  (expr_op2 binary_op_sub (expr_id "y") (expr_number (JsNumber.of_int 1970))))
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
      (expr_id "part2")) (expr_id "part3"))))))
.
Definition ex_privDayWithinYear := 
expr_op2 binary_op_sub (expr_app (expr_id "%Day") [expr_id "t"])
(expr_app (expr_id "%DayFromYear")
 [expr_app (expr_id "%YearFromTime") [expr_id "t"]])
.
Definition ex_privDaysInMonth := 
expr_let "m"
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
    (expr_number (JsNumber.of_int 10))))) (expr_number (JsNumber.of_int 30))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "m") (expr_number (JsNumber.of_int 1)))
  (expr_op2 binary_op_add (expr_number (JsNumber.of_int 28)) (expr_id "leap"))
  (expr_number (JsNumber.of_int 31))))
.
Definition ex_privDaysInYear := 
expr_if
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_op2 binary_op_mod (expr_id "y") (expr_number (JsNumber.of_int 4)))
  (expr_number (JsNumber.of_int 0))) expr_false expr_true)
(expr_number (JsNumber.of_int 365))
(expr_if
 (expr_let "%or"
  (expr_op2 binary_op_stx_eq
   (expr_op2 binary_op_mod (expr_id "y") (expr_number (JsNumber.of_int 400)))
   (expr_number (JsNumber.of_int 0)))
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_op2 binary_op_mod (expr_id "y")
      (expr_number (JsNumber.of_int 100))) (expr_number (JsNumber.of_int 0)))
    expr_false expr_true))) (expr_number (JsNumber.of_int 366))
 (expr_number (JsNumber.of_int 365)))
.
Definition ex_privEnvCheckAssign := 
expr_if
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
 (expr_app (expr_id "%UnwritableDispatch") [expr_id "id"]))
.
Definition ex_privEnvGet := 
expr_if
(expr_if (expr_id "strict")
 (expr_app (expr_id "%isUnbound") [expr_id "context"; expr_id "id"])
 expr_false) (expr_app (expr_id "%UnboundId") [expr_id "id"])
(expr_get_field (expr_id "context") (expr_id "id"))
.
Definition ex_privEqEq := 
expr_label "ret"
(expr_let "t1" (expr_op1 unary_op_typeof (expr_id "x1"))
 (expr_let "t2" (expr_op1 unary_op_typeof (expr_id "x2"))
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_id "t2"))
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "undefined"))
    (expr_break "ret" expr_true)
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "null"))
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
            (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "number"))))
          (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "object"))
          expr_false)
         (expr_break "ret"
          (expr_app (expr_id "eqeq")
           [expr_id "x1"; expr_app (expr_id "%ToPrimitive") [expr_id "x2"]]))
         (expr_if
          (expr_if
           (expr_let "%or"
            (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "string"))
            (expr_if (expr_id "%or") (expr_id "%or")
             (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "number"))))
           (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "object"))
           expr_false)
          (expr_break "ret"
           (expr_app (expr_id "eqeq")
            [expr_app (expr_id "%ToPrimitive") [expr_id "x1"]; expr_id "x2"]))
          (expr_break "ret" expr_false)))))))))))
.
Definition ex_privErrorConstructor := 
expr_let "o"
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
   (expr_set_field (expr_id "o") (expr_string "message") (expr_id "$newVal")))
  (expr_id "o")) (expr_id "o"))
.
Definition ex_privErrorDispatch := 
expr_if (expr_app (expr_id "%IsJSError") [expr_id "maybe-js-error"])
(expr_throw (expr_id "maybe-js-error"))
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
  (expr_string "unwritable-field"))
 (expr_app (expr_id "%TypeError") [expr_string "Field not writable"])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
   (expr_string "unconfigurable-delete"))
  (expr_app (expr_id "%TypeError") [expr_string "Field not deletable"])
  (expr_throw (expr_id "maybe-js-error"))))
.
Definition ex_privEvalErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privFunctionConstructor := 
expr_let "argCount" (expr_get_field (expr_id "args") (expr_string "length"))
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
      [expr_op2 binary_op_add (expr_id "n") (expr_number (JsNumber.of_int 1));
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
              (data_intro (expr_id "final") expr_false expr_false expr_false))]]))))))
.
Definition ex_privGetterValue := 
expr_get_field (expr_id "o") (expr_string "func")
.
Definition ex_privGreaterEqual := 
expr_let "result"
(expr_app (expr_id "%CompareOp") [expr_id "l"; expr_id "r"; expr_true])
(expr_if
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
  expr_false expr_true) (expr_op1 unary_op_not (expr_id "result")) expr_false)
.
Definition ex_privGreaterThan := 
expr_let "result"
(expr_app (expr_id "%CompareOp") [expr_id "r"; expr_id "l"; expr_false])
(expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
 expr_false (expr_id "result"))
.
Definition ex_privImmut := 
expr_seq (expr_op1 unary_op_pretty (expr_id "obj"))
(expr_seq
 (expr_set_attr pattr_enum (expr_id "obj") (expr_id "prop") expr_false)
 (expr_set_attr pattr_config (expr_id "obj") (expr_id "prop") expr_false))
.
Definition ex_privInLeapYear := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "%DaysInYear")
  [expr_app (expr_id "%YearFromTime") [expr_id "t"]])
 (expr_number (JsNumber.of_int 365))) (expr_number (JsNumber.of_int 0))
(expr_number (JsNumber.of_int 1))
.
Definition ex_privIsFinite := 
expr_op1 unary_op_not
(expr_let "%or"
 (expr_let "%or"
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")) expr_false
   expr_true)
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_op2 binary_op_stx_eq (expr_id "n") (expr_number (JsNumber.of_int 0)))))
 (expr_if (expr_id "%or") (expr_id "%or")
  (expr_op2 binary_op_stx_eq (expr_id "n") (expr_number (JsNumber.of_int 0)))))
.
Definition ex_privIsJSError := 
expr_if
(expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "thing"))
 (expr_string "object"))
(expr_op2 binary_op_has_own_property (expr_id "thing")
 (expr_string "%js-exn")) expr_false
.
Definition ex_privIsObject := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
(expr_let "c1"
 (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
 (expr_let "c2"
  (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
  (expr_let "%or" (expr_id "c1")
   (expr_if (expr_id "%or") (expr_id "%or") (expr_id "c2")))))
.
Definition ex_privIsPrototypeOflambda := 
expr_recc "searchChain"
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
    [expr_id "O"; expr_get_field (expr_id "args") (expr_string "0")]))))
.
Definition ex_privJSError := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_null
 expr_undefined)
[("%js-exn", property_data
             (data_intro (expr_id "err") expr_false expr_false expr_false))]
.
Definition ex_privLeftShift := 
expr_op2 binary_op_shiftl (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privLessEqual := 
expr_let "result"
(expr_app (expr_id "%CompareOp") [expr_id "r"; expr_id "l"; expr_false])
(expr_if
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
  expr_false expr_true) (expr_op1 unary_op_not (expr_id "result")) expr_false)
.
Definition ex_privLessThan := 
expr_let "result"
(expr_app (expr_id "%CompareOp") [expr_id "l"; expr_id "r"; expr_true])
(expr_if (expr_op2 binary_op_stx_eq (expr_id "result") expr_undefined)
 expr_false (expr_id "result"))
.
Definition ex_privLocalTime :=  expr_id "t" .
Definition ex_privMakeDate := 
expr_op2 binary_op_add
(expr_op2 binary_op_mul (expr_id "day") (expr_id "%msPerDay"))
(expr_id "time")
.
Definition ex_privMakeDay := 
expr_if
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
     (expr_op2 binary_op_mod (expr_id "m") (expr_number (JsNumber.of_int 12)))
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
           (expr_id "dt")) (expr_number (JsNumber.of_int 1))))))))))))
.
Definition ex_privMakeGetter := 
expr_object
(objattrs_intro (expr_string "Object") expr_false expr_null
 (expr_lambda ["this"]
  (expr_app (expr_id "f")
   [expr_id "this";
    expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
     expr_undefined) []])) expr_undefined)
[("func", property_data
          (data_intro (expr_id "f") expr_false expr_false expr_false))]
.
Definition ex_privMakeSetter := 
expr_object
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
          (data_intro (expr_id "f") expr_false expr_false expr_false))]
.
Definition ex_privMakeTime := 
expr_if
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
      (expr_id "millis")) (expr_id "t"))))))
.
Definition ex_privMakeTypeError := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "msg"))
  (expr_string "object")) (expr_string "object passed to ThrowTypeError")
 (expr_op1 unary_op_prim_to_str (expr_id "msg")))
(expr_object
 (objattrs_intro (expr_string "Object") expr_true (expr_id "%TypeErrorProto")
  expr_null expr_undefined)
 [("message", property_data
              (data_intro (expr_id "msg") expr_false expr_false expr_false))])
.
Definition ex_privMonthFromTime := 
expr_let "DayWithinYear"
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
   (expr_op2 binary_op_lt (expr_app (expr_id "DayWithinYear") [expr_id "t"])
    (expr_op2 binary_op_add (expr_id "end")
     (expr_app (expr_id "%InLeapYear") [expr_id "t"]))) expr_false))
 (expr_if
  (expr_if
   (expr_op2 binary_op_le (expr_number (JsNumber.of_int 0))
    (expr_app (expr_id "%DayWithinYear") [expr_id "t"]))
   (expr_op2 binary_op_lt (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
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
       [expr_number (JsNumber.of_int 120); expr_number (JsNumber.of_int 151)])
      (expr_number (JsNumber.of_int 4))
      (expr_if
       (expr_app (expr_id "CheckLeapRange")
        [expr_number (JsNumber.of_int 151); expr_number (JsNumber.of_int 181)])
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
              [expr_string "Something terrible in date %MonthFromTime"]))))))))))))))
.
Definition ex_privNativeErrorConstructor := 
expr_lambda ["this"; "args"]
(expr_let "rtn"
 (expr_object
  (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
   expr_undefined) [])
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
     (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn")))
.
Definition ex_privNumberConstructor := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "this") expr_undefined)
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
    (objattrs_intro (expr_string "Number") expr_true (expr_id "%NumberProto")
     expr_null (expr_id "v")) []))))
.
Definition ex_privObjectConstructor := 
expr_let "calledAsFunction"
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
            (expr_id "defaultRtn")))))) (expr_id "defaultRtn"))))))))
.
Definition ex_privObjectTypeCheck := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
(expr_let "c1"
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
  expr_false expr_true)
 (expr_let "c2"
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
   expr_false expr_true)
  (expr_if (expr_if (expr_id "c1") (expr_id "c2") expr_false)
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus
     (expr_op1 unary_op_prim_to_str (expr_id "o"))
     (expr_string " is not an object")]) expr_null)))
.
Definition ex_privPostDecrement := 
expr_app (expr_id "%PostfixOp")
[expr_id "obj"; expr_id "fld"; expr_id "%PrimSub"]
.
Definition ex_privPostIncrement := 
expr_app (expr_id "%PostfixOp")
[expr_id "obj"; expr_id "fld"; expr_id "%PrimAdd"]
.
Definition ex_privPostfixOp := 
expr_let "oldValue"
(expr_app (expr_id "%ToNumber")
 [expr_get_field (expr_id "obj") (expr_id "fld")])
(expr_let "newValue"
 (expr_app (expr_id "op")
  [expr_id "oldValue"; expr_number (JsNumber.of_int 1)])
 (expr_seq
  (expr_let "$newVal" (expr_id "newValue")
   (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal")))
  (expr_id "oldValue")))
.
Definition ex_privPrefixDecrement := 
expr_app (expr_id "%PrefixOp")
[expr_id "obj"; expr_id "fld"; expr_id "%PrimSub"]
.
Definition ex_privPrefixIncrement := 
expr_app (expr_id "%PrefixOp")
[expr_id "obj"; expr_id "fld"; expr_id "%PrimAdd"]
.
Definition ex_privPrefixOp := 
expr_let "oldValue"
(expr_app (expr_id "%ToNumber")
 [expr_get_field (expr_id "obj") (expr_id "fld")])
(expr_let "newValue"
 (expr_app (expr_id "op")
  [expr_id "oldValue"; expr_number (JsNumber.of_int 1)])
 (expr_seq
  (expr_let "$newVal" (expr_id "newValue")
   (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal")))
  (expr_id "newValue")))
.
Definition ex_privPrimAdd := 
expr_let "l" (expr_app (expr_id "%ToPrimitive") [expr_id "l"])
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
     (expr_op2 binary_op_add (expr_id "lnum") (expr_id "rnum")))))))
.
Definition ex_privPrimMultOp := 
expr_let "lNum" (expr_app (expr_id "%ToNumber") [expr_id "l"])
(expr_let "rNum" (expr_app (expr_id "%ToNumber") [expr_id "r"])
 (expr_app (expr_id "op") [expr_id "lNum"; expr_id "rNum"]))
.
Definition ex_privPrimNew := 
expr_let "cproto1"
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
    (expr_id "constr_ret") (expr_id "newobj")))))
.
Definition ex_privPrimSub := 
expr_let "l" (expr_app (expr_id "%ToNumber") [expr_id "l"])
(expr_let "r" (expr_app (expr_id "%ToNumber") [expr_id "r"])
 (expr_op2 binary_op_sub (expr_id "l") (expr_id "r")))
.
Definition ex_privPropAccessorCheck := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "o") expr_undefined)
(expr_throw
 (expr_app (expr_id "%JSError")
  [expr_object
   (objattrs_intro (expr_string "Object") expr_true
    (expr_id "%ReferenceErrorProto") expr_null expr_undefined) []]))
(expr_app (expr_id "%ToObject") [expr_id "o"])
.
Definition ex_privRangeErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privReferenceErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privRegExpConstructor := 
expr_object
(objattrs_intro (expr_string "Object") expr_true (expr_id "%RegExpProto")
 expr_null expr_undefined) []
.
Definition ex_privSetterValue := 
expr_get_field (expr_id "o") (expr_string "func")
.
Definition ex_privSignedRightShift := 
expr_op2 binary_op_shiftr (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privStringConstructor := 
expr_let "S"
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
   (objattrs_intro (expr_string "String") expr_true (expr_id "%StringProto")
    expr_null (expr_id "S"))
   [("length", property_data
               (data_intro (expr_op1 unary_op_strlen (expr_id "S")) expr_true
                expr_false expr_false))])
  (expr_seq
   (expr_app (expr_id "%StringIndices") [expr_id "obj"; expr_id "S"])
   (expr_id "obj"))))
.
Definition ex_privStringIndexOflambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
              (expr_op2 binary_op_char_at (expr_id "searchStr") (expr_id "j")))
             expr_false expr_true) expr_false
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
        (expr_app (expr_id "find_k") [expr_id "start"])))))))))
.
Definition ex_privStringIndices := 
expr_let "len" (expr_op1 unary_op_strlen (expr_id "s"))
(expr_recc "loop"
 (expr_lambda ["i"]
  (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
   (expr_seq
    (expr_let "$newVal"
     (expr_op2 binary_op_char_at (expr_id "s") (expr_id "i"))
     (expr_set_field (expr_id "obj")
      (expr_op1 unary_op_prim_to_str (expr_id "i")) (expr_id "$newVal")))
    (expr_app (expr_id "loop")
     [expr_op2 binary_op_add (expr_id "i") (expr_number (JsNumber.of_int 1))]))
   expr_undefined))
 (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)]))
.
Definition ex_privSyntaxError := 
expr_throw
(expr_app (expr_id "%JSError")
 [expr_object
  (objattrs_intro (expr_string "Object") expr_true
   (expr_id "%SyntaxErrorProto") expr_null expr_undefined)
  [("message", property_data
               (data_intro
                (expr_op2 binary_op_string_plus
                 (expr_string "ReferenceError: ") (expr_id "msg")) expr_true
                expr_false expr_false))]])
.
Definition ex_privSyntaxErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privThrowTypeErrorFun := 
expr_let "msg" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_throw
 (expr_app (expr_id "%JSError")
  [expr_app (expr_id "%MakeTypeError") [expr_id "msg"]]))
.
Definition ex_privTimeClip := 
expr_if
(expr_op1 unary_op_not
 (expr_if (expr_app (expr_id "%IsFinite") [expr_id "t"])
  (expr_op2 binary_op_le (expr_op1 unary_op_abs (expr_id "t"))
   (expr_number (JsNumber.of_int 8640000000000000))) expr_false))
(expr_number (JsNumber.of_int 0))
(expr_app (expr_id "%ToInteger") [expr_id "t"])
.
Definition ex_privTimeFromYear := 
expr_op2 binary_op_mul (expr_id "%msPerDay")
(expr_app (expr_id "%DayFromYear") [expr_id "y"])
.
Definition ex_privTimeWithinDay := 
expr_op2 binary_op_mod (expr_id "t") (expr_id "%msPerDay")
.
Definition ex_privToBoolean := 
expr_op1 unary_op_prim_to_bool (expr_id "x")
.
Definition ex_privToInt32 := 
expr_let "int32bit" (expr_app (expr_id "%ToUint32") [expr_id "n"])
(expr_if
 (expr_op2 binary_op_ge (expr_id "int32bit")
  (expr_number (JsNumber.of_int 2147483648)))
 (expr_op2 binary_op_sub (expr_id "int32bit")
  (expr_number (JsNumber.of_int 4294967296))) (expr_id "int32bit"))
.
Definition ex_privToInteger := 
expr_label "ret"
(expr_let "number" (expr_app (expr_id "%ToNumber") [expr_id "i"])
 (expr_seq
  (expr_if
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "number") (expr_id "number"))
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
       (expr_break "ret" (expr_id "r")))))))))
.
Definition ex_privToJSError := 
expr_if (expr_app (expr_id "%IsJSError") [expr_id "maybe-js-error"])
(expr_get_field (expr_id "maybe-js-error") (expr_string "%js-exn"))
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
  (expr_string "unwritable-field"))
 (expr_app (expr_id "%MakeTypeError") [expr_string "Field not writable"])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "maybe-js-error")
   (expr_string "unconfigurable-delete"))
  (expr_app (expr_id "%MakeTypeError") [expr_string "Field not deletable"])
  (expr_throw (expr_id "maybe-js-error"))))
.
Definition ex_privToNumber := 
expr_recc "inner"
(expr_lambda ["x"]
 (expr_label "ret"
  (expr_let "t" (expr_op1 unary_op_typeof (expr_id "x"))
   (expr_seq
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "number"))
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
(expr_app (expr_id "inner") [expr_id "x"])
.
Definition ex_privToObject := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "o") expr_null)
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
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "string"))
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
           (expr_id "%BooleanProto") expr_null (expr_id "o")) [])) expr_null)
       (expr_app (expr_id "%TypeError")
        [expr_string "%ToObject received undefined"]))))))))
.
Definition ex_privToPrimitive := 
expr_app (expr_id "%ToPrimitiveHint") [expr_id "val"; expr_string "number"]
.
Definition ex_privToPrimitiveHint := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "val"))
(expr_if
 (expr_let "%or"
  (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "function"))
  (expr_if (expr_id "%or") (expr_id "%or")
   (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))))
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "hint") (expr_string "string"))
  (expr_app (expr_id "%ToPrimitiveStr") [expr_id "val"])
  (expr_app (expr_id "%ToPrimitiveNum") [expr_id "val"])) (expr_id "val"))
.
Definition ex_privToPrimitiveNum := 
expr_let "check"
(expr_lambda ["o"; "str"]
 (expr_let "valueOf" (expr_get_field (expr_id "o") (expr_id "str"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "valueOf"))
    (expr_string "function"))
   (expr_let "str"
    (expr_app (expr_id "valueOf")
     [expr_id "o";
      expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
       expr_undefined) []])
    (expr_if (expr_op1 unary_op_is_primitive (expr_id "str")) (expr_id "str")
     expr_null)) expr_null)))
(expr_let "r1"
 (expr_app (expr_id "check") [expr_id "obj"; expr_string "valueOf"])
 (expr_if
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "r1") expr_null) expr_false
   expr_true) (expr_id "r1")
  (expr_let "r2"
   (expr_app (expr_id "check") [expr_id "obj"; expr_string "toString"])
   (expr_if
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "r2") expr_null) expr_false
     expr_true) (expr_id "r2")
    (expr_app (expr_id "%TypeError")
     [expr_string "valueOf and toString both absent in toPrimitiveNum"])))))
.
Definition ex_privToPrimitiveStr := 
expr_label "ret"
(expr_seq
 (expr_let "toString"
  (expr_get_field (expr_id "obj") (expr_string "toString"))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "toString"))
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
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "valueOf"))
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
   [expr_string "valueOf and toString both absent in toPrimitiveStr"])))
.
Definition ex_privToString := 
expr_op1 unary_op_prim_to_str
(expr_app (expr_id "%ToPrimitiveHint") [expr_id "val"; expr_string "string"])
.
Definition ex_privToUint := 
expr_let "number" (expr_app (expr_id "%ToNumber") [expr_id "n"])
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
    (expr_op2 binary_op_lt (expr_id "sign") (expr_number (JsNumber.of_int 0)))
    (expr_let "close"
     (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))
     (expr_op2 binary_op_add (expr_id "close") (expr_id "limit")))
    (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))))))
.
Definition ex_privToUint16 := 
expr_app (expr_id "%ToUint")
[expr_id "n"; expr_number (JsNumber.of_int 65536)]
.
Definition ex_privToUint32 := 
expr_app (expr_id "%ToUint")
[expr_id "n"; expr_number (JsNumber.of_int 4294967296)]
.
Definition ex_privTypeError := 
expr_app (expr_id "%ThrowTypeErrorFun")
[expr_undefined;
 expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
  expr_undefined)
 [("0", property_data
        (data_intro (expr_id "msg") expr_false expr_false expr_false))]]
.
Definition ex_privTypeErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privTypeof := 
expr_try_catch
(expr_op1 unary_op_typeof (expr_get_field (expr_id "context") (expr_id "id")))
(expr_lambda ["e"] (expr_string "undefined"))
.
Definition ex_privURIErrorConstructor := 
expr_let "rtn"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto") expr_null
  expr_undefined) [])
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
    (expr_id "$newVal"))) (expr_id "rtn")) (expr_id "rtn"))
.
Definition ex_privUTC :=  expr_id "t" .
Definition ex_privUnaryNeg := 
expr_let "oldValue" (expr_app (expr_id "%ToNumber") [expr_id "expr"])
(expr_if
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "oldValue") (expr_id "oldValue"))
  expr_false expr_true) (expr_id "oldValue")
 (expr_let "negOne"
  (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
   (expr_number (JsNumber.of_int 1)))
  (expr_op2 binary_op_mul (expr_id "oldValue") (expr_id "negOne"))))
.
Definition ex_privUnaryPlus := 
expr_app (expr_id "%ToNumber") [expr_id "expr"]
.
Definition ex_privUnboundId := 
expr_throw
(expr_app (expr_id "%JSError")
 [expr_object
  (objattrs_intro (expr_string "Object") expr_true
   (expr_id "%ReferenceErrorProto") expr_null expr_undefined)
  [("message", property_data
               (data_intro
                (expr_op2 binary_op_string_plus
                 (expr_string "Unbound identifier: ") (expr_id "id"))
                expr_true expr_false expr_false))]])
.
Definition ex_privUnsignedRightShift := 
expr_op2 binary_op_zfshiftr (expr_app (expr_id "%ToUint32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privUnwritableDispatch := 
expr_lambda ["e"]
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "e") (expr_string "unwritable-field"))
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "id")
   (expr_string " not writable")])
 (expr_app (expr_id "%ErrorDispatch") [expr_id "e"]))
.
Definition ex_privYearFromTime := 
expr_let "sign"
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
  (expr_app (expr_id "loop") [expr_id "start"])))
.
Definition ex_privacosLambda :=  expr_string "acos NYI" .
Definition ex_privaiolambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
          (expr_break "ret" (expr_id "negOne"))))))))))))
.
Definition ex_privaliolambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
      (expr_break "ret" (expr_id "negOne"))))))))
.
Definition ex_privapplylambda := 
expr_let "applyArgs1" (expr_get_field (expr_id "args") (expr_string "1"))
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
    expr_app (expr_id "%mkArgsObj") [expr_id "applyArgs"]])))
.
Definition ex_privarrayTLSlambda := 
expr_let "isCallable"
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
     (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_code (expr_id "o"))
      expr_null) (expr_break "ret" expr_false) expr_null)
    (expr_break "ret" expr_true)))))
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
           (expr_op2 binary_op_stx_eq (expr_id "firstElement") expr_undefined)))
         (expr_string "")
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
                (expr_op2 binary_op_stx_eq (expr_id "nextElement") expr_null)
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
           [expr_number (JsNumber.of_int 1); expr_id "R"])))))))))))
.
Definition ex_privarrayToStringlambda := 
expr_let "array" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "thefunc" (expr_get_field (expr_id "array") (expr_string "join"))
 (expr_let "ffunc"
  (expr_if
   (expr_if
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_typeof (expr_id "thefunc")) (expr_string "object")))
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_typeof (expr_id "thefunc")) (expr_string "function")))
    expr_false) (expr_id "%objectToStringlambda")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_code (expr_id "thefunc")) expr_null)
    (expr_id "%objectToStringlambda") (expr_id "thefunc")))
  (expr_app (expr_id "ffunc")
   [expr_id "array";
    expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
     expr_undefined) []])))
.
Definition ex_privasinLambda :=  expr_string "asin NYI" .
Definition ex_privatan2Lambda :=  expr_string "atan2 NYI" .
Definition ex_privatanLambda :=  expr_string "atan NYI" .
Definition ex_privbindLambda := 
expr_label "ret"
(expr_seq
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
    (expr_string "function")) expr_false expr_true)
  (expr_app (expr_id "%TypeError") [expr_string "this not function in bind"])
  expr_null)
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
       (expr_if (expr_get_field (expr_id "args_inner") (expr_string "%new"))
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
           (expr_break "ret" (expr_id "F")))))))))))))
.
Definition ex_privbooleanToStringlambda := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "this"))
(expr_let "b"
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "boolean"))
  (expr_id "this")
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_class (expr_id "this")) (expr_string "Boolean"))
    (expr_get_obj_attr oattr_primval (expr_id "this"))
    (expr_app (expr_id "%TypeError")
     [expr_string "Boolean.prototype.toString got non-boolean object"]))
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus
     (expr_string "Boolean.prototype.toString got ") (expr_id "t")])))
 (expr_if (expr_id "b") (expr_string "true") (expr_string "false")))
.
Definition ex_privcalllambda := 
expr_let "callArgs"
(expr_app (expr_id "%slice_internal")
 [expr_id "args";
  expr_number (JsNumber.of_int 1);
  expr_app (expr_id "%len") [expr_id "args"]])
(expr_app (expr_id "this")
 [expr_get_field (expr_id "args") (expr_string "0"); expr_id "callArgs"])
.
Definition ex_privcharatlambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
    (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position"))))))
.
Definition ex_privcharcodeatlambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
     (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position")))))))
.
Definition ex_privconcatLambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
       (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "elt"))
        (expr_string "object"))
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
         (expr_id "$newVal"))) (expr_id "A"))))))))
.
Definition ex_privconfigurableEval := 
expr_let "evalStr" (expr_get_field (expr_id "args") (expr_string "0"))
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
      (expr_set_field (expr_id "globalEnv") (expr_string "%nonstrictContext")
       (expr_id "$newVal")))
     (expr_seq
      (expr_let "$newVal" (expr_app (expr_id "%makeContextVarDefiner") [])
       (expr_set_field (expr_id "globalEnv") (expr_string "%defineGlobalVar")
        (expr_id "$newVal")))
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_op1 unary_op_typeof (expr_id "evalStr")) (expr_string "string"))
       (expr_eval (expr_id "evalStr") (expr_id "globalEnv"))
       (expr_id "evalStr"))))))))
.
Definition ex_privcosLambda :=  expr_string "cos NYI" .
Definition ex_privcreateLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
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
          (expr_get_field (expr_id "args") (expr_string "1")) expr_undefined)
         expr_false expr_true) expr_false)
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
       (expr_id "obj"))))))))
.
Definition ex_privdateGetTimezoneOffsetLambda := 
expr_let "t" (expr_get_obj_attr oattr_primval (expr_id "this"))
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number (JsNumber.of_int 0)))
 (expr_number (JsNumber.of_int 0)) (expr_number (JsNumber.of_int 0)))
.
Definition ex_privdateToStringLambda :=  expr_string "Date toString NYI" .
Definition ex_privdateValueOfLambda := 
expr_get_obj_attr oattr_primval (expr_id "this")
.
Definition ex_privdategetDateLambda := 
expr_let "t" (expr_get_obj_attr oattr_primval (expr_id "this"))
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number (JsNumber.of_int 0)))
 (expr_id "t")
 (expr_app (expr_id "%DateFromTime")
  [expr_app (expr_id "%LocalTime") [expr_id "t"]]))
.
Definition ex_privdategetDayLambda := 
expr_let "day"
(expr_op1 unary_op_floor
 (expr_op2 binary_op_div (expr_get_obj_attr oattr_primval (expr_id "this"))
  (expr_id "%msPerDay")))
(expr_let "weekday"
 (expr_op2 binary_op_mod
  (expr_op2 binary_op_add (expr_id "day") (expr_number (JsNumber.of_int 4)))
  (expr_number (JsNumber.of_int 7))) (expr_id "weekday"))
.
Definition ex_privdecodeURIComponentLambda := 
expr_string "decodeURIComponent NYI"
.
Definition ex_privdecodeURILambda :=  expr_string "decodeURI NYI" .
Definition ex_privdefine15Property := 
expr_let "%mkPropObj"
(expr_lambda ["value"; "writable"; "enumerable"; "configurable"]
 (expr_if
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "value") expr_null) expr_false
   expr_true)
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
   [expr_id "prop"; expr_true; expr_false; expr_true]]))
.
Definition ex_privdefineGlobalAccessors := 
expr_seq
(expr_set_attr pattr_config (expr_id "%globalContext") (expr_id "id")
 expr_true)
(expr_seq
 (expr_set_attr pattr_enum (expr_id "%globalContext") (expr_id "id")
  expr_true)
 (expr_seq
  (expr_set_attr pattr_getter (expr_id "%globalContext") (expr_id "id")
   (expr_app (expr_id "%makeEnvGetter") [expr_id "%global"; expr_id "id"]))
  (expr_set_attr pattr_setter (expr_id "%globalContext") (expr_id "id")
   (expr_app (expr_id "%makeEnvSetter") [expr_id "%global"; expr_id "id"]))))
.
Definition ex_privdefineGlobalVar := 
expr_if
(expr_op1 unary_op_not
 (expr_op2 binary_op_has_property (expr_id "context") (expr_id "id")))
(expr_seq
 (expr_set_attr pattr_config (expr_id "%global") (expr_id "id") expr_true)
 (expr_seq
  (expr_set_attr pattr_writable (expr_id "%global") (expr_id "id") expr_true)
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
       (expr_set_attr pattr_enum (expr_id "context") (expr_id "id") expr_true)
       (expr_seq
        (expr_set_attr pattr_getter (expr_id "context") (expr_id "id")
         (expr_app (expr_id "%makeEnvGetter")
          [expr_id "%global"; expr_id "id"]))
        (expr_set_attr pattr_setter (expr_id "context") (expr_id "id")
         (expr_app (expr_id "%makeEnvSetter")
          [expr_id "%global"; expr_id "id"])))))))))) expr_undefined
.
Definition ex_privdefineNYIProperty := 
expr_let "unimplFunc"
(expr_lambda ["this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
(expr_let "unimplObj"
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true (expr_id "%FunctionProto")
   (expr_id "unimplFunc") expr_undefined) [])
 (expr_app (expr_id "%define15Property")
  [expr_id "base"; expr_id "name"; expr_id "unimplObj"]))
.
Definition ex_privdefineOwnProperty := 
expr_seq
(expr_let "t" (expr_op1 unary_op_typeof (expr_id "obj"))
 (expr_if
  (expr_if
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
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
     (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr") expr_true)
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
            (expr_get_field (expr_id "current-prop") (expr_string "writable")))
           expr_false expr_true)
          (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
           (expr_get_field (expr_id "current-prop") (expr_string "writable")))
          expr_undefined))
        (expr_if
         (expr_app (expr_id "isAccessorDescriptor") [expr_id "current-prop"])
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
          (expr_get_field (expr_id "current-prop") (expr_string "enumerable")))
         expr_undefined)
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
            (expr_get_field (expr_id "current-prop")
             (expr_string "configurable"))) expr_false expr_true)
          (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr")
           (expr_get_field (expr_id "current-prop")
            (expr_string "configurable"))) expr_undefined) expr_true)))))))))
.
Definition ex_privdefinePropertiesLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_seq
  (expr_let "props"
   (expr_app (expr_id "%ToObject")
    [expr_get_field (expr_id "args") (expr_string "1")])
   (expr_let "names" (expr_own_field_names (expr_id "props"))
    (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
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
                  (expr_set_field (expr_id "argsObj") (expr_string "length")
                   (expr_id "$newVal")))
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
  (expr_id "O")))
.
Definition ex_privdefinePropertylambda := 
expr_let "obj" (expr_get_field (expr_id "args") (expr_string "0"))
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
            [expr_id "obj"; expr_id "field"; expr_id "attrobj"]))))))))))))
.
Definition ex_privencodeURIComponentLambda := 
expr_string "encodeURIComponent NYI"
.
Definition ex_privencodeURILambda :=  expr_string "encodeURI NYI" .
Definition ex_privescapeLambda :=  expr_string "escape NYI" .
Definition ex_privetslambda := 
expr_if
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
    (expr_get_field (expr_id "this") (expr_string "message")) expr_undefined)
   (expr_string "")
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
        (expr_if (expr_id "c2") (expr_break "ret" (expr_id "name")) expr_null)
        (expr_let "prefix"
         (expr_op2 binary_op_string_plus (expr_id "name") (expr_string ": "))
         (expr_break "ret"
          (expr_op2 binary_op_string_plus (expr_id "prefix") (expr_id "msg"))))))))))))
.
Definition ex_privevallambda := 
expr_app (expr_id "%configurableEval")
[expr_id "%global"; expr_id "%globalContext"; expr_false; expr_id "args"]
.
Definition ex_priveverylambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
            (expr_let "kValue" (expr_get_field (expr_id "O") (expr_id "Pk"))
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
                   (expr_set_field (expr_id "argsObj") (expr_string "length")
                    (expr_id "$newVal")))
                  (expr_let "testResult"
                   (expr_app (expr_id "callbackfn")
                    [expr_id "T"; expr_id "argsObj"])
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_app (expr_id "%ToBoolean") [expr_id "testResult"])
                     expr_false) expr_false
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "k")
                      (expr_number (JsNumber.of_int 1))])))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int 1))])))) expr_true))
       (expr_break "ret"
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))))
.
Definition ex_privexplambda :=  expr_undefined .
Definition ex_privfilterlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
            (expr_let "kValue" (expr_get_field (expr_id "O") (expr_id "Pk"))
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
                   (expr_set_field (expr_id "argsObj") (expr_string "length")
                    (expr_id "$newVal")))
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
         (expr_break "ret" (expr_id "A")))))))))))
.
Definition ex_privforeachlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
             (expr_let "kValue" (expr_get_field (expr_id "O") (expr_id "Pk"))
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
      expr_undefined))))))
.
Definition ex_privfreezelambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
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
     (expr_seq (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
      (expr_id "O")))))))
.
Definition ex_privfromcclambda := 
expr_if
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
   [expr_number (JsNumber.of_int 0); expr_string ""])))
.
Definition ex_privfunctionToStringlambda := 
expr_string "function ToString"
.
Definition ex_privgetCurrentUTC := 
expr_op1 unary_op_current_utc_millis (expr_string "ignored")
.
Definition ex_privgetMonthlambda :=  expr_number (JsNumber.of_int 3) .
Definition ex_privgetYearlambda :=  expr_number (JsNumber.of_int 78) .
Definition ex_privgopdLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
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
        (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
         expr_undefined)
        [("value", property_data
                   (data_intro
                    (expr_get_attr pattr_enum (expr_id "O") (expr_id "name"))
                    expr_true expr_false expr_false));
         ("writable", property_data
                      (data_intro expr_true expr_true expr_false expr_false));
         ("enumerable", property_data
                        (data_intro expr_true expr_true expr_false expr_false));
         ("configurable", property_data
                          (data_intro expr_true expr_true expr_false
                           expr_false))]])
      (expr_seq
       (expr_app (expr_id "%defineOwnProperty")
        [expr_id "obj";
         expr_string "configurable";
         expr_object
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined)
         [("value", property_data
                    (data_intro
                     (expr_get_attr pattr_config (expr_id "O")
                      (expr_id "name")) expr_true expr_false expr_false));
          ("writable", property_data
                       (data_intro expr_true expr_true expr_false expr_false));
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
          (expr_break "ret" (expr_id "obj"))))))))))))
.
Definition ex_privgopnLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "A"
  (expr_object
   (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
    expr_null expr_undefined)
   [("length", property_data
               (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                expr_false expr_false))])
  (expr_let "props" (expr_own_field_names (expr_id "O"))
   (expr_let "len" (expr_get_field (expr_id "props") (expr_string "length"))
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
     (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
      (expr_id "A")))))))
.
Definition ex_privgpoLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_get_obj_attr oattr_proto (expr_id "O")))
.
Definition ex_privhasOwnPropertylambda := 
expr_if
(expr_op2 binary_op_has_own_property (expr_id "this")
 (expr_get_field (expr_id "args") (expr_string "0"))) expr_true expr_false
.
Definition ex_privin := 
expr_let "rtype" (expr_op1 unary_op_typeof (expr_id "r"))
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
  (expr_app (expr_id "%ToString") [expr_id "l"])))
.
Definition ex_privinstanceof := 
expr_let "rtype" (expr_op1 unary_op_typeof (expr_id "r"))
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
       (expr_op2 binary_op_stx_eq (expr_id "ltype") (expr_string "function"))
       expr_false expr_true)
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
          (expr_op2 binary_op_stx_eq (expr_id "Otype") (expr_string "object"))
          expr_false expr_true) expr_false)
        (expr_app (expr_id "%TypeError")
         [expr_string "Prototype was not function or object"]) expr_null)
       (expr_recc "search"
        (expr_lambda ["v"]
         (expr_let "vp" (expr_get_obj_attr oattr_proto (expr_id "v"))
          (expr_if (expr_op2 binary_op_stx_eq (expr_id "vp") expr_null)
           expr_false
           (expr_if (expr_op2 binary_op_stx_eq (expr_id "O") (expr_id "vp"))
            expr_true (expr_app (expr_id "search") [expr_id "vp"])))))
        (expr_break "ret" (expr_app (expr_id "search") [expr_id "l"]))))))))))
.
Definition ex_privisExtensibleLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_get_obj_attr oattr_extensible (expr_id "O")))
.
Definition ex_privisFiniteLambda := 
expr_let "n"
(expr_app (expr_id "%ToNumber")
 [expr_get_field (expr_id "args") (expr_string "0")])
(expr_app (expr_id "%IsFinite") [expr_id "n"])
.
Definition ex_privisFrozenLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
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
    (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))
.
Definition ex_privisNaNlambda := 
expr_let "n"
(expr_app (expr_id "%ToNumber")
 [expr_get_field (expr_id "args") (expr_string "0")])
(expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")) expr_false
 expr_true)
.
Definition ex_privisSealedLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
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
         (expr_if (expr_get_attr pattr_config (expr_id "O") (expr_id "name"))
          (expr_break "ret" expr_false) expr_null))
        (expr_break "ret"
         (expr_app (expr_id "loop")
          [expr_op2 binary_op_add (expr_id "i")
           (expr_number (JsNumber.of_int 1))])))
       (expr_break "ret"
        (expr_op1 unary_op_not
         (expr_get_obj_attr oattr_extensible (expr_id "O")))))))
    (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))
.
Definition ex_privisUnbound := 
expr_op1 unary_op_not
(expr_op2 binary_op_has_property (expr_id "%global") (expr_id "id"))
.
Definition ex_privjoinlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
       (expr_number (JsNumber.of_int 0))) (expr_break "ret" (expr_string ""))
      expr_null)
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
         [expr_number (JsNumber.of_int 1); expr_id "start"])))))))))
.
Definition ex_privkeysLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "A"
  (expr_object
   (objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
    expr_null expr_undefined)
   [("length", property_data
               (data_intro (expr_number (JsNumber.of_int 0)) expr_true
                expr_false expr_false))])
  (expr_let "names" (expr_own_field_names (expr_id "O"))
   (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
    (expr_recc "loop"
     (expr_lambda ["i"; "enumCount"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
        (expr_let "name" (expr_get_field (expr_id "names") (expr_id "indx"))
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
      (expr_id "A")))))))
.
Definition ex_privlen := 
expr_recc "inner_len"
(expr_lambda ["iter"]
 (expr_if
  (expr_op2 binary_op_has_own_property (expr_id "list")
   (expr_op1 unary_op_prim_to_str (expr_id "iter")))
  (expr_op2 binary_op_add (expr_number (JsNumber.of_int 1))
   (expr_app (expr_id "inner_len")
    [expr_op2 binary_op_add (expr_number (JsNumber.of_int 1))
     (expr_id "iter")])) (expr_id "iter")))
(expr_app (expr_id "inner_len") [expr_number (JsNumber.of_int 0)])
.
Definition ex_privlocaleCompareLambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "That"
  (expr_app (expr_id "%ToString")
   [expr_get_field (expr_id "args") (expr_string "0")])
  (expr_op2 binary_op_locale_compare (expr_id "S") (expr_id "That"))))
.
Definition ex_privlogLambda := 
expr_recc "loop"
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
(expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
.
Definition ex_privmakeContextVarDefiner := 
expr_let "envstore"
(expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
  expr_undefined) [])
(expr_lambda ["context"; "id"]
 (expr_let "envstore"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "context") (expr_id "%globalContext"))
   (expr_id "%global") (expr_id "envstore"))
  (expr_if
   (expr_op2 binary_op_has_own_property (expr_id "context") (expr_id "id"))
   (expr_seq
    (expr_if
     (expr_op1 unary_op_not
      (expr_op2 binary_op_has_property (expr_id "envstore") (expr_id "id")))
     (expr_let "$newVal" expr_undefined
      (expr_set_field (expr_id "envstore") (expr_id "id") (expr_id "$newVal")))
     expr_undefined) expr_undefined)
   (expr_seq
    (expr_let "$newVal" expr_undefined
     (expr_set_field (expr_id "envstore") (expr_id "id") (expr_id "$newVal")))
    (expr_let "%setter"
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true expr_null
       (expr_lambda ["this"; "args"]
        (expr_if
         (expr_op2 binary_op_has_property (expr_id "envstore") (expr_id "id"))
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
        (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
         expr_undefined)
        [("get", property_data
                 (data_intro (expr_id "%getter") expr_true expr_false
                  expr_false));
         ("set", property_data
                 (data_intro (expr_id "%setter") expr_true expr_false
                  expr_false))]])))))))
.
Definition ex_privmakeEnvGetter := 
expr_object
(objattrs_intro (expr_string "Object") expr_false (expr_id "%FunctionProto")
 (expr_lambda ["this"]
  (expr_if
   (expr_op2 binary_op_has_property (expr_id "object") (expr_id "id"))
   (expr_get_field (expr_id "object") (expr_id "id"))
   (expr_app (expr_id "%UnboundId") [expr_id "id"]))) expr_undefined) 
[]
.
Definition ex_privmakeEnvSetter := 
expr_object
(objattrs_intro (expr_string "Object") expr_false (expr_id "%FunctionProto")
 (expr_lambda ["this"; "arg"]
  (expr_try_catch
   (expr_let "$newVal" (expr_id "arg")
    (expr_set_field (expr_id "object") (expr_id "id") (expr_id "$newVal")))
   (expr_app (expr_id "%UnwritableDispatch") [expr_id "id"]))) expr_undefined)
[]
.
Definition ex_privmakeWithContext := 
expr_let "names"
(expr_app (expr_id "%propertyNames") [expr_id "object"; expr_true])
(expr_let "mksetter"
 (expr_lambda ["id"]
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null
    (expr_lambda ["this"; "args"]
     (expr_if
      (expr_op2 binary_op_has_property (expr_id "object") (expr_id "id"))
      (expr_let "$newVal" (expr_get_field (expr_id "args") (expr_string "0"))
       (expr_set_field (expr_id "object") (expr_id "id") (expr_id "$newVal")))
      (expr_let "$newVal" (expr_get_field (expr_id "args") (expr_string "0"))
       (expr_set_field (expr_id "context") (expr_id "id") (expr_id "$newVal")))))
    expr_undefined) []))
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
                       (data_intro expr_true expr_true expr_false expr_false))]]))
    (expr_seq
     (expr_app (expr_id "%primEach") [expr_id "names"; expr_id "addBinding"])
     (expr_id "newcontext"))))))
.
Definition ex_privmaplambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
            (expr_let "kValue" (expr_get_field (expr_id "O") (expr_id "Pk"))
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
                   (expr_set_field (expr_id "argsObj") (expr_string "length")
                    (expr_id "$newVal")))
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
         (expr_break "ret" (expr_id "A")))))))))))
.
Definition ex_privmathAbsLambda := 
expr_let "n"
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
   (expr_break "ret" (expr_op1 unary_op_abs (expr_id "n"))))))
.
Definition ex_privmathCeilLambda := 
expr_let "x"
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
   expr_null) (expr_break "ret" (expr_op1 unary_op_ceil (expr_id "x")))))
.
Definition ex_privmathFloorLambda := 
expr_let "x"
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
   expr_null) (expr_break "ret" (expr_op1 unary_op_floor (expr_id "x")))))
.
Definition ex_privmathLogLambda := 
expr_let "n"
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
       expr_null) (expr_break "ret" (expr_op1 unary_op_log (expr_id "n")))))))))
.
Definition ex_privmathMaxLambda := 
expr_app (expr_id "%minMaxLambda")
[expr_id "this";
 expr_id "args";
 expr_id "%max";
 expr_number (JsNumber.of_int 0)]
.
Definition ex_privmathMinLambda := 
expr_app (expr_id "%minMaxLambda")
[expr_id "this";
 expr_id "args";
 expr_id "%min";
 expr_number (JsNumber.of_int 0)]
.
Definition ex_privmathPowLambda := 
expr_let "x"
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
         (expr_number (JsNumber.of_int 0))) expr_false expr_true) expr_false)
      (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
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
              (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
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
                         (expr_break "ret" (expr_number (JsNumber.of_int 0)))
                         expr_null))))
                     (expr_break "ret"
                      (expr_op2 binary_op_pow (expr_id "x") (expr_id "y"))))))))))))))))))))))))
.
Definition ex_privmax := 
expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "b")
(expr_id "a")
.
Definition ex_privmaybeDirectEval := 
expr_let "contextEval"
(expr_get_field (expr_id "theContext") (expr_string "eval"))
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "contextEval") (expr_id "%eval"))
 (expr_app (expr_id "%configurableEval")
  [expr_id "theThis"; expr_id "theContext"; expr_id "strict"; expr_id "args"])
 (expr_app (expr_id "%AppExprCheck")
  [expr_id "contextEval"; expr_undefined; expr_id "args"]))
.
Definition ex_privmin := 
expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "a")
(expr_id "b")
.
Definition ex_privminMaxLambda := 
expr_let "end" (expr_get_field (expr_id "args") (expr_string "length"))
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
     [expr_id "init"; expr_number (JsNumber.of_int 0)])))))
.
Definition ex_privmkArgsObj := 
expr_let "argsObj" (expr_app (expr_id "%mkArgsObjBase") [expr_id "args"])
(expr_seq
 (expr_let "$newVal" expr_false
  (expr_set_field (expr_id "argsObj") (expr_string "%new")
   (expr_id "$newVal")))
 (expr_seq
  (expr_set_attr pattr_writable (expr_id "argsObj") (expr_string "%new")
   expr_false) (expr_id "argsObj")))
.
Definition ex_privmkArgsObjBase := 
expr_let "keys" (expr_own_field_names (expr_id "args"))
(expr_let "argsObj"
 (expr_object
  (objattrs_intro (expr_string "Arguments") expr_true
   (expr_id "%ObjectProto") expr_null expr_undefined)
  [("callee", property_accessor
              (accessor_intro
               (expr_app (expr_id "%MakeGetter") [expr_id "%ThrowTypeError"])
               (expr_app (expr_id "%MakeSetter") [expr_id "%ThrowTypeError"])
               expr_false expr_true));
   ("caller", property_accessor
              (accessor_intro
               (expr_app (expr_id "%MakeGetter") [expr_id "%ThrowTypeError"])
               (expr_app (expr_id "%MakeSetter") [expr_id "%ThrowTypeError"])
               expr_false expr_true))])
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
       (expr_op2 binary_op_has_own_property (expr_id "keys") (expr_id "strx"))
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
         (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
          expr_undefined)
         [("value", property_data
                    (data_intro (expr_id "iter") expr_false expr_false
                     expr_false));
          ("writable", property_data
                       (data_intro expr_true expr_false expr_false expr_false));
          ("configurable", property_data
                           (data_intro expr_true expr_false expr_false
                            expr_false));
          ("enumerable", property_data
                         (data_intro expr_false expr_false expr_false
                          expr_false))]]))))
    (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
     (expr_id "argsObj"))))))
.
Definition ex_privmkNewArgsObj := 
expr_let "argsObj" (expr_app (expr_id "%mkArgsObjBase") [expr_id "args"])
(expr_seq
 (expr_let "$newVal" expr_true
  (expr_set_field (expr_id "argsObj") (expr_string "%new")
   (expr_id "$newVal")))
 (expr_seq
  (expr_set_attr pattr_writable (expr_id "argsObj") (expr_string "%new")
   expr_false) (expr_id "argsObj")))
.
Definition ex_privnumTLSLambda := 
expr_let "x"
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
    expr_undefined) []]))
.
Definition ex_privnumToStringAbstract := 
expr_recc "nts"
(expr_lambda ["n"; "r"]
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))
     expr_false expr_true) (expr_break "ret" (expr_string "NaN")) expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "n")
      (expr_number (JsNumber.of_int 0))) (expr_break "ret" (expr_string "0"))
     expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_lt (expr_id "n") (expr_number (JsNumber.of_int 0)))
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
(expr_app (expr_id "nts") [expr_id "n"; expr_id "r"])
.
Definition ex_privnumberToStringlambda := 
expr_let "notNumProto"
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "this") (expr_id "%NumberProto"))
 expr_false expr_true)
(expr_if
 (expr_if (expr_id "notNumProto")
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_obj_attr oattr_proto (expr_id "this")) (expr_id "%NumberProto"))
   expr_false expr_true) expr_false)
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
      [expr_get_obj_attr oattr_primval (expr_id "this"); expr_id "rint"]))))))
.
Definition ex_privobjectToStringlambda := 
expr_label "ret"
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
      (expr_op2 binary_op_string_plus (expr_id "class") (expr_string "]"))))))))
.
Definition ex_privoneArgObj := 
expr_app (expr_id "%mkArgsObj")
[expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
  expr_undefined)
 [("0", property_data
        (data_intro (expr_id "arg") expr_false expr_false expr_false));
  ("length", property_data
             (data_intro (expr_number (JsNumber.of_int 1)) expr_false
              expr_false expr_false))]]
.
Definition ex_privparse :=  expr_number (JsNumber.of_int 0) .
Definition ex_privparseFloatLambda :=  expr_string "parseFloat NYI" .
Definition ex_privparseIntlambda := 
expr_let "numstr"
(expr_app (expr_id "%ToString")
 [expr_get_field (expr_id "args") (expr_string "0")])
(expr_op1 unary_op_numstr_to_num (expr_id "numstr"))
.
Definition ex_privpoplambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "len")
    (expr_number (JsNumber.of_int 0)))
   (expr_seq
    (expr_let "$newVal" (expr_number (JsNumber.of_int 0))
     (expr_set_field (expr_id "O") (expr_string "length") (expr_id "$newVal")))
    expr_undefined)
   (expr_let "indx"
    (expr_app (expr_id "%ToString")
     [expr_op2 binary_op_sub (expr_id "len")
      (expr_number (JsNumber.of_int 1))])
    (expr_let "element" (expr_get_field (expr_id "O") (expr_id "indx"))
     (expr_seq (expr_delete_field (expr_id "O") (expr_id "indx"))
      (expr_seq
       (expr_let "$newVal" (expr_app (expr_id "%ToNumber") [expr_id "indx"])
        (expr_set_field (expr_id "O") (expr_string "length")
         (expr_id "$newVal"))) (expr_id "element"))))))))
.
Definition ex_privpreventExtensionsLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_seq (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
  (expr_id "O")))
.
Definition ex_privprimEach := 
expr_recc "loop"
(expr_lambda ["i"]
 (expr_let "istr" (expr_app (expr_id "%ToString") [expr_id "i"])
  (expr_if
   (expr_op2 binary_op_has_own_property (expr_id "arr") (expr_id "istr"))
   (expr_seq
    (expr_app (expr_id "fn")
     [expr_get_field (expr_id "arr") (expr_id "istr")])
    (expr_app (expr_id "loop")
     [expr_op2 binary_op_add (expr_id "i") (expr_number (JsNumber.of_int 1))]))
   expr_undefined)))
(expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])
.
Definition ex_privprintlambda := 
expr_op1 unary_op_print
(expr_app (expr_id "%ToString")
 [expr_get_field (expr_id "s") (expr_string "0")])
.
Definition ex_privpropEnumlambda := 
expr_let "getOwnProperty"
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
     expr_false (expr_get_attr pattr_enum (expr_id "O") (expr_id "P")))))))
.
Definition ex_privpropertyNames := 
expr_let "aux"
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
  (expr_own_field_names (expr_id "aux"))))
.
Definition ex_privprotoOfField := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "object") expr_null)
(expr_id "object")
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "object") (expr_id "fld"))
 (expr_id "object")
 (expr_app (expr_id "%protoOfField")
  [expr_get_obj_attr oattr_proto (expr_id "object"); expr_id "fld"]))
.
Definition ex_privpushlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
    [expr_number (JsNumber.of_int 0); expr_id "len"]))))
.
Definition ex_privrandomLambda :=  expr_number (JsNumber.of_int 4) .
Definition ex_privreduceRightLambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_null expr_undefined) [])
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
             expr_id "accumulator"]))))))))))))
.
Definition ex_privreducelambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
            (expr_app (expr_id "%TypeError") [expr_string "In Array reduce"])))
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
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_null expr_undefined) [])
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
             expr_id "accumulator"]))))))))))))
.
Definition ex_privreplacelambda := 
expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
(expr_let "search"
 (expr_app (expr_id "%ToString")
  [expr_get_field (expr_id "args") (expr_string "0")])
 (expr_let "replace" (expr_get_field (expr_id "args") (expr_string "1"))
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "replace"))
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
    (expr_app (expr_id "loop") [expr_id "S"])))))
.
Definition ex_privresolveThis := 
expr_if (expr_id "strict")
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
 (expr_id "%global") (expr_id "obj"))
.
Definition ex_privreverselambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "middle"
   (expr_op1 unary_op_floor
    (expr_op2 binary_op_div (expr_id "len") (expr_number (JsNumber.of_int 2))))
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
        (expr_let "upperP" (expr_app (expr_id "%ToString") [expr_id "upper"])
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
     (expr_id "O"))))))
.
Definition ex_privroundLambda :=  expr_string "round NYI" .
Definition ex_privsealLambda := 
expr_let "O" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_seq
  (expr_let "names" (expr_own_field_names (expr_id "O"))
   (expr_let "len" (expr_get_field (expr_id "names") (expr_string "length"))
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
   (expr_id "O"))))
.
Definition ex_privset_property := 
expr_let "obj" (expr_app (expr_id "%ToObject") [expr_id "obj"])
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
          (expr_let "newLen" (expr_app (expr_id "%ToUint32") [expr_id "val"])
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
            (expr_op2 binary_op_stx_eq (expr_id "fld") (expr_string "length"))
            (expr_app (expr_id "%ToUint32") [expr_id "val"]) (expr_id "val"))
           (expr_set_field (expr_id "obj") (expr_id "fld")
            (expr_id "$newVal")))
          (expr_if (expr_app (expr_id "isArrayIndex") [])
           (expr_let "uint" (expr_app (expr_id "%ToUint32") [expr_id "fld"])
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
        (expr_get_obj_attr oattr_class (expr_id "obj")) (expr_string "Array"))
       (expr_app (expr_id "setArrayField") [])
       (expr_let "$newVal" (expr_id "val")
        (expr_set_field (expr_id "obj") (expr_id "fld") (expr_id "$newVal"))))))))))
.
Definition ex_privshiftlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "len")
    (expr_number (JsNumber.of_int 0)))
   (expr_seq
    (expr_let "$newVal" (expr_number (JsNumber.of_int 0))
     (expr_set_field (expr_id "O") (expr_string "length") (expr_id "$newVal")))
    expr_undefined)
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
          (expr_id "$newVal"))) (expr_id "first")))))))))
.
Definition ex_privsinLambda := 
expr_let "n"
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
     (expr_break "ret" (expr_op1 unary_op_sin (expr_id "n"))))))))
.
Definition ex_privslice_internal := 
expr_let "retObj"
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
   [expr_id "min"; expr_number (JsNumber.of_int 0)])) (expr_id "retObj"))
.
Definition ex_privslicelambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_null expr_undefined)
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
                                  (data_intro expr_true expr_true expr_false
                                   expr_false))]]))
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
           (expr_id "$newVal"))) (expr_id "A"))))))))))
.
Definition ex_privsliolambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
           (expr_op2 binary_op_lt (expr_id "curr")
            (expr_number (JsNumber.of_int 0)))
           (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
            (expr_number (JsNumber.of_int 1)))
           (expr_if (expr_app (expr_id "check_k") [expr_id "curr"])
            (expr_id "curr")
            (expr_app (expr_id "find_k")
             [expr_op2 binary_op_sub (expr_id "curr")
              (expr_number (JsNumber.of_int 1))]))))
         (expr_app (expr_id "find_k") [expr_id "start"]))))))))))
.
Definition ex_privsomelambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn" (expr_get_field (expr_id "args") (expr_string "0"))
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
            (expr_let "kValue" (expr_get_field (expr_id "O") (expr_id "Pk"))
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
                   (expr_set_field (expr_id "argsObj") (expr_string "length")
                    (expr_id "$newVal")))
                  (expr_let "testResult"
                   (expr_app (expr_id "callbackfn")
                    [expr_id "T"; expr_id "argsObj"])
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_app (expr_id "%ToBoolean") [expr_id "testResult"])
                     expr_true) expr_true
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "k")
                      (expr_number (JsNumber.of_int 1))])))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int 1))])))) expr_false))
       (expr_break "ret"
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0)])))))))))
.
Definition ex_privsortlambda := 
expr_let "obj" (expr_app (expr_id "%ToObject") [expr_id "this"])
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
          (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false) expr_false)
         (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
        (expr_seq
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "hasj") expr_false)
          (expr_break "ret" (expr_number (JsNumber.of_int 1))) expr_null)
         (expr_seq
          (expr_if (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false)
           (expr_break "ret"
            (expr_op2 binary_op_sub (expr_number (JsNumber.of_int 0))
             (expr_number (JsNumber.of_int 1)))) expr_null)
          (expr_let "x" (expr_get_field (expr_id "obj") (expr_id "jString"))
           (expr_let "y" (expr_get_field (expr_id "obj") (expr_id "kString"))
            (expr_seq
             (expr_if
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
               (expr_op2 binary_op_stx_eq (expr_id "y") expr_undefined)
               expr_false)
              (expr_break "ret" (expr_number (JsNumber.of_int 0))) expr_null)
             (expr_seq
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
               (expr_break "ret" (expr_number (JsNumber.of_int 1))) expr_null)
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
         (expr_set_field (expr_id "obj") (expr_id "indx") (expr_id "$newVal")))
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
       (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "currIndex"))
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
    (expr_app (expr_id "isort") [expr_number (JsNumber.of_int 1)])))))
.
Definition ex_privsplicelambda := 
expr_let "start" (expr_get_field (expr_id "args") (expr_string "0"))
(expr_let "deleteCount" (expr_get_field (expr_id "args") (expr_string "1"))
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "emptyobj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
     expr_undefined) [])
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
       (expr_app (expr_id "%ToInteger") [expr_id "start"])
       (expr_let "actualStart"
        (expr_if
         (expr_op2 binary_op_lt (expr_id "relativeStart")
          (expr_number (JsNumber.of_int 0)))
         (expr_app (expr_id "%max")
          [expr_op2 binary_op_add (expr_id "len") (expr_id "relativeStart");
           expr_number (JsNumber.of_int 0)])
         (expr_app (expr_id "%min") [expr_id "relativeStart"; expr_id "len"]))
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
               [expr_op2 binary_op_add (expr_id "actualStart") (expr_id "k")])
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
                   (objattrs_intro (expr_string "Object") expr_true expr_null
                    expr_null expr_undefined)
                   [("value", property_data
                              (data_intro (expr_id "fromValue") expr_true
                               expr_false expr_false));
                    ("writable", property_data
                                 (data_intro expr_true expr_true expr_false
                                  expr_false));
                    ("enumerable", property_data
                                   (data_intro expr_true expr_true expr_false
                                    expr_false));
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
                  (expr_app (expr_id "writeToOLoop") [expr_id "actualStart"])))
                (expr_let "delLimit"
                 (expr_op2 binary_op_add
                  (expr_op2 binary_op_sub (expr_id "len")
                   (expr_id "actualDeleteCount")) (expr_id "itemCount"))
                 (expr_recc "deleteloop"
                  (expr_lambda ["k"]
                   (expr_if
                    (expr_op2 binary_op_gt (expr_id "k") (expr_id "delLimit"))
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
                 (expr_id "$newVal"))) (expr_id "A"))))))))))))))))
.
Definition ex_privsplitLambda :=  expr_string "String.prototype.split NYI" .
Definition ex_privsqrtLambda :=  expr_string "sqrt NYI" .
Definition ex_privstrconcatlambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
   (expr_app (expr_id "loop") [expr_number (JsNumber.of_int 0); expr_id "S"]))))
.
Definition ex_privstringSliceLambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
          [expr_number (JsNumber.of_int 0); expr_string ""]))))))))))
.
Definition ex_privstringToStringlambda := 
expr_get_obj_attr oattr_primval (expr_id "this")
.
Definition ex_privsubstringlambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
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
       (expr_app (expr_id "%min") [expr_id "finalStart"; expr_id "finalEnd"])
       (expr_let "to"
        (expr_app (expr_id "%max") [expr_id "finalStart"; expr_id "finalEnd"])
        (expr_recc "loop"
         (expr_lambda ["i"; "soFar"]
          (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "to"))
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int 1));
             expr_op2 binary_op_string_plus (expr_id "soFar")
             (expr_op2 binary_op_char_at (expr_id "S") (expr_id "i"))])
           (expr_id "soFar")))
         (expr_app (expr_id "loop") [expr_id "from"; expr_string ""]))))))))))
.
Definition ex_privtanLambda :=  expr_string "tan NYI" .
Definition ex_privtestlambda := 
expr_op1 unary_op_print
(expr_string
 "You used the es5.env testlambda.  Are you sure you didn't forget to include the regexp.js library, or regexp.env?")
.
Definition ex_privtlclambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_op1 unary_op_to_lower (expr_id "S")))
.
Definition ex_privtoExponentialLambda :=  expr_string "toExponential NYI" .
Definition ex_privtoFixedLambda := 
expr_let "f"
(expr_app (expr_id "%ToInteger")
 [expr_get_field (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_let "%or"
    (expr_op2 binary_op_lt (expr_id "f") (expr_number (JsNumber.of_int 0)))
    (expr_if (expr_id "%or") (expr_id "%or")
     (expr_op2 binary_op_gt (expr_id "f") (expr_number (JsNumber.of_int 20)))))
   (expr_throw
    (expr_app (expr_id "%JSError")
     [expr_object
      (objattrs_intro (expr_string "Object") expr_true
       (expr_id "%RangeErrorProto") expr_null expr_undefined) []])) expr_null)
  (expr_let "x"
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
     (expr_string "number")) (expr_id "this")
    (expr_get_obj_attr oattr_primval (expr_id "this")))
   (expr_seq
    (expr_if
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))
      expr_false expr_true) (expr_break "ret" (expr_string "NaN")) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_ge (expr_id "x") (expr_number (JsNumber.of_int 0)))
      (expr_break "ret" (expr_app (expr_id "%ToString") [expr_id "x"]))
      expr_null)
     (expr_break "ret"
      (expr_op2 binary_op_to_fixed (expr_id "x") (expr_id "f"))))))))
.
Definition ex_privtoLocaleStringlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "toString" (expr_get_field (expr_id "O") (expr_string "toString"))
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_obj_attr oattr_code (expr_id "toString")) expr_null)
  (expr_app (expr_id "%TypeError") [expr_string "toLocaleString"])
  (expr_app (expr_id "toString")
   [expr_id "O";
    expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
     expr_undefined) []])))
.
Definition ex_privtoPrecisionLambda :=  expr_string "toPrecision NYI" .
Definition ex_privtuclambda := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_op1 unary_op_to_upper (expr_id "S")))
.
Definition ex_privtwoArgObj := 
expr_app (expr_id "%mkArgsObj")
[expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_null
  expr_undefined)
 [("0", property_data
        (data_intro (expr_id "arg1") expr_false expr_false expr_false));
  ("1", property_data
        (data_intro (expr_id "arg2") expr_false expr_false expr_false));
  ("length", property_data
             (data_intro (expr_number (JsNumber.of_int 2)) expr_false
              expr_false expr_false))]]
.
Definition ex_privunescapeLambda :=  expr_string "unescape NYI" .
Definition ex_privunshiftlambda := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal" (expr_get_field (expr_id "O") (expr_string "length"))
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "argCount"
   (expr_get_field (expr_id "args") (expr_string "length"))
   (expr_seq
    (expr_recc "Oloop"
     (expr_lambda ["k"]
      (expr_if
       (expr_op2 binary_op_gt (expr_id "k") (expr_number (JsNumber.of_int 0)))
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
            (expr_set_field (expr_id "O") (expr_id "to") (expr_id "$newVal")))
           (expr_app (expr_id "Oloop")
            [expr_op2 binary_op_sub (expr_id "k")
             (expr_number (JsNumber.of_int 1))]))
          (expr_seq (expr_delete_field (expr_id "O") (expr_id "to"))
           (expr_app (expr_id "Oloop")
            [expr_op2 binary_op_sub (expr_id "k")
             (expr_number (JsNumber.of_int 1))]))))) expr_undefined))
     (expr_app (expr_id "Oloop") [expr_id "len"]))
    (expr_seq
     (expr_let "end" (expr_get_field (expr_id "args") (expr_string "length"))
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
         (expr_id "$newVal"))) (expr_id "finalLen"))))))))
.
Definition ex_privvalueOfLambda := 
expr_let "hasWrongProto"
(expr_if
 (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_proto (expr_id "this"))
  (expr_id "proto")) expr_false expr_true)
(expr_let "hasWrongTypeof"
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
   (expr_id "typestr")) expr_false expr_true)
 (expr_let "isntProto"
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "this") (expr_id "proto"))
   expr_false expr_true)
  (expr_if
   (expr_if
    (expr_if (expr_id "hasWrongProto") (expr_id "hasWrongTypeof") expr_false)
    (expr_id "isntProto") expr_false)
   (expr_app (expr_id "%TypeError") [expr_string "valueOf"])
   (expr_if (expr_id "hasWrongTypeof")
    (expr_get_obj_attr oattr_primval (expr_id "this")) (expr_id "this")))))
.
Definition ex_privvalueOflambda := 
expr_app (expr_id "%ToObject") [expr_id "this"]
.
Definition objCode :=  value_null .
Definition name_objCode :=  "objCode" .
Definition privJSError := 
value_closure (closure_intro [] None ["err"] ex_privJSError)
.
Definition name_privJSError :=  "%JSError" .
Definition privTypeErrorProto :=  value_object 7 .
Definition name_privTypeErrorProto :=  "%TypeErrorProto" .
Definition privMakeTypeError := 
value_closure
(closure_intro [("%TypeErrorProto", privTypeErrorProto)] None ["msg"]
 ex_privMakeTypeError)
.
Definition name_privMakeTypeError :=  "%MakeTypeError" .
Definition privThrowTypeErrorFun := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%MakeTypeError", privMakeTypeError)] None
 ["this"; "args"] ex_privThrowTypeErrorFun)
.
Definition name_privThrowTypeErrorFun :=  "%ThrowTypeErrorFun" .
Definition privTypeError := 
value_closure
(closure_intro [("%ThrowTypeErrorFun", privThrowTypeErrorFun)] None ["msg"]
 ex_privTypeError)
.
Definition name_privTypeError :=  "%TypeError" .
Definition privAppExprCheck := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["fun"; "this"; "args"]
 ex_privAppExprCheck)
.
Definition name_privAppExprCheck :=  "%AppExprCheck" .
Definition privArrayProto :=  value_object 58 .
Definition name_privArrayProto :=  "%ArrayProto" .
Definition privRangeErrorProto :=  value_object 50 .
Definition name_privRangeErrorProto :=  "%RangeErrorProto" .
Definition privToPrimitiveNum := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"]
 ex_privToPrimitiveNum)
.
Definition name_privToPrimitiveNum :=  "%ToPrimitiveNum" .
Definition privToNumber := 
value_closure
(closure_intro [("%ToPrimitiveNum", privToPrimitiveNum)] None ["x"]
 ex_privToNumber)
.
Definition name_privToNumber :=  "%ToNumber" .
Definition privToUint := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["n"; "limit"]
 ex_privToUint)
.
Definition name_privToUint :=  "%ToUint" .
Definition privToUint32 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"] ex_privToUint32)
.
Definition name_privToUint32 :=  "%ToUint32" .
Definition privMakeGetter := 
value_closure (closure_intro [] None ["f"] ex_privMakeGetter)
.
Definition name_privMakeGetter :=  "%MakeGetter" .
Definition privMakeSetter := 
value_closure (closure_intro [] None ["f"] ex_privMakeSetter)
.
Definition name_privMakeSetter :=  "%MakeSetter" .
Definition privToBoolean := 
value_closure (closure_intro [] None ["x"] ex_privToBoolean)
.
Definition name_privToBoolean :=  "%ToBoolean" .
Definition privToPrimitiveStr := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"]
 ex_privToPrimitiveStr)
.
Definition name_privToPrimitiveStr :=  "%ToPrimitiveStr" .
Definition privToPrimitiveHint := 
value_closure
(closure_intro
 [("%ToPrimitiveNum", privToPrimitiveNum);
  ("%ToPrimitiveStr", privToPrimitiveStr)] None ["val"; "hint"]
 ex_privToPrimitiveHint)
.
Definition name_privToPrimitiveHint :=  "%ToPrimitiveHint" .
Definition privToString := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 ex_privToString)
.
Definition name_privToString :=  "%ToString" .
Definition copy_when_defined := 
value_closure
(closure_intro [] None ["obj1"; "obj2"; "s"] ex_copy_when_defined)
.
Definition name_copy_when_defined :=  "copy-when-defined" .
Definition copy_access_desc := 
value_closure
(closure_intro [("copy-when-defined", copy_when_defined)] None
 ["obj1"; "obj2"] ex_copy_access_desc)
.
Definition name_copy_access_desc :=  "copy-access-desc" .
Definition copy_data_desc := 
value_closure
(closure_intro [("copy-when-defined", copy_when_defined)] None
 ["obj1"; "obj2"] ex_copy_data_desc)
.
Definition name_copy_data_desc :=  "copy-data-desc" .
Definition isAccessorDescriptor := 
value_closure (closure_intro [] None ["attr-obj"] ex_isAccessorDescriptor)
.
Definition name_isAccessorDescriptor :=  "isAccessorDescriptor" .
Definition isDataDescriptor := 
value_closure (closure_intro [] None ["attr-obj"] ex_isDataDescriptor)
.
Definition name_isDataDescriptor :=  "isDataDescriptor" .
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
 ex_privdefineOwnProperty)
.
Definition name_privdefineOwnProperty :=  "%defineOwnProperty" .
Definition privArrayConstructor := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%JSError", privJSError);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privArrayConstructor)
.
Definition name_privArrayConstructor :=  "%ArrayConstructor" .
Definition privArrayGlobalFuncObj :=  value_object 107 .
Definition name_privArrayGlobalFuncObj :=  "%ArrayGlobalFuncObj" .
Definition privArrayLengthChange := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["arr"; "newlen"]
 ex_privArrayLengthChange)
.
Definition name_privArrayLengthChange :=  "%ArrayLengthChange" .
Definition privToInt32 := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["n"] ex_privToInt32)
.
Definition name_privToInt32 :=  "%ToInt32" .
Definition privBitwiseAnd := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["l"; "r"] ex_privBitwiseAnd)
.
Definition name_privBitwiseAnd :=  "%BitwiseAnd" .
Definition privBitwiseInfix := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["l"; "r"; "op"]
 ex_privBitwiseInfix)
.
Definition name_privBitwiseInfix :=  "%BitwiseInfix" .
Definition privBitwiseNot := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["expr"] ex_privBitwiseNot)
.
Definition name_privBitwiseNot :=  "%BitwiseNot" .
Definition privBooleanProto :=  value_object 11 .
Definition name_privBooleanProto :=  "%BooleanProto" .
Definition privBooleanConstructor := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto); ("%ToBoolean", privToBoolean)] 
 None ["this"; "args"] ex_privBooleanConstructor)
.
Definition name_privBooleanConstructor :=  "%BooleanConstructor" .
Definition privBooleanGlobalFuncObj :=  value_object 33 .
Definition name_privBooleanGlobalFuncObj :=  "%BooleanGlobalFuncObj" .
Definition privCheckObjectCoercible := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 ex_privCheckObjectCoercible)
.
Definition name_privCheckObjectCoercible :=  "%CheckObjectCoercible" .
Definition privCompareOp := 
value_closure
(closure_intro
 [("%ToNumber", privToNumber); ("%ToPrimitiveHint", privToPrimitiveHint)]
 None ["l"; "r"; "LeftFirst"] ex_privCompareOp)
.
Definition name_privCompareOp :=  "%CompareOp" .
Definition privDateProto :=  value_object 173 .
Definition name_privDateProto :=  "%DateProto" .
Definition privmsPerDay :=  value_number (JsNumber.of_int 86400000) .
Definition name_privmsPerDay :=  "%msPerDay" .
Definition privMakeDate := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["day"; "time"]
 ex_privMakeDate)
.
Definition name_privMakeDate :=  "%MakeDate" .
Definition privDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"] ex_privDay)
.
Definition name_privDay :=  "%Day" .
Definition privDayFromYear := 
value_closure (closure_intro [] None ["y"] ex_privDayFromYear)
.
Definition name_privDayFromYear :=  "%DayFromYear" .
Definition privTimeFromYear := 
value_closure
(closure_intro
 [("%DayFromYear", privDayFromYear); ("%msPerDay", privmsPerDay)] None 
 ["y"] ex_privTimeFromYear)
.
Definition name_privTimeFromYear :=  "%TimeFromYear" .
Definition privYearFromTime := 
value_closure
(closure_intro [("%TimeFromYear", privTimeFromYear)] None ["t"]
 ex_privYearFromTime)
.
Definition name_privYearFromTime :=  "%YearFromTime" .
Definition privDayWithinYear := 
value_closure
(closure_intro
 [("%Day", privDay);
  ("%DayFromYear", privDayFromYear);
  ("%YearFromTime", privYearFromTime)] None ["t"] ex_privDayWithinYear)
.
Definition name_privDayWithinYear :=  "%DayWithinYear" .
Definition privDaysInYear := 
value_closure (closure_intro [] None ["y"] ex_privDaysInYear)
.
Definition name_privDaysInYear :=  "%DaysInYear" .
Definition privInLeapYear := 
value_closure
(closure_intro
 [("%DaysInYear", privDaysInYear); ("%YearFromTime", privYearFromTime)] 
 None ["t"] ex_privInLeapYear)
.
Definition name_privInLeapYear :=  "%InLeapYear" .
Definition privMonthFromTime := 
value_closure
(closure_intro
 [("%Day", privDay);
  ("%DayFromYear", privDayFromYear);
  ("%DayWithinYear", privDayWithinYear);
  ("%InLeapYear", privInLeapYear);
  ("%TypeError", privTypeError);
  ("%YearFromTime", privYearFromTime)] None ["t"] ex_privMonthFromTime)
.
Definition name_privMonthFromTime :=  "%MonthFromTime" .
Definition privDateFromTime := 
value_closure
(closure_intro
 [("%DayWithinYear", privDayWithinYear);
  ("%InLeapYear", privInLeapYear);
  ("%MonthFromTime", privMonthFromTime);
  ("%TypeError", privTypeError)] None ["t"] ex_privDateFromTime)
.
Definition name_privDateFromTime :=  "%DateFromTime" .
Definition privDaysInMonth := 
value_closure (closure_intro [] None ["m"; "leap"] ex_privDaysInMonth)
.
Definition name_privDaysInMonth :=  "%DaysInMonth" .
Definition privIsFinite := 
value_closure (closure_intro [] None ["n"] ex_privIsFinite)
.
Definition name_privIsFinite :=  "%IsFinite" .
Definition privToInteger := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["i"] ex_privToInteger)
.
Definition name_privToInteger :=  "%ToInteger" .
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
  ("%msPerDay", privmsPerDay)] None ["yr"; "mt"; "date"] ex_privMakeDay)
.
Definition name_privMakeDay :=  "%MakeDay" .
Definition privmsPerHour :=  value_number (JsNumber.of_int 3600000) .
Definition name_privmsPerHour :=  "%msPerHour" .
Definition privmsPerMin :=  value_number (JsNumber.of_int 60000) .
Definition name_privmsPerMin :=  "%msPerMin" .
Definition privmsPerSecond :=  value_number (JsNumber.of_int 1000) .
Definition name_privmsPerSecond :=  "%msPerSecond" .
Definition privMakeTime := 
value_closure
(closure_intro
 [("%IsFinite", privIsFinite);
  ("%ToInteger", privToInteger);
  ("%msPerHour", privmsPerHour);
  ("%msPerMin", privmsPerMin);
  ("%msPerSecond", privmsPerSecond)] None ["h"; "m"; "s"; "ms"]
 ex_privMakeTime)
.
Definition name_privMakeTime :=  "%MakeTime" .
Definition privTimeClip := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToInteger", privToInteger)]
 None ["t"] ex_privTimeClip)
.
Definition name_privTimeClip :=  "%TimeClip" .
Definition privToPrimitive := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 ex_privToPrimitive)
.
Definition name_privToPrimitive :=  "%ToPrimitive" .
Definition privUTC := 
value_closure (closure_intro [] None ["t"] ex_privUTC)
.
Definition name_privUTC :=  "%UTC" .
Definition privdateToStringLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privdateToStringLambda)
.
Definition name_privdateToStringLambda :=  "%dateToStringLambda" .
Definition privgetCurrentUTC := 
value_closure (closure_intro [] None [] ex_privgetCurrentUTC)
.
Definition name_privgetCurrentUTC :=  "%getCurrentUTC" .
Definition privparse := 
value_closure (closure_intro [] None ["v"] ex_privparse)
.
Definition name_privparse :=  "%parse" .
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
  ("%parse", privparse)] None ["this"; "args"] ex_privDateConstructor)
.
Definition name_privDateConstructor :=  "%DateConstructor" .
Definition privDateGlobalFuncObj :=  value_object 177 .
Definition name_privDateGlobalFuncObj :=  "%DateGlobalFuncObj" .
Definition privReferenceErrorProto :=  value_object 9 .
Definition name_privReferenceErrorProto :=  "%ReferenceErrorProto" .
Definition privIsJSError := 
value_closure (closure_intro [] None ["thing"] ex_privIsJSError)
.
Definition name_privIsJSError :=  "%IsJSError" .
Definition privErrorDispatch := 
value_closure
(closure_intro [("%IsJSError", privIsJSError); ("%TypeError", privTypeError)]
 None ["maybe-js-error"] ex_privErrorDispatch)
.
Definition name_privErrorDispatch :=  "%ErrorDispatch" .
Definition privUnwritableDispatch := 
value_closure
(closure_intro
 [("%ErrorDispatch", privErrorDispatch); ("%TypeError", privTypeError)] 
 None ["id"] ex_privUnwritableDispatch)
.
Definition name_privUnwritableDispatch :=  "%UnwritableDispatch" .
Definition privglobal :=  value_object 2 .
Definition name_privglobal :=  "%global" .
Definition privisUnbound := 
value_closure
(closure_intro [("%global", privglobal)] None ["context"; "id"]
 ex_privisUnbound)
.
Definition name_privisUnbound :=  "%isUnbound" .
Definition privNumberProto :=  value_object 12 .
Definition name_privNumberProto :=  "%NumberProto" .
Definition privStringIndices := 
value_closure (closure_intro [] None ["obj"; "s"] ex_privStringIndices)
.
Definition name_privStringIndices :=  "%StringIndices" .
Definition privStringProto :=  value_object 13 .
Definition name_privStringProto :=  "%StringProto" .
Definition privToObject := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto);
  ("%NumberProto", privNumberProto);
  ("%StringIndices", privStringIndices);
  ("%StringProto", privStringProto);
  ("%TypeError", privTypeError)] None ["o"] ex_privToObject)
.
Definition name_privToObject :=  "%ToObject" .
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
 ex_privset_property)
.
Definition name_privset_property :=  "%set-property" .
Definition privEnvCheckAssign := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto);
  ("%UnwritableDispatch", privUnwritableDispatch);
  ("%isUnbound", privisUnbound);
  ("%set-property", privset_property)] None
 ["context"; "id"; "val"; "strict"] ex_privEnvCheckAssign)
.
Definition name_privEnvCheckAssign :=  "%EnvCheckAssign" .
Definition privUnboundId := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto)] None ["id"]
 ex_privUnboundId)
.
Definition name_privUnboundId :=  "%UnboundId" .
Definition privEnvGet := 
value_closure
(closure_intro [("%UnboundId", privUnboundId); ("%isUnbound", privisUnbound)]
 None ["context"; "id"; "strict"] ex_privEnvGet)
.
Definition name_privEnvGet :=  "%EnvGet" .
Definition privEqEq := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] (Some "eqeq") ["x1"; "x2"]
 ex_privEqEq)
.
Definition name_privEqEq :=  "%EqEq" .
Definition privErrorProto :=  value_object 6 .
Definition name_privErrorProto :=  "%ErrorProto" .
Definition privErrorConstructor := 
value_closure
(closure_intro [("%ErrorProto", privErrorProto); ("%ToString", privToString)]
 None ["this"; "args"] ex_privErrorConstructor)
.
Definition name_privErrorConstructor :=  "%ErrorConstructor" .
Definition privErrorGlobalFuncObj :=  value_object 23 .
Definition name_privErrorGlobalFuncObj :=  "%ErrorGlobalFuncObj" .
Definition proto :=  value_object 46 .
Definition name_proto :=  "proto" .
Definition privEvalErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", proto)] None
 ["this"; "args"] ex_privEvalErrorConstructor)
.
Definition name_privEvalErrorConstructor :=  "%EvalErrorConstructor" .
Definition privEvalErrorGlobalFuncObj :=  value_object 49 .
Definition name_privEvalErrorGlobalFuncObj :=  "%EvalErrorGlobalFuncObj" .
Definition privglobalContext :=  value_object 3 .
Definition name_privglobalContext :=  "%globalContext" .
Definition privmakeContextVarDefiner := 
value_closure
(closure_intro
 [("%UnboundId", privUnboundId);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None [] ex_privmakeContextVarDefiner)
.
Definition name_privmakeContextVarDefiner :=  "%makeContextVarDefiner" .
Definition privmakeGlobalEnv :=  value_object 0 .
Definition name_privmakeGlobalEnv :=  "%makeGlobalEnv" .
Definition privconfigurableEval := 
value_closure
(closure_intro
 [("%makeContextVarDefiner", privmakeContextVarDefiner);
  ("%makeGlobalEnv", privmakeGlobalEnv)] None
 ["evalThis"; "evalContext"; "useStrict"; "args"] ex_privconfigurableEval)
.
Definition name_privconfigurableEval :=  "%configurableEval" .
Definition privevallambda := 
value_closure
(closure_intro
 [("%configurableEval", privconfigurableEval);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None ["this"; "args"]
 ex_privevallambda)
.
Definition name_privevallambda :=  "%evallambda" .
Definition privFunctionConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("%evallambda", privevallambda)]
 None ["this"; "args"] ex_privFunctionConstructor)
.
Definition name_privFunctionConstructor :=  "%FunctionConstructor" .
Definition privFunctionGlobalFuncObj :=  value_object 316 .
Definition name_privFunctionGlobalFuncObj :=  "%FunctionGlobalFuncObj" .
Definition privFunctionProto :=  value_object 4 .
Definition name_privFunctionProto :=  "%FunctionProto" .
Definition privGetterValue := 
value_closure (closure_intro [] None ["o"] ex_privGetterValue)
.
Definition name_privGetterValue :=  "%GetterValue" .
Definition privGreaterEqual := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 ex_privGreaterEqual)
.
Definition name_privGreaterEqual :=  "%GreaterEqual" .
Definition privGreaterThan := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 ex_privGreaterThan)
.
Definition name_privGreaterThan :=  "%GreaterThan" .
Definition privImmut := 
value_closure (closure_intro [] None ["obj"; "prop"] ex_privImmut)
.
Definition name_privImmut :=  "%Immut" .
Definition privIsObject := 
value_closure (closure_intro [] None ["o"] ex_privIsObject)
.
Definition name_privIsObject :=  "%IsObject" .
Definition privIsPrototypeOflambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 ex_privIsPrototypeOflambda)
.
Definition name_privIsPrototypeOflambda :=  "%IsPrototypeOflambda" .
Definition privLeftShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"] ex_privLeftShift)
.
Definition name_privLeftShift :=  "%LeftShift" .
Definition privLessEqual := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 ex_privLessEqual)
.
Definition name_privLessEqual :=  "%LessEqual" .
Definition privLessThan := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"]
 ex_privLessThan)
.
Definition name_privLessThan :=  "%LessThan" .
Definition privLocalTime := 
value_closure (closure_intro [] None ["t"] ex_privLocalTime)
.
Definition name_privLocalTime :=  "%LocalTime" .
Definition privMath :=  value_object 261 .
Definition name_privMath :=  "%Math" .
Definition privNativeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString)] None ["proto"]
 ex_privNativeErrorConstructor)
.
Definition name_privNativeErrorConstructor :=  "%NativeErrorConstructor" .
Definition privNumberConstructor := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto); ("%ToNumber", privToNumber)] None
 ["this"; "args"] ex_privNumberConstructor)
.
Definition name_privNumberConstructor :=  "%NumberConstructor" .
Definition privNumberGlobalFuncObj :=  value_object 26 .
Definition name_privNumberGlobalFuncObj :=  "%NumberGlobalFuncObj" .
Definition privObjectProto :=  value_object 1 .
Definition name_privObjectProto :=  "%ObjectProto" .
Definition privObjectConstructor := 
value_closure
(closure_intro
 [("%ObjectProto", privObjectProto); ("%ToObject", privToObject)] None
 ["this"; "args"] ex_privObjectConstructor)
.
Definition name_privObjectConstructor :=  "%ObjectConstructor" .
Definition privObjectGlobalFuncObj :=  value_object 35 .
Definition name_privObjectGlobalFuncObj :=  "%ObjectGlobalFuncObj" .
Definition privObjectTypeCheck := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 ex_privObjectTypeCheck)
.
Definition name_privObjectTypeCheck :=  "%ObjectTypeCheck" .
Definition privPostfixOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "fld"; "op"]
 ex_privPostfixOp)
.
Definition name_privPostfixOp :=  "%PostfixOp" .
Definition privPrimSub := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["l"; "r"] ex_privPrimSub)
.
Definition name_privPrimSub :=  "%PrimSub" .
Definition privPostDecrement := 
value_closure
(closure_intro [("%PostfixOp", privPostfixOp); ("%PrimSub", privPrimSub)]
 None ["obj"; "fld"] ex_privPostDecrement)
.
Definition name_privPostDecrement :=  "%PostDecrement" .
Definition privPrimAdd := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] None ["l"; "r"]
 ex_privPrimAdd)
.
Definition name_privPrimAdd :=  "%PrimAdd" .
Definition privPostIncrement := 
value_closure
(closure_intro [("%PostfixOp", privPostfixOp); ("%PrimAdd", privPrimAdd)]
 None ["obj"; "fld"] ex_privPostIncrement)
.
Definition name_privPostIncrement :=  "%PostIncrement" .
Definition privPrefixOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "fld"; "op"]
 ex_privPrefixOp)
.
Definition name_privPrefixOp :=  "%PrefixOp" .
Definition privPrefixDecrement := 
value_closure
(closure_intro [("%PrefixOp", privPrefixOp); ("%PrimSub", privPrimSub)] 
 None ["obj"; "fld"] ex_privPrefixDecrement)
.
Definition name_privPrefixDecrement :=  "%PrefixDecrement" .
Definition privPrefixIncrement := 
value_closure
(closure_intro [("%PrefixOp", privPrefixOp); ("%PrimAdd", privPrimAdd)] 
 None ["obj"; "fld"] ex_privPrefixIncrement)
.
Definition name_privPrefixIncrement :=  "%PrefixIncrement" .
Definition privPrimMultOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["l"; "r"; "op"]
 ex_privPrimMultOp)
.
Definition name_privPrimMultOp :=  "%PrimMultOp" .
Definition privPrimNew := 
value_closure
(closure_intro
 [("%AppExprCheck", privAppExprCheck);
  ("%IsObject", privIsObject);
  ("%ObjectProto", privObjectProto)] None ["constr"; "args"] ex_privPrimNew)
.
Definition name_privPrimNew :=  "%PrimNew" .
Definition privPropAccessorCheck := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto);
  ("%ToObject", privToObject)] None ["o"] ex_privPropAccessorCheck)
.
Definition name_privPropAccessorCheck :=  "%PropAccessorCheck" .
Definition privRangeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privRangeErrorProto)]
 None ["this"; "args"] ex_privRangeErrorConstructor)
.
Definition name_privRangeErrorConstructor :=  "%RangeErrorConstructor" .
Definition privRangeErrorGlobalFuncObj :=  value_object 51 .
Definition name_privRangeErrorGlobalFuncObj :=  "%RangeErrorGlobalFuncObj" .
Definition privReferenceErrorConstructor := 
value_closure
(closure_intro
 [("%ToString", privToString); ("proto", privReferenceErrorProto)] None
 ["this"; "args"] ex_privReferenceErrorConstructor)
.
Definition name_privReferenceErrorConstructor :=  "%ReferenceErrorConstructor" .
Definition privReferenceErrorGlobalFuncObj :=  value_object 53 .
Definition name_privReferenceErrorGlobalFuncObj :=  "%ReferenceErrorGlobalFuncObj" .
Definition privRegExpProto :=  value_object 253 .
Definition name_privRegExpProto :=  "%RegExpProto" .
Definition privRegExpConstructor := 
value_closure
(closure_intro [("%RegExpProto", privRegExpProto)] None ["this"; "args"]
 ex_privRegExpConstructor)
.
Definition name_privRegExpConstructor :=  "%RegExpConstructor" .
Definition privRegExpGlobalFuncObj :=  value_object 254 .
Definition name_privRegExpGlobalFuncObj :=  "%RegExpGlobalFuncObj" .
Definition privSetterValue := 
value_closure (closure_intro [] None ["o"] ex_privSetterValue)
.
Definition name_privSetterValue :=  "%SetterValue" .
Definition privSignedRightShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"] ex_privSignedRightShift)
.
Definition name_privSignedRightShift :=  "%SignedRightShift" .
Definition privStringConstructor := 
value_closure
(closure_intro
 [("%StringIndices", privStringIndices);
  ("%StringProto", privStringProto);
  ("%ToString", privToString)] None ["this"; "args"] ex_privStringConstructor)
.
Definition name_privStringConstructor :=  "%StringConstructor" .
Definition privStringGlobalFuncObj :=  value_object 29 .
Definition name_privStringGlobalFuncObj :=  "%StringGlobalFuncObj" .
Definition privStringIndexOf :=  value_object 162 .
Definition name_privStringIndexOf :=  "%StringIndexOf" .
Definition privmax := 
value_closure (closure_intro [] None ["a"; "b"] ex_privmax)
.
Definition name_privmax :=  "%max" .
Definition privmin := 
value_closure (closure_intro [] None ["a"; "b"] ex_privmin)
.
Definition name_privmin :=  "%min" .
Definition privStringIndexOflambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"] ex_privStringIndexOflambda)
.
Definition name_privStringIndexOflambda :=  "%StringIndexOflambda" .
Definition privStringLastIndexOf :=  value_object 164 .
Definition name_privStringLastIndexOf :=  "%StringLastIndexOf" .
Definition privSyntaxErrorProto :=  value_object 10 .
Definition name_privSyntaxErrorProto :=  "%SyntaxErrorProto" .
Definition privSyntaxError := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%SyntaxErrorProto", privSyntaxErrorProto)]
 None ["msg"] ex_privSyntaxError)
.
Definition name_privSyntaxError :=  "%SyntaxError" .
Definition privSyntaxErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privSyntaxErrorProto)]
 None ["this"; "args"] ex_privSyntaxErrorConstructor)
.
Definition name_privSyntaxErrorConstructor :=  "%SyntaxErrorConstructor" .
Definition privSyntaxErrorGlobalFuncObj :=  value_object 48 .
Definition name_privSyntaxErrorGlobalFuncObj :=  "%SyntaxErrorGlobalFuncObj" .
Definition privThrowReferenceError :=  value_object 14 .
Definition name_privThrowReferenceError :=  "%ThrowReferenceError" .
Definition privThrowSyntaxError :=  value_object 15 .
Definition name_privThrowSyntaxError :=  "%ThrowSyntaxError" .
Definition privThrowTypeError :=  value_object 8 .
Definition name_privThrowTypeError :=  "%ThrowTypeError" .
Definition privTimeWithinDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"] ex_privTimeWithinDay)
.
Definition name_privTimeWithinDay :=  "%TimeWithinDay" .
Definition privToJSError := 
value_closure
(closure_intro
 [("%IsJSError", privIsJSError); ("%MakeTypeError", privMakeTypeError)] 
 None ["maybe-js-error"] ex_privToJSError)
.
Definition name_privToJSError :=  "%ToJSError" .
Definition privToUint16 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"] ex_privToUint16)
.
Definition name_privToUint16 :=  "%ToUint16" .
Definition privTypeErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", privTypeErrorProto)]
 None ["this"; "args"] ex_privTypeErrorConstructor)
.
Definition name_privTypeErrorConstructor :=  "%TypeErrorConstructor" .
Definition privTypeErrorGlobalFuncObj :=  value_object 55 .
Definition name_privTypeErrorGlobalFuncObj :=  "%TypeErrorGlobalFuncObj" .
Definition privTypeof := 
value_closure (closure_intro [] None ["context"; "id"] ex_privTypeof)
.
Definition name_privTypeof :=  "%Typeof" .
Definition proto1 :=  value_object 56 .
Definition name_proto1 :=  "proto" .
Definition privURIErrorConstructor := 
value_closure
(closure_intro [("%ToString", privToString); ("proto", proto1)] None
 ["this"; "args"] ex_privURIErrorConstructor)
.
Definition name_privURIErrorConstructor :=  "%URIErrorConstructor" .
Definition privURIErrorGlobalFuncObj :=  value_object 57 .
Definition name_privURIErrorGlobalFuncObj :=  "%URIErrorGlobalFuncObj" .
Definition privUnaryNeg := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"] ex_privUnaryNeg)
.
Definition name_privUnaryNeg :=  "%UnaryNeg" .
Definition privUnaryPlus := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"] ex_privUnaryPlus)
.
Definition name_privUnaryPlus :=  "%UnaryPlus" .
Definition privUnsignedRightShift := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["l"; "r"]
 ex_privUnsignedRightShift)
.
Definition name_privUnsignedRightShift :=  "%UnsignedRightShift" .
Definition privacos :=  value_object 270 .
Definition name_privacos :=  "%acos" .
Definition privacosLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privacosLambda)
.
Definition name_privacosLambda :=  "%acosLambda" .
Definition privaiolambda := 
value_closure
(closure_intro
 [("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%max", privmax)] None ["this"; "args"] ex_privaiolambda)
.
Definition name_privaiolambda :=  "%aiolambda" .
Definition privaliolambda := 
value_closure
(closure_intro
 [("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%min", privmin)] None ["this"; "args"] ex_privaliolambda)
.
Definition name_privaliolambda :=  "%aliolambda" .
Definition privapply :=  value_object 19 .
Definition name_privapply :=  "%apply" .
Definition privmkArgsObjBase := 
value_closure
(closure_intro
 [("%MakeGetter", privMakeGetter);
  ("%MakeSetter", privMakeSetter);
  ("%ObjectProto", privObjectProto);
  ("%ThrowTypeError", privThrowTypeError);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["args"]
 ex_privmkArgsObjBase)
.
Definition name_privmkArgsObjBase :=  "%mkArgsObjBase" .
Definition privmkArgsObj := 
value_closure
(closure_intro [("%mkArgsObjBase", privmkArgsObjBase)] None ["args"]
 ex_privmkArgsObj)
.
Definition name_privmkArgsObj :=  "%mkArgsObj" .
Definition privapplylambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck); ("%mkArgsObj", privmkArgsObj)]
 None ["this"; "args"] ex_privapplylambda)
.
Definition name_privapplylambda :=  "%applylambda" .
Definition privarrayIndexOf :=  value_object 127 .
Definition name_privarrayIndexOf :=  "%arrayIndexOf" .
Definition privarrayLastIndexOf :=  value_object 130 .
Definition name_privarrayLastIndexOf :=  "%arrayLastIndexOf" .
Definition privarrayTLSlambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ToObject", privToObject);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%TypeErrorProto", privTypeErrorProto)] None ["this"; "args"]
 ex_privarrayTLSlambda)
.
Definition name_privarrayTLSlambda :=  "%arrayTLSlambda" .
Definition privarrayToLocaleString :=  value_object 99 .
Definition name_privarrayToLocaleString :=  "%arrayToLocaleString" .
Definition privarrayToString :=  value_object 96 .
Definition name_privarrayToString :=  "%arrayToString" .
Definition privobjectToStringlambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 ex_privobjectToStringlambda)
.
Definition name_privobjectToStringlambda :=  "%objectToStringlambda" .
Definition privarrayToStringlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%objectToStringlambda", privobjectToStringlambda)] None ["this"; "args"]
 ex_privarrayToStringlambda)
.
Definition name_privarrayToStringlambda :=  "%arrayToStringlambda" .
Definition privasin :=  value_object 272 .
Definition name_privasin :=  "%asin" .
Definition privasinLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privasinLambda)
.
Definition name_privasinLambda :=  "%asinLambda" .
Definition privatan :=  value_object 274 .
Definition name_privatan :=  "%atan" .
Definition privatan2 :=  value_object 276 .
Definition name_privatan2 :=  "%atan2" .
Definition privatan2Lambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privatan2Lambda)
.
Definition name_privatan2Lambda :=  "%atan2Lambda" .
Definition privatanLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privatanLambda)
.
Definition name_privatanLambda :=  "%atanLambda" .
Definition privbind :=  value_object 156 .
Definition name_privbind :=  "%bind" .
Definition privconcatLambda := 
value_closure
(closure_intro
 [("%ArrayConstructor", privArrayConstructor); ("%ToObject", privToObject)]
 None ["this"; "args"] ex_privconcatLambda)
.
Definition name_privconcatLambda :=  "%concatLambda" .
Definition privoneArgObj := 
value_closure
(closure_intro [("%mkArgsObj", privmkArgsObj)] None ["arg"] ex_privoneArgObj)
.
Definition name_privoneArgObj :=  "%oneArgObj" .
Definition privslicelambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privslicelambda)
.
Definition name_privslicelambda :=  "%slicelambda" .
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
  ("%slicelambda", privslicelambda)] None ["this"; "args"] ex_privbindLambda)
.
Definition name_privbindLambda :=  "%bindLambda" .
Definition privbooleanToString :=  value_object 30 .
Definition name_privbooleanToString :=  "%booleanToString" .
Definition privbooleanToStringlambda := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["this"; "args"]
 ex_privbooleanToStringlambda)
.
Definition name_privbooleanToStringlambda :=  "%booleanToStringlambda" .
Definition privbooleanValueOf :=  value_object 302 .
Definition name_privbooleanValueOf :=  "%booleanValueOf" .
Definition privcall :=  value_object 18 .
Definition name_privcall :=  "%call" .
Definition privlen := 
value_closure (closure_intro [] None ["list"] ex_privlen)
.
Definition name_privlen :=  "%len" .
Definition privslice_internal := 
value_closure
(closure_intro [] None ["list"; "min"; "max"] ex_privslice_internal)
.
Definition name_privslice_internal :=  "%slice_internal" .
Definition privcalllambda := 
value_closure
(closure_intro [("%len", privlen); ("%slice_internal", privslice_internal)]
 None ["this"; "args"] ex_privcalllambda)
.
Definition name_privcalllambda :=  "%calllambda" .
Definition privcharat :=  value_object 109 .
Definition name_privcharat :=  "%charat" .
Definition privcharatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"] ex_privcharatlambda)
.
Definition name_privcharatlambda :=  "%charatlambda" .
Definition privcharcodeat :=  value_object 112 .
Definition name_privcharcodeat :=  "%charcodeat" .
Definition privcharcodeatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"] ex_privcharcodeatlambda)
.
Definition name_privcharcodeatlambda :=  "%charcodeatlambda" .
Definition privconcat :=  value_object 101 .
Definition name_privconcat :=  "%concat" .
Definition privconsole :=  value_object 314 .
Definition name_privconsole :=  "%console" .
Definition privcos :=  value_object 278 .
Definition name_privcos :=  "%cos" .
Definition privcosLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privcosLambda)
.
Definition name_privcosLambda :=  "%cosLambda" .
Definition privcreate :=  value_object 64 .
Definition name_privcreate :=  "%create" .
Definition privdefinePropertylambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["this"; "args"]
 ex_privdefinePropertylambda)
.
Definition name_privdefinePropertylambda :=  "%definePropertylambda" .
Definition privdefinePropertiesLambda := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToObject", privToObject);
  ("%definePropertylambda", privdefinePropertylambda)] None ["this"; "args"]
 ex_privdefinePropertiesLambda)
.
Definition name_privdefinePropertiesLambda :=  "%definePropertiesLambda" .
Definition privcreateLambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%TypeError", privTypeError);
  ("%definePropertiesLambda", privdefinePropertiesLambda)] None
 ["this"; "args"] ex_privcreateLambda)
.
Definition name_privcreateLambda :=  "%createLambda" .
Definition privdateGetTimezoneOffset :=  value_object 178 .
Definition name_privdateGetTimezoneOffset :=  "%dateGetTimezoneOffset" .
Definition privdateGetTimezoneOffsetLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privdateGetTimezoneOffsetLambda)
.
Definition name_privdateGetTimezoneOffsetLambda :=  "%dateGetTimezoneOffsetLambda" .
Definition privdateToString :=  value_object 174 .
Definition name_privdateToString :=  "%dateToString" .
Definition privdateValueOf :=  value_object 176 .
Definition name_privdateValueOf :=  "%dateValueOf" .
Definition privdateValueOfLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privdateValueOfLambda)
.
Definition name_privdateValueOfLambda :=  "%dateValueOfLambda" .
Definition privdategetDate :=  value_object 182 .
Definition name_privdategetDate :=  "%dategetDate" .
Definition privdategetDateLambda := 
value_closure
(closure_intro
 [("%DateFromTime", privDateFromTime); ("%LocalTime", privLocalTime)] 
 None ["this"; "args"] ex_privdategetDateLambda)
.
Definition name_privdategetDateLambda :=  "%dategetDateLambda" .
Definition privdategetDay :=  value_object 180 .
Definition name_privdategetDay :=  "%dategetDay" .
Definition privdategetDayLambda := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["this"; "args"]
 ex_privdategetDayLambda)
.
Definition name_privdategetDayLambda :=  "%dategetDayLambda" .
Definition privdecodeURI :=  value_object 256 .
Definition name_privdecodeURI :=  "%decodeURI" .
Definition privdecodeURIComponent :=  value_object 257 .
Definition name_privdecodeURIComponent :=  "%decodeURIComponent" .
Definition privdecodeURIComponentLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privdecodeURIComponentLambda)
.
Definition name_privdecodeURIComponentLambda :=  "%decodeURIComponentLambda" .
Definition privdecodeURILambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privdecodeURILambda)
.
Definition name_privdecodeURILambda :=  "%decodeURILambda" .
Definition privdefine15Property := 
value_closure
(closure_intro [("%defineOwnProperty", privdefineOwnProperty)] None
 ["obj"; "field"; "prop"] ex_privdefine15Property)
.
Definition name_privdefine15Property :=  "%define15Property" .
Definition privmakeEnvGetter := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto); ("%UnboundId", privUnboundId)] 
 None ["object"; "id"] ex_privmakeEnvGetter)
.
Definition name_privmakeEnvGetter :=  "%makeEnvGetter" .
Definition privmakeEnvSetter := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%UnwritableDispatch", privUnwritableDispatch)] None ["object"; "id"]
 ex_privmakeEnvSetter)
.
Definition name_privmakeEnvSetter :=  "%makeEnvSetter" .
Definition privdefineGlobalAccessors := 
value_closure
(closure_intro
 [("%global", privglobal);
  ("%globalContext", privglobalContext);
  ("%makeEnvGetter", privmakeEnvGetter);
  ("%makeEnvSetter", privmakeEnvSetter)] None ["context"; "id"]
 ex_privdefineGlobalAccessors)
.
Definition name_privdefineGlobalAccessors :=  "%defineGlobalAccessors" .
Definition privdefineGlobalVar := 
value_closure
(closure_intro
 [("%global", privglobal);
  ("%makeEnvGetter", privmakeEnvGetter);
  ("%makeEnvSetter", privmakeEnvSetter)] None ["context"; "id"]
 ex_privdefineGlobalVar)
.
Definition name_privdefineGlobalVar :=  "%defineGlobalVar" .
Definition privdefineNYIProperty := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%TypeError", privTypeError);
  ("%define15Property", privdefine15Property)] None ["base"; "name"]
 ex_privdefineNYIProperty)
.
Definition name_privdefineNYIProperty :=  "%defineNYIProperty" .
Definition privdefineProperties :=  value_object 62 .
Definition name_privdefineProperties :=  "%defineProperties" .
Definition privdefineProperty :=  value_object 17 .
Definition name_privdefineProperty :=  "%defineProperty" .
Definition privencodeURI :=  value_object 258 .
Definition name_privencodeURI :=  "%encodeURI" .
Definition privencodeURIComponent :=  value_object 259 .
Definition name_privencodeURIComponent :=  "%encodeURIComponent" .
Definition privencodeURIComponentLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privencodeURIComponentLambda)
.
Definition name_privencodeURIComponentLambda :=  "%encodeURIComponentLambda" .
Definition privencodeURILambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privencodeURILambda)
.
Definition name_privencodeURILambda :=  "%encodeURILambda" .
Definition privescape :=  value_object 321 .
Definition name_privescape :=  "%escape" .
Definition privescapeLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privescapeLambda)
.
Definition name_privescapeLambda :=  "%escapeLambda" .
Definition privets :=  value_object 24 .
Definition name_privets :=  "%ets" .
Definition privetslambda := 
value_closure
(closure_intro [("%ToString", privToString); ("%TypeError", privTypeError)]
 None ["this"; "args"] ex_privetslambda)
.
Definition name_privetslambda :=  "%etslambda" .
Definition priveval :=  value_object 315 .
Definition name_priveval :=  "%eval" .
Definition privevery :=  value_object 144 .
Definition name_privevery :=  "%every" .
Definition priveverylambda := 
value_closure
(closure_intro
 [("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"] ex_priveverylambda)
.
Definition name_priveverylambda :=  "%everylambda" .
Definition privexp :=  value_object 260 .
Definition name_privexp :=  "%exp" .
Definition privexplambda := 
value_closure (closure_intro [] None [] ex_privexplambda)
.
Definition name_privexplambda :=  "%explambda" .
Definition privfilter :=  value_object 139 .
Definition name_privfilter :=  "%filter" .
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
 ex_privfilterlambda)
.
Definition name_privfilterlambda :=  "%filterlambda" .
Definition privforeach :=  value_object 133 .
Definition name_privforeach :=  "%foreach" .
Definition privforeachlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"] ex_privforeachlambda)
.
Definition name_privforeachlambda :=  "%foreachlambda" .
Definition privfreeze :=  value_object 68 .
Definition name_privfreeze :=  "%freeze" .
Definition privfreezelambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privfreezelambda)
.
Definition name_privfreezelambda :=  "%freezelambda" .
Definition privfromCharCode :=  value_object 80 .
Definition name_privfromCharCode :=  "%fromCharCode" .
Definition privfromcclambda := 
value_closure
(closure_intro [("%ToUint16", privToUint16)] None ["this"; "args"]
 ex_privfromcclambda)
.
Definition name_privfromcclambda :=  "%fromcclambda" .
Definition privfunctionToString :=  value_object 5 .
Definition name_privfunctionToString :=  "%functionToString" .
Definition privfunctionToStringlambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privfunctionToStringlambda)
.
Definition name_privfunctionToStringlambda :=  "%functionToStringlambda" .
Definition privgetMonth :=  value_object 172 .
Definition name_privgetMonth :=  "%getMonth" .
Definition privgetMonthlambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privgetMonthlambda)
.
Definition name_privgetMonthlambda :=  "%getMonthlambda" .
Definition privgetYear :=  value_object 171 .
Definition name_privgetYear :=  "%getYear" .
Definition privgetYearlambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privgetYearlambda)
.
Definition name_privgetYearlambda :=  "%getYearlambda" .
Definition privgopd :=  value_object 38 .
Definition name_privgopd :=  "%gopd" .
Definition privgopdLambda := 
value_closure
(closure_intro
 [("%ObjectProto", privObjectProto);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privgopdLambda)
.
Definition name_privgopdLambda :=  "%gopdLambda" .
Definition privgopn :=  value_object 59 .
Definition name_privgopn :=  "%gopn" .
Definition privgopnLambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto); ("%ObjectTypeCheck", privObjectTypeCheck)]
 None ["this"; "args"] ex_privgopnLambda)
.
Definition name_privgopnLambda :=  "%gopnLambda" .
Definition privgpo :=  value_object 36 .
Definition name_privgpo :=  "%gpo" .
Definition privgpoLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privgpoLambda)
.
Definition name_privgpoLambda :=  "%gpoLambda" .
Definition privhasOwnProperty :=  value_object 44 .
Definition name_privhasOwnProperty :=  "%hasOwnProperty" .
Definition privhasOwnPropertylambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privhasOwnPropertylambda)
.
Definition name_privhasOwnPropertylambda :=  "%hasOwnPropertylambda" .
Definition privin := 
value_closure
(closure_intro [("%ToString", privToString); ("%TypeError", privTypeError)]
 None ["l"; "r"] ex_privin)
.
Definition name_privin :=  "%in" .
Definition privinstanceof := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["l"; "r"]
 ex_privinstanceof)
.
Definition name_privinstanceof :=  "%instanceof" .
Definition privisExtensible :=  value_object 76 .
Definition name_privisExtensible :=  "%isExtensible" .
Definition privisExtensibleLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privisExtensibleLambda)
.
Definition name_privisExtensibleLambda :=  "%isExtensibleLambda" .
Definition privisFinite :=  value_object 317 .
Definition name_privisFinite :=  "%isFinite" .
Definition privisFiniteLambda := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToNumber", privToNumber)]
 None ["this"; "args"] ex_privisFiniteLambda)
.
Definition name_privisFiniteLambda :=  "%isFiniteLambda" .
Definition privisFrozen :=  value_object 72 .
Definition name_privisFrozen :=  "%isFrozen" .
Definition privisFrozenLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privisFrozenLambda)
.
Definition name_privisFrozenLambda :=  "%isFrozenLambda" .
Definition privisNaN :=  value_object 22 .
Definition name_privisNaN :=  "%isNaN" .
Definition privisNaNlambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privisNaNlambda)
.
Definition name_privisNaNlambda :=  "%isNaNlambda" .
Definition privisPrototypeOf :=  value_object 45 .
Definition name_privisPrototypeOf :=  "%isPrototypeOf" .
Definition privisSealed :=  value_object 74 .
Definition name_privisSealed :=  "%isSealed" .
Definition privisSealedLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privisSealedLambda)
.
Definition name_privisSealedLambda :=  "%isSealedLambda" .
Definition privjoin :=  value_object 82 .
Definition name_privjoin :=  "%join" .
Definition privjoinlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"] ex_privjoinlambda)
.
Definition name_privjoinlambda :=  "%joinlambda" .
Definition privkeys :=  value_object 78 .
Definition name_privkeys :=  "%keys" .
Definition privkeysLambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privkeysLambda)
.
Definition name_privkeysLambda :=  "%keysLambda" .
Definition privlocaleCompare :=  value_object 165 .
Definition name_privlocaleCompare :=  "%localeCompare" .
Definition privlocaleCompareLambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"]
 ex_privlocaleCompareLambda)
.
Definition name_privlocaleCompareLambda :=  "%localeCompareLambda" .
Definition privlog :=  value_object 313 .
Definition name_privlog :=  "%log" .
Definition privlogLambda := 
value_closure (closure_intro [] None ["o"; "s"] ex_privlogLambda)
.
Definition name_privlogLambda :=  "%logLambda" .
Definition privprimEach := 
value_closure
(closure_intro [("%ToString", privToString)] None ["arr"; "fn"]
 ex_privprimEach)
.
Definition name_privprimEach :=  "%primEach" .
Definition privpropertyNames := 
value_closure
(closure_intro [] None ["obj"; "get-non-enumerable"] ex_privpropertyNames)
.
Definition name_privpropertyNames :=  "%propertyNames" .
Definition privmakeWithContext := 
value_closure
(closure_intro
 [("%defineOwnProperty", privdefineOwnProperty);
  ("%primEach", privprimEach);
  ("%propertyNames", privpropertyNames)] None ["context"; "object"]
 ex_privmakeWithContext)
.
Definition name_privmakeWithContext :=  "%makeWithContext" .
Definition privmap :=  value_object 136 .
Definition name_privmap :=  "%map" .
Definition privmaplambda := 
value_closure
(closure_intro
 [("%ArrayProto", privArrayProto);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privmaplambda)
.
Definition name_privmaplambda :=  "%maplambda" .
Definition privmathAbs :=  value_object 268 .
Definition name_privmathAbs :=  "%mathAbs" .
Definition privmathAbsLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privmathAbsLambda)
.
Definition name_privmathAbsLambda :=  "%mathAbsLambda" .
Definition privmathCeil :=  value_object 292 .
Definition name_privmathCeil :=  "%mathCeil" .
Definition privmathCeilLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privmathCeilLambda)
.
Definition name_privmathCeilLambda :=  "%mathCeilLambda" .
Definition privmathFloor :=  value_object 294 .
Definition name_privmathFloor :=  "%mathFloor" .
Definition privmathFloorLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privmathFloorLambda)
.
Definition name_privmathFloorLambda :=  "%mathFloorLambda" .
Definition privmathLog :=  value_object 290 .
Definition name_privmathLog :=  "%mathLog" .
Definition privmathLogLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privmathLogLambda)
.
Definition name_privmathLogLambda :=  "%mathLogLambda" .
Definition privmathMax :=  value_object 265 .
Definition name_privmathMax :=  "%mathMax" .
Definition privminMaxLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None
 ["this"; "args"; "op"; "init"] ex_privminMaxLambda)
.
Definition name_privminMaxLambda :=  "%minMaxLambda" .
Definition privmathMaxLambda := 
value_closure
(closure_intro [("%max", privmax); ("%minMaxLambda", privminMaxLambda)] 
 None ["this"; "args"] ex_privmathMaxLambda)
.
Definition name_privmathMaxLambda :=  "%mathMaxLambda" .
Definition privmathMin :=  value_object 262 .
Definition name_privmathMin :=  "%mathMin" .
Definition privmathMinLambda := 
value_closure
(closure_intro [("%min", privmin); ("%minMaxLambda", privminMaxLambda)] 
 None ["this"; "args"] ex_privmathMinLambda)
.
Definition name_privmathMinLambda :=  "%mathMinLambda" .
Definition privmathPow :=  value_object 296 .
Definition name_privmathPow :=  "%mathPow" .
Definition privmathPowLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privmathPowLambda)
.
Definition name_privmathPowLambda :=  "%mathPowLambda" .
Definition privmaybeDirectEval := 
value_closure
(closure_intro
 [("%AppExprCheck", privAppExprCheck);
  ("%configurableEval", privconfigurableEval);
  ("%eval", priveval)] None ["theThis"; "theContext"; "args"; "strict"]
 ex_privmaybeDirectEval)
.
Definition name_privmaybeDirectEval :=  "%maybeDirectEval" .
Definition privmkNewArgsObj := 
value_closure
(closure_intro [("%mkArgsObjBase", privmkArgsObjBase)] None ["args"]
 ex_privmkNewArgsObj)
.
Definition name_privmkNewArgsObj :=  "%mkNewArgsObj" .
Definition privnumTLS :=  value_object 307 .
Definition name_privnumTLS :=  "%numTLS" .
Definition privtoLocaleStringlambda := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%TypeError", privTypeError)]
 None ["this"; "args"] ex_privtoLocaleStringlambda)
.
Definition name_privtoLocaleStringlambda :=  "%toLocaleStringlambda" .
Definition privnumTLSLambda := 
value_closure
(closure_intro
 [("%StringProto", privStringProto);
  ("%toLocaleStringlambda", privtoLocaleStringlambda)] None ["this"; "args"]
 ex_privnumTLSLambda)
.
Definition name_privnumTLSLambda :=  "%numTLSLambda" .
Definition privnumToStringAbstract := 
value_closure (closure_intro [] None ["n"; "r"] ex_privnumToStringAbstract)
.
Definition name_privnumToStringAbstract :=  "%numToStringAbstract" .
Definition privnumValueOf :=  value_object 300 .
Definition name_privnumValueOf :=  "%numValueOf" .
Definition privnumberToString :=  value_object 159 .
Definition name_privnumberToString :=  "%numberToString" .
Definition privnumberToStringlambda := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto);
  ("%ToInteger", privToInteger);
  ("%TypeErrorProto", privTypeErrorProto);
  ("%numToStringAbstract", privnumToStringAbstract)] None ["this"; "args"]
 ex_privnumberToStringlambda)
.
Definition name_privnumberToStringlambda :=  "%numberToStringlambda" .
Definition privobjectToString :=  value_object 40 .
Definition name_privobjectToString :=  "%objectToString" .
Definition privparseFloat :=  value_object 319 .
Definition name_privparseFloat :=  "%parseFloat" .
Definition privparseFloatLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privparseFloatLambda)
.
Definition name_privparseFloatLambda :=  "%parseFloatLambda" .
Definition privparseInt :=  value_object 255 .
Definition name_privparseInt :=  "%parseInt" .
Definition privparseIntlambda := 
value_closure
(closure_intro [("%ToString", privToString)] None ["this"; "args"]
 ex_privparseIntlambda)
.
Definition name_privparseIntlambda :=  "%parseIntlambda" .
Definition privpop :=  value_object 84 .
Definition name_privpop :=  "%pop" .
Definition privpoplambda := 
value_closure
(closure_intro
 [("%ToNumber", privToNumber);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"] ex_privpoplambda)
.
Definition name_privpoplambda :=  "%poplambda" .
Definition privpreventExtensions :=  value_object 70 .
Definition name_privpreventExtensions :=  "%preventExtensions" .
Definition privpreventExtensionsLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privpreventExtensionsLambda)
.
Definition name_privpreventExtensionsLambda :=  "%preventExtensionsLambda" .
Definition privprint :=  value_object 16 .
Definition name_privprint :=  "%print" .
Definition privprintlambda := 
value_closure
(closure_intro [("%ToString", privToString)] None ["o"; "s"]
 ex_privprintlambda)
.
Definition name_privprintlambda :=  "%printlambda" .
Definition privpropEnumlambda := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%ToString", privToString)]
 None ["this"; "args"] ex_privpropEnumlambda)
.
Definition name_privpropEnumlambda :=  "%propEnumlambda" .
Definition privpropertyIsEnumerable :=  value_object 41 .
Definition name_privpropertyIsEnumerable :=  "%propertyIsEnumerable" .
Definition privprotoOfField := 
value_closure
(closure_intro [] (Some "%protoOfField") ["object"; "fld"]
 ex_privprotoOfField)
.
Definition name_privprotoOfField :=  "%protoOfField" .
Definition privpush :=  value_object 87 .
Definition name_privpush :=  "%push" .
Definition privpushlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%set-property", privset_property)] None ["this"; "args"]
 ex_privpushlambda)
.
Definition name_privpushlambda :=  "%pushlambda" .
Definition privrandom :=  value_object 280 .
Definition name_privrandom :=  "%random" .
Definition privrandomLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privrandomLambda)
.
Definition name_privrandomLambda :=  "%randomLambda" .
Definition privreduce :=  value_object 141 .
Definition name_privreduce :=  "%reduce" .
Definition privreduceRight :=  value_object 150 .
Definition name_privreduceRight :=  "%reduceRight" .
Definition privreduceRightLambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"]
 ex_privreduceRightLambda)
.
Definition name_privreduceRightLambda :=  "%reduceRightLambda" .
Definition privreducelambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"] ex_privreducelambda)
.
Definition name_privreducelambda :=  "%reducelambda" .
Definition privreplace :=  value_object 163 .
Definition name_privreplace :=  "%replace" .
Definition privsubstringlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"] ex_privsubstringlambda)
.
Definition name_privsubstringlambda :=  "%substringlambda" .
Definition privtwoArgObj := 
value_closure
(closure_intro [("%mkArgsObj", privmkArgsObj)] None ["arg1"; "arg2"]
 ex_privtwoArgObj)
.
Definition name_privtwoArgObj :=  "%twoArgObj" .
Definition privreplacelambda := 
value_closure
(closure_intro
 [("%StringIndexOflambda", privStringIndexOflambda);
  ("%ToString", privToString);
  ("%oneArgObj", privoneArgObj);
  ("%substringlambda", privsubstringlambda);
  ("%twoArgObj", privtwoArgObj)] None ["this"; "args"] ex_privreplacelambda)
.
Definition name_privreplacelambda :=  "%replacelambda" .
Definition privresolveThis := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto);
  ("%NumberProto", privNumberProto);
  ("%StringProto", privStringProto);
  ("%global", privglobal)] None ["strict"; "obj"] ex_privresolveThis)
.
Definition name_privresolveThis :=  "%resolveThis" .
Definition privreverse :=  value_object 90 .
Definition name_privreverse :=  "%reverse" .
Definition privreverselambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"] ex_privreverselambda)
.
Definition name_privreverselambda :=  "%reverselambda" .
Definition privround :=  value_object 282 .
Definition name_privround :=  "%round" .
Definition privroundLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privroundLambda)
.
Definition name_privroundLambda :=  "%roundLambda" .
Definition privseal :=  value_object 66 .
Definition name_privseal :=  "%seal" .
Definition privsealLambda := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privsealLambda)
.
Definition name_privsealLambda :=  "%sealLambda" .
Definition privshift :=  value_object 93 .
Definition name_privshift :=  "%shift" .
Definition privshiftlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"] ex_privshiftlambda)
.
Definition name_privshiftlambda :=  "%shiftlambda" .
Definition privsin :=  value_object 284 .
Definition name_privsin :=  "%sin" .
Definition privsinLambda := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["this"; "args"]
 ex_privsinLambda)
.
Definition name_privsinLambda :=  "%sinLambda" .
Definition privslice :=  value_object 153 .
Definition name_privslice :=  "%slice" .
Definition privsliolambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToNumber", privToNumber);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"] ex_privsliolambda)
.
Definition name_privsliolambda :=  "%sliolambda" .
Definition privsome :=  value_object 147 .
Definition name_privsome :=  "%some" .
Definition privsomelambda := 
value_closure
(closure_intro
 [("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["this"; "args"] ex_privsomelambda)
.
Definition name_privsomelambda :=  "%somelambda" .
Definition privsort :=  value_object 104 .
Definition name_privsort :=  "%sort" .
Definition privsortlambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%TypeErrorProto", privTypeErrorProto)] None ["this"; "args"]
 ex_privsortlambda)
.
Definition name_privsortlambda :=  "%sortlambda" .
Definition privsplice :=  value_object 121 .
Definition name_privsplice :=  "%splice" .
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
  ("%min", privmin)] None ["this"; "args"] ex_privsplicelambda)
.
Definition name_privsplicelambda :=  "%splicelambda" .
Definition privsplit :=  value_object 169 .
Definition name_privsplit :=  "%split" .
Definition privsplitLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privsplitLambda)
.
Definition name_privsplitLambda :=  "%splitLambda" .
Definition privsqrt :=  value_object 286 .
Definition name_privsqrt :=  "%sqrt" .
Definition privsqrtLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privsqrtLambda)
.
Definition name_privsqrtLambda :=  "%sqrtLambda" .
Definition privstrconcat :=  value_object 115 .
Definition name_privstrconcat :=  "%strconcat" .
Definition privstrconcatlambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"] ex_privstrconcatlambda)
.
Definition name_privstrconcatlambda :=  "%strconcatlambda" .
Definition privstringSlice :=  value_object 166 .
Definition name_privstringSlice :=  "%stringSlice" .
Definition privstringSliceLambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["this"; "args"] ex_privstringSliceLambda)
.
Definition name_privstringSliceLambda :=  "%stringSliceLambda" .
Definition privstringToString :=  value_object 27 .
Definition name_privstringToString :=  "%stringToString" .
Definition privstringToStringlambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privstringToStringlambda)
.
Definition name_privstringToStringlambda :=  "%stringToStringlambda" .
Definition privstringValueOf :=  value_object 298 .
Definition name_privstringValueOf :=  "%stringValueOf" .
Definition privsubstring :=  value_object 118 .
Definition name_privsubstring :=  "%substring" .
Definition privtan :=  value_object 288 .
Definition name_privtan :=  "%tan" .
Definition privtanLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privtanLambda)
.
Definition name_privtanLambda :=  "%tanLambda" .
Definition privtest :=  value_object 252 .
Definition name_privtest :=  "%test" .
Definition privtestlambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privtestlambda)
.
Definition name_privtestlambda :=  "%testlambda" .
Definition privthrowUnboundIDErrors :=  value_false .
Definition name_privthrowUnboundIDErrors :=  "%throwUnboundIDErrors" .
Definition privtlclambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"] ex_privtlclambda)
.
Definition name_privtlclambda :=  "%tlclambda" .
Definition privtoExponential :=  value_object 309 .
Definition name_privtoExponential :=  "%toExponential" .
Definition privtoExponentialLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privtoExponentialLambda)
.
Definition name_privtoExponentialLambda :=  "%toExponentialLambda" .
Definition privtoFixed :=  value_object 304 .
Definition name_privtoFixed :=  "%toFixed" .
Definition privtoFixedLambda := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["this"; "args"] ex_privtoFixedLambda)
.
Definition name_privtoFixedLambda :=  "%toFixedLambda" .
Definition privtoLocaleString :=  value_object 42 .
Definition name_privtoLocaleString :=  "%toLocaleString" .
Definition privtoLowerCase :=  value_object 167 .
Definition name_privtoLowerCase :=  "%toLowerCase" .
Definition privtoPrecision :=  value_object 311 .
Definition name_privtoPrecision :=  "%toPrecision" .
Definition privtoPrecisionLambda := 
value_closure
(closure_intro [] None ["this"; "args"] ex_privtoPrecisionLambda)
.
Definition name_privtoPrecisionLambda :=  "%toPrecisionLambda" .
Definition privtoUpperCase :=  value_object 168 .
Definition name_privtoUpperCase :=  "%toUpperCase" .
Definition privtuclambda := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["this"; "args"] ex_privtuclambda)
.
Definition name_privtuclambda :=  "%tuclambda" .
Definition privunescape :=  value_object 323 .
Definition name_privunescape :=  "%unescape" .
Definition privunescapeLambda := 
value_closure (closure_intro [] None ["this"; "args"] ex_privunescapeLambda)
.
Definition name_privunescapeLambda :=  "%unescapeLambda" .
Definition privunshift :=  value_object 124 .
Definition name_privunshift :=  "%unshift" .
Definition privunshiftlambda := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["this"; "args"] ex_privunshiftlambda)
.
Definition name_privunshiftlambda :=  "%unshiftlambda" .
Definition privvalueOf :=  value_object 43 .
Definition name_privvalueOf :=  "%valueOf" .
Definition privvalueOfLambda := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None
 ["this"; "args"; "proto"; "typestr"] ex_privvalueOfLambda)
.
Definition name_privvalueOfLambda :=  "%valueOfLambda" .
Definition privvalueOflambda := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["this"; "args"]
 ex_privvalueOflambda)
.
Definition name_privvalueOflambda :=  "%valueOflambda" .
Definition isAccessorField := 
value_closure (closure_intro [] None ["obj"; "field"] ex_isAccessorField)
.
Definition name_isAccessorField :=  "isAccessorField" .
Definition isDataField := 
value_closure (closure_intro [] None ["obj"; "field"] ex_isDataField)
.
Definition name_isDataField :=  "isDataField" .
Definition isGenericDescriptor := 
value_closure
(closure_intro
 [("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["attr-obj"]
 ex_isGenericDescriptor)
.
Definition name_isGenericDescriptor :=  "isGenericDescriptor" .
Definition isGenericField := 
value_closure
(closure_intro
 [("isAccessorField", isAccessorField); ("isDataField", isDataField)] 
 None ["obj"; "field"] ex_isGenericField)
.
Definition name_isGenericField :=  "isGenericField" .
Definition objCode1 := 
value_closure (closure_intro [] None ["this"; "args"] ex_objCode1)
.
Definition name_objCode1 :=  "objCode" .
Definition objCode2 := 
value_closure
(closure_intro
 [("%JSError", privJSError);
  ("%ReferenceErrorProto", privReferenceErrorProto)] None ["this"; "args"]
 ex_objCode2)
.
Definition name_objCode2 :=  "objCode" .
Definition objCode3 := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%SyntaxErrorProto", privSyntaxErrorProto)]
 None ["this"; "args"] ex_objCode3)
.
Definition name_objCode3 :=  "objCode" .
Definition name :=  value_string "parse" .
Definition name_name :=  "name" .
Definition objCode4 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name)] None
 ["this"; "args"] ex_objCode4)
.
Definition name_objCode4 :=  "objCode" .
Definition name1 :=  value_string "UTC" .
Definition name_name1 :=  "name" .
Definition objCode5 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name1)] None
 ["this"; "args"] ex_objCode5)
.
Definition name_objCode5 :=  "objCode" .
Definition name2 :=  value_string "getTime" .
Definition name_name2 :=  "name" .
Definition objCode6 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name2)] None
 ["this"; "args"] ex_objCode6)
.
Definition name_objCode6 :=  "objCode" .
Definition name3 :=  value_string "getFullYear" .
Definition name_name3 :=  "name" .
Definition objCode7 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name3)] None
 ["this"; "args"] ex_objCode7)
.
Definition name_objCode7 :=  "objCode" .
Definition name4 :=  value_string "getUTCFullYear" .
Definition name_name4 :=  "name" .
Definition objCode8 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name4)] None
 ["this"; "args"] ex_objCode8)
.
Definition name_objCode8 :=  "objCode" .
Definition name5 :=  value_string "getUTCMonth" .
Definition name_name5 :=  "name" .
Definition objCode9 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name5)] None
 ["this"; "args"] ex_objCode9)
.
Definition name_objCode9 :=  "objCode" .
Definition name6 :=  value_string "getUTCDate" .
Definition name_name6 :=  "name" .
Definition objCode10 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name6)] None
 ["this"; "args"] ex_objCode10)
.
Definition name_objCode10 :=  "objCode" .
Definition name7 :=  value_string "getUTCDay" .
Definition name_name7 :=  "name" .
Definition objCode11 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name7)] None
 ["this"; "args"] ex_objCode11)
.
Definition name_objCode11 :=  "objCode" .
Definition name8 :=  value_string "getHours" .
Definition name_name8 :=  "name" .
Definition objCode12 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name8)] None
 ["this"; "args"] ex_objCode12)
.
Definition name_objCode12 :=  "objCode" .
Definition name9 :=  value_string "getUTCHours" .
Definition name_name9 :=  "name" .
Definition objCode13 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name9)] None
 ["this"; "args"] ex_objCode13)
.
Definition name_objCode13 :=  "objCode" .
Definition name10 :=  value_string "getMinutes" .
Definition name_name10 :=  "name" .
Definition objCode14 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name10)] None
 ["this"; "args"] ex_objCode14)
.
Definition name_objCode14 :=  "objCode" .
Definition name11 :=  value_string "getUTCMinutes" .
Definition name_name11 :=  "name" .
Definition objCode15 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name11)] None
 ["this"; "args"] ex_objCode15)
.
Definition name_objCode15 :=  "objCode" .
Definition name12 :=  value_string "getSeconds" .
Definition name_name12 :=  "name" .
Definition objCode16 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name12)] None
 ["this"; "args"] ex_objCode16)
.
Definition name_objCode16 :=  "objCode" .
Definition name13 :=  value_string "getUTCSeconds" .
Definition name_name13 :=  "name" .
Definition objCode17 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name13)] None
 ["this"; "args"] ex_objCode17)
.
Definition name_objCode17 :=  "objCode" .
Definition name14 :=  value_string "getMilliseconds" .
Definition name_name14 :=  "name" .
Definition objCode18 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name14)] None
 ["this"; "args"] ex_objCode18)
.
Definition name_objCode18 :=  "objCode" .
Definition name15 :=  value_string "getUTCMilliseconds" .
Definition name_name15 :=  "name" .
Definition objCode19 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name15)] None
 ["this"; "args"] ex_objCode19)
.
Definition name_objCode19 :=  "objCode" .
Definition name16 :=  value_string "setTime" .
Definition name_name16 :=  "name" .
Definition objCode20 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name16)] None
 ["this"; "args"] ex_objCode20)
.
Definition name_objCode20 :=  "objCode" .
Definition name17 :=  value_string "setMilliseconds" .
Definition name_name17 :=  "name" .
Definition objCode21 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name17)] None
 ["this"; "args"] ex_objCode21)
.
Definition name_objCode21 :=  "objCode" .
Definition name18 :=  value_string "setUTCMilliseconds" .
Definition name_name18 :=  "name" .
Definition objCode22 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name18)] None
 ["this"; "args"] ex_objCode22)
.
Definition name_objCode22 :=  "objCode" .
Definition name19 :=  value_string "setSeconds" .
Definition name_name19 :=  "name" .
Definition objCode23 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name19)] None
 ["this"; "args"] ex_objCode23)
.
Definition name_objCode23 :=  "objCode" .
Definition name20 :=  value_string "setUTCSeconds" .
Definition name_name20 :=  "name" .
Definition objCode24 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name20)] None
 ["this"; "args"] ex_objCode24)
.
Definition name_objCode24 :=  "objCode" .
Definition name21 :=  value_string "setMinutes" .
Definition name_name21 :=  "name" .
Definition objCode25 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name21)] None
 ["this"; "args"] ex_objCode25)
.
Definition name_objCode25 :=  "objCode" .
Definition name22 :=  value_string "setUTCMinutes" .
Definition name_name22 :=  "name" .
Definition objCode26 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name22)] None
 ["this"; "args"] ex_objCode26)
.
Definition name_objCode26 :=  "objCode" .
Definition name23 :=  value_string "setHours" .
Definition name_name23 :=  "name" .
Definition objCode27 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name23)] None
 ["this"; "args"] ex_objCode27)
.
Definition name_objCode27 :=  "objCode" .
Definition name24 :=  value_string "setUTCHours" .
Definition name_name24 :=  "name" .
Definition objCode28 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name24)] None
 ["this"; "args"] ex_objCode28)
.
Definition name_objCode28 :=  "objCode" .
Definition name25 :=  value_string "setDate" .
Definition name_name25 :=  "name" .
Definition objCode29 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name25)] None
 ["this"; "args"] ex_objCode29)
.
Definition name_objCode29 :=  "objCode" .
Definition name26 :=  value_string "setUTCDate" .
Definition name_name26 :=  "name" .
Definition objCode30 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name26)] None
 ["this"; "args"] ex_objCode30)
.
Definition name_objCode30 :=  "objCode" .
Definition name27 :=  value_string "setMonth" .
Definition name_name27 :=  "name" .
Definition objCode31 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name27)] None
 ["this"; "args"] ex_objCode31)
.
Definition name_objCode31 :=  "objCode" .
Definition name28 :=  value_string "setUTCMonth" .
Definition name_name28 :=  "name" .
Definition objCode32 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name28)] None
 ["this"; "args"] ex_objCode32)
.
Definition name_objCode32 :=  "objCode" .
Definition name29 :=  value_string "setFullYear" .
Definition name_name29 :=  "name" .
Definition objCode33 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name29)] None
 ["this"; "args"] ex_objCode33)
.
Definition name_objCode33 :=  "objCode" .
Definition name30 :=  value_string "setUTCFullYear" .
Definition name_name30 :=  "name" .
Definition objCode34 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name30)] None
 ["this"; "args"] ex_objCode34)
.
Definition name_objCode34 :=  "objCode" .
Definition name31 :=  value_string "toUTCString" .
Definition name_name31 :=  "name" .
Definition objCode35 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name31)] None
 ["this"; "args"] ex_objCode35)
.
Definition name_objCode35 :=  "objCode" .
Definition name32 :=  value_string "toGMTString" .
Definition name_name32 :=  "name" .
Definition objCode36 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name32)] None
 ["this"; "args"] ex_objCode36)
.
Definition name_objCode36 :=  "objCode" .
Definition name33 :=  value_string "setYear" .
Definition name_name33 :=  "name" .
Definition objCode37 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name33)] None
 ["this"; "args"] ex_objCode37)
.
Definition name_objCode37 :=  "objCode" .
Definition objCode38 := 
value_closure
(closure_intro
 [("%StringProto", privStringProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"] ex_objCode38)
.
Definition name_objCode38 :=  "objCode" .
Definition objCode39 := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"] ex_objCode39)
.
Definition name_objCode39 :=  "objCode" .
Definition objCode40 := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto); ("%valueOfLambda", privvalueOfLambda)]
 None ["this"; "args"] ex_objCode40)
.
Definition name_objCode40 :=  "objCode" .
Definition ctx_items := 
[(name_privAppExprCheck, privAppExprCheck);
 (name_privArrayConstructor, privArrayConstructor);
 (name_privArrayGlobalFuncObj, privArrayGlobalFuncObj);
 (name_privArrayLengthChange, privArrayLengthChange);
 (name_privArrayProto, privArrayProto);
 (name_privBitwiseAnd, privBitwiseAnd);
 (name_privBitwiseInfix, privBitwiseInfix);
 (name_privBitwiseNot, privBitwiseNot);
 (name_privBooleanConstructor, privBooleanConstructor);
 (name_privBooleanGlobalFuncObj, privBooleanGlobalFuncObj);
 (name_privBooleanProto, privBooleanProto);
 (name_privCheckObjectCoercible, privCheckObjectCoercible);
 (name_privCompareOp, privCompareOp);
 (name_privDateConstructor, privDateConstructor);
 (name_privDateFromTime, privDateFromTime);
 (name_privDateGlobalFuncObj, privDateGlobalFuncObj);
 (name_privDateProto, privDateProto);
 (name_privDay, privDay);
 (name_privDayFromYear, privDayFromYear);
 (name_privDayWithinYear, privDayWithinYear);
 (name_privDaysInMonth, privDaysInMonth);
 (name_privDaysInYear, privDaysInYear);
 (name_privEnvCheckAssign, privEnvCheckAssign);
 (name_privEnvGet, privEnvGet);
 (name_privEqEq, privEqEq);
 (name_privErrorConstructor, privErrorConstructor);
 (name_privErrorDispatch, privErrorDispatch);
 (name_privErrorGlobalFuncObj, privErrorGlobalFuncObj);
 (name_privErrorProto, privErrorProto);
 (name_privEvalErrorConstructor, privEvalErrorConstructor);
 (name_privEvalErrorGlobalFuncObj, privEvalErrorGlobalFuncObj);
 (name_proto, proto);
 (name_privFunctionConstructor, privFunctionConstructor);
 (name_privFunctionGlobalFuncObj, privFunctionGlobalFuncObj);
 (name_privFunctionProto, privFunctionProto);
 (name_privGetterValue, privGetterValue);
 (name_privGreaterEqual, privGreaterEqual);
 (name_privGreaterThan, privGreaterThan);
 (name_privImmut, privImmut);
 (name_privInLeapYear, privInLeapYear);
 (name_privIsFinite, privIsFinite);
 (name_privIsJSError, privIsJSError);
 (name_privIsObject, privIsObject);
 (name_privIsPrototypeOflambda, privIsPrototypeOflambda);
 (name_privJSError, privJSError);
 (name_privLeftShift, privLeftShift);
 (name_privLessEqual, privLessEqual);
 (name_privLessThan, privLessThan);
 (name_privLocalTime, privLocalTime);
 (name_privMakeDate, privMakeDate);
 (name_privMakeDay, privMakeDay);
 (name_privMakeGetter, privMakeGetter);
 (name_privMakeSetter, privMakeSetter);
 (name_privMakeTime, privMakeTime);
 (name_privMakeTypeError, privMakeTypeError);
 (name_privMath, privMath);
 (name_privMonthFromTime, privMonthFromTime);
 (name_privNativeErrorConstructor, privNativeErrorConstructor);
 (name_privNumberConstructor, privNumberConstructor);
 (name_privNumberGlobalFuncObj, privNumberGlobalFuncObj);
 (name_privNumberProto, privNumberProto);
 (name_privObjectConstructor, privObjectConstructor);
 (name_privObjectGlobalFuncObj, privObjectGlobalFuncObj);
 (name_privObjectProto, privObjectProto);
 (name_privObjectTypeCheck, privObjectTypeCheck);
 (name_privPostDecrement, privPostDecrement);
 (name_privPostIncrement, privPostIncrement);
 (name_privPostfixOp, privPostfixOp);
 (name_privPrefixDecrement, privPrefixDecrement);
 (name_privPrefixIncrement, privPrefixIncrement);
 (name_privPrefixOp, privPrefixOp);
 (name_privPrimAdd, privPrimAdd);
 (name_privPrimMultOp, privPrimMultOp);
 (name_privPrimNew, privPrimNew);
 (name_privPrimSub, privPrimSub);
 (name_privPropAccessorCheck, privPropAccessorCheck);
 (name_privRangeErrorConstructor, privRangeErrorConstructor);
 (name_privRangeErrorGlobalFuncObj, privRangeErrorGlobalFuncObj);
 (name_privRangeErrorProto, privRangeErrorProto);
 (name_privReferenceErrorConstructor, privReferenceErrorConstructor);
 (name_privReferenceErrorGlobalFuncObj, privReferenceErrorGlobalFuncObj);
 (name_privReferenceErrorProto, privReferenceErrorProto);
 (name_privRegExpConstructor, privRegExpConstructor);
 (name_privRegExpGlobalFuncObj, privRegExpGlobalFuncObj);
 (name_privRegExpProto, privRegExpProto);
 (name_privSetterValue, privSetterValue);
 (name_privSignedRightShift, privSignedRightShift);
 (name_privStringConstructor, privStringConstructor);
 (name_privStringGlobalFuncObj, privStringGlobalFuncObj);
 (name_privStringIndexOf, privStringIndexOf);
 (name_privStringIndexOflambda, privStringIndexOflambda);
 (name_privStringIndices, privStringIndices);
 (name_privStringLastIndexOf, privStringLastIndexOf);
 (name_privStringProto, privStringProto);
 (name_privSyntaxError, privSyntaxError);
 (name_privSyntaxErrorConstructor, privSyntaxErrorConstructor);
 (name_privSyntaxErrorGlobalFuncObj, privSyntaxErrorGlobalFuncObj);
 (name_privSyntaxErrorProto, privSyntaxErrorProto);
 (name_privThrowReferenceError, privThrowReferenceError);
 (name_privThrowSyntaxError, privThrowSyntaxError);
 (name_privThrowTypeError, privThrowTypeError);
 (name_privThrowTypeErrorFun, privThrowTypeErrorFun);
 (name_privTimeClip, privTimeClip);
 (name_privTimeFromYear, privTimeFromYear);
 (name_privTimeWithinDay, privTimeWithinDay);
 (name_privToBoolean, privToBoolean);
 (name_privToInt32, privToInt32);
 (name_privToInteger, privToInteger);
 (name_privToJSError, privToJSError);
 (name_privToNumber, privToNumber);
 (name_privToObject, privToObject);
 (name_privToPrimitive, privToPrimitive);
 (name_privToPrimitiveHint, privToPrimitiveHint);
 (name_privToPrimitiveNum, privToPrimitiveNum);
 (name_privToPrimitiveStr, privToPrimitiveStr);
 (name_privToString, privToString);
 (name_privToUint, privToUint);
 (name_privToUint16, privToUint16);
 (name_privToUint32, privToUint32);
 (name_privTypeError, privTypeError);
 (name_privTypeErrorConstructor, privTypeErrorConstructor);
 (name_privTypeErrorGlobalFuncObj, privTypeErrorGlobalFuncObj);
 (name_privTypeErrorProto, privTypeErrorProto);
 (name_privTypeof, privTypeof);
 (name_privURIErrorConstructor, privURIErrorConstructor);
 (name_privURIErrorGlobalFuncObj, privURIErrorGlobalFuncObj);
 (name_proto1, proto1);
 (name_privUTC, privUTC);
 (name_privUnaryNeg, privUnaryNeg);
 (name_privUnaryPlus, privUnaryPlus);
 (name_privUnboundId, privUnboundId);
 (name_privUnsignedRightShift, privUnsignedRightShift);
 (name_privUnwritableDispatch, privUnwritableDispatch);
 (name_privYearFromTime, privYearFromTime);
 (name_privacos, privacos);
 (name_privacosLambda, privacosLambda);
 (name_privaiolambda, privaiolambda);
 (name_privaliolambda, privaliolambda);
 (name_privapply, privapply);
 (name_privapplylambda, privapplylambda);
 (name_privarrayIndexOf, privarrayIndexOf);
 (name_privarrayLastIndexOf, privarrayLastIndexOf);
 (name_privarrayTLSlambda, privarrayTLSlambda);
 (name_privarrayToLocaleString, privarrayToLocaleString);
 (name_privarrayToString, privarrayToString);
 (name_privarrayToStringlambda, privarrayToStringlambda);
 (name_privasin, privasin);
 (name_privasinLambda, privasinLambda);
 (name_privatan, privatan);
 (name_privatan2, privatan2);
 (name_privatan2Lambda, privatan2Lambda);
 (name_privatanLambda, privatanLambda);
 (name_privbind, privbind);
 (name_privbindLambda, privbindLambda);
 (name_privbooleanToString, privbooleanToString);
 (name_privbooleanToStringlambda, privbooleanToStringlambda);
 (name_privbooleanValueOf, privbooleanValueOf);
 (name_privcall, privcall);
 (name_privcalllambda, privcalllambda);
 (name_privcharat, privcharat);
 (name_privcharatlambda, privcharatlambda);
 (name_privcharcodeat, privcharcodeat);
 (name_privcharcodeatlambda, privcharcodeatlambda);
 (name_privconcat, privconcat);
 (name_privconcatLambda, privconcatLambda);
 (name_privconfigurableEval, privconfigurableEval);
 (name_privconsole, privconsole);
 (name_privcos, privcos);
 (name_privcosLambda, privcosLambda);
 (name_privcreate, privcreate);
 (name_privcreateLambda, privcreateLambda);
 (name_privdateGetTimezoneOffset, privdateGetTimezoneOffset);
 (name_privdateGetTimezoneOffsetLambda, privdateGetTimezoneOffsetLambda);
 (name_privdateToString, privdateToString);
 (name_privdateToStringLambda, privdateToStringLambda);
 (name_privdateValueOf, privdateValueOf);
 (name_privdateValueOfLambda, privdateValueOfLambda);
 (name_privdategetDate, privdategetDate);
 (name_privdategetDateLambda, privdategetDateLambda);
 (name_privdategetDay, privdategetDay);
 (name_privdategetDayLambda, privdategetDayLambda);
 (name_privdecodeURI, privdecodeURI);
 (name_privdecodeURIComponent, privdecodeURIComponent);
 (name_privdecodeURIComponentLambda, privdecodeURIComponentLambda);
 (name_privdecodeURILambda, privdecodeURILambda);
 (name_privdefine15Property, privdefine15Property);
 (name_privdefineGlobalAccessors, privdefineGlobalAccessors);
 (name_privdefineGlobalVar, privdefineGlobalVar);
 (name_privdefineNYIProperty, privdefineNYIProperty);
 (name_privdefineOwnProperty, privdefineOwnProperty);
 (name_privdefineProperties, privdefineProperties);
 (name_privdefinePropertiesLambda, privdefinePropertiesLambda);
 (name_privdefineProperty, privdefineProperty);
 (name_privdefinePropertylambda, privdefinePropertylambda);
 (name_privencodeURI, privencodeURI);
 (name_privencodeURIComponent, privencodeURIComponent);
 (name_privencodeURIComponentLambda, privencodeURIComponentLambda);
 (name_privencodeURILambda, privencodeURILambda);
 (name_privescape, privescape);
 (name_privescapeLambda, privescapeLambda);
 (name_privets, privets);
 (name_privetslambda, privetslambda);
 (name_priveval, priveval);
 (name_privevallambda, privevallambda);
 (name_privevery, privevery);
 (name_priveverylambda, priveverylambda);
 (name_privexp, privexp);
 (name_privexplambda, privexplambda);
 (name_privfilter, privfilter);
 (name_privfilterlambda, privfilterlambda);
 (name_privforeach, privforeach);
 (name_privforeachlambda, privforeachlambda);
 (name_privfreeze, privfreeze);
 (name_privfreezelambda, privfreezelambda);
 (name_privfromCharCode, privfromCharCode);
 (name_privfromcclambda, privfromcclambda);
 (name_privfunctionToString, privfunctionToString);
 (name_privfunctionToStringlambda, privfunctionToStringlambda);
 (name_privgetCurrentUTC, privgetCurrentUTC);
 (name_privgetMonth, privgetMonth);
 (name_privgetMonthlambda, privgetMonthlambda);
 (name_privgetYear, privgetYear);
 (name_privgetYearlambda, privgetYearlambda);
 (name_privglobal, privglobal);
 (name_privglobalContext, privglobalContext);
 (name_privgopd, privgopd);
 (name_privgopdLambda, privgopdLambda);
 (name_privgopn, privgopn);
 (name_privgopnLambda, privgopnLambda);
 (name_privgpo, privgpo);
 (name_privgpoLambda, privgpoLambda);
 (name_privhasOwnProperty, privhasOwnProperty);
 (name_privhasOwnPropertylambda, privhasOwnPropertylambda);
 (name_privin, privin);
 (name_privinstanceof, privinstanceof);
 (name_privisExtensible, privisExtensible);
 (name_privisExtensibleLambda, privisExtensibleLambda);
 (name_privisFinite, privisFinite);
 (name_privisFiniteLambda, privisFiniteLambda);
 (name_privisFrozen, privisFrozen);
 (name_privisFrozenLambda, privisFrozenLambda);
 (name_privisNaN, privisNaN);
 (name_privisNaNlambda, privisNaNlambda);
 (name_privisPrototypeOf, privisPrototypeOf);
 (name_privisSealed, privisSealed);
 (name_privisSealedLambda, privisSealedLambda);
 (name_privisUnbound, privisUnbound);
 (name_privjoin, privjoin);
 (name_privjoinlambda, privjoinlambda);
 (name_privkeys, privkeys);
 (name_privkeysLambda, privkeysLambda);
 (name_privlen, privlen);
 (name_privlocaleCompare, privlocaleCompare);
 (name_privlocaleCompareLambda, privlocaleCompareLambda);
 (name_privlog, privlog);
 (name_privlogLambda, privlogLambda);
 (name_privmakeContextVarDefiner, privmakeContextVarDefiner);
 (name_privmakeEnvGetter, privmakeEnvGetter);
 (name_privmakeEnvSetter, privmakeEnvSetter);
 (name_privmakeGlobalEnv, privmakeGlobalEnv);
 (name_privmakeWithContext, privmakeWithContext);
 (name_privmap, privmap);
 (name_privmaplambda, privmaplambda);
 (name_privmathAbs, privmathAbs);
 (name_privmathAbsLambda, privmathAbsLambda);
 (name_privmathCeil, privmathCeil);
 (name_privmathCeilLambda, privmathCeilLambda);
 (name_privmathFloor, privmathFloor);
 (name_privmathFloorLambda, privmathFloorLambda);
 (name_privmathLog, privmathLog);
 (name_privmathLogLambda, privmathLogLambda);
 (name_privmathMax, privmathMax);
 (name_privmathMaxLambda, privmathMaxLambda);
 (name_privmathMin, privmathMin);
 (name_privmathMinLambda, privmathMinLambda);
 (name_privmathPow, privmathPow);
 (name_privmathPowLambda, privmathPowLambda);
 (name_privmax, privmax);
 (name_privmaybeDirectEval, privmaybeDirectEval);
 (name_privmin, privmin);
 (name_privminMaxLambda, privminMaxLambda);
 (name_privmkArgsObj, privmkArgsObj);
 (name_privmkArgsObjBase, privmkArgsObjBase);
 (name_privmkNewArgsObj, privmkNewArgsObj);
 (name_privmsPerDay, privmsPerDay);
 (name_privmsPerHour, privmsPerHour);
 (name_privmsPerMin, privmsPerMin);
 (name_privmsPerSecond, privmsPerSecond);
 (name_privglobalContext, privglobalContext);
 (name_privnumTLS, privnumTLS);
 (name_privnumTLSLambda, privnumTLSLambda);
 (name_privnumToStringAbstract, privnumToStringAbstract);
 (name_privnumValueOf, privnumValueOf);
 (name_privnumberToString, privnumberToString);
 (name_privnumberToStringlambda, privnumberToStringlambda);
 (name_privobjectToString, privobjectToString);
 (name_privobjectToStringlambda, privobjectToStringlambda);
 (name_privoneArgObj, privoneArgObj);
 (name_privparse, privparse);
 (name_privparseFloat, privparseFloat);
 (name_privparseFloatLambda, privparseFloatLambda);
 (name_privparseInt, privparseInt);
 (name_privparseIntlambda, privparseIntlambda);
 (name_privpop, privpop);
 (name_privpoplambda, privpoplambda);
 (name_privpreventExtensions, privpreventExtensions);
 (name_privpreventExtensionsLambda, privpreventExtensionsLambda);
 (name_privprimEach, privprimEach);
 (name_privprint, privprint);
 (name_privprintlambda, privprintlambda);
 (name_privpropEnumlambda, privpropEnumlambda);
 (name_privpropertyIsEnumerable, privpropertyIsEnumerable);
 (name_privpropertyNames, privpropertyNames);
 (name_privprotoOfField, privprotoOfField);
 (name_privpush, privpush);
 (name_privpushlambda, privpushlambda);
 (name_privrandom, privrandom);
 (name_privrandomLambda, privrandomLambda);
 (name_privreduce, privreduce);
 (name_privreduceRight, privreduceRight);
 (name_privreduceRightLambda, privreduceRightLambda);
 (name_privreducelambda, privreducelambda);
 (name_privreplace, privreplace);
 (name_privreplacelambda, privreplacelambda);
 (name_privresolveThis, privresolveThis);
 (name_privreverse, privreverse);
 (name_privreverselambda, privreverselambda);
 (name_privround, privround);
 (name_privroundLambda, privroundLambda);
 (name_privseal, privseal);
 (name_privsealLambda, privsealLambda);
 (name_privset_property, privset_property);
 (name_privshift, privshift);
 (name_privshiftlambda, privshiftlambda);
 (name_privsin, privsin);
 (name_privsinLambda, privsinLambda);
 (name_privslice, privslice);
 (name_privslice_internal, privslice_internal);
 (name_privslicelambda, privslicelambda);
 (name_privsliolambda, privsliolambda);
 (name_privsome, privsome);
 (name_privsomelambda, privsomelambda);
 (name_privsort, privsort);
 (name_privsortlambda, privsortlambda);
 (name_privsplice, privsplice);
 (name_privsplicelambda, privsplicelambda);
 (name_privsplit, privsplit);
 (name_privsplitLambda, privsplitLambda);
 (name_privsqrt, privsqrt);
 (name_privsqrtLambda, privsqrtLambda);
 (name_privstrconcat, privstrconcat);
 (name_privstrconcatlambda, privstrconcatlambda);
 (name_privglobalContext, privglobalContext);
 (name_privstringSlice, privstringSlice);
 (name_privstringSliceLambda, privstringSliceLambda);
 (name_privstringToString, privstringToString);
 (name_privstringToStringlambda, privstringToStringlambda);
 (name_privstringValueOf, privstringValueOf);
 (name_privsubstring, privsubstring);
 (name_privsubstringlambda, privsubstringlambda);
 (name_privtan, privtan);
 (name_privtanLambda, privtanLambda);
 (name_privtest, privtest);
 (name_privtestlambda, privtestlambda);
 (name_privglobal, privglobal);
 (name_privthrowUnboundIDErrors, privthrowUnboundIDErrors);
 (name_privtlclambda, privtlclambda);
 (name_privtoExponential, privtoExponential);
 (name_privtoExponentialLambda, privtoExponentialLambda);
 (name_privtoFixed, privtoFixed);
 (name_privtoFixedLambda, privtoFixedLambda);
 (name_privtoLocaleString, privtoLocaleString);
 (name_privtoLocaleStringlambda, privtoLocaleStringlambda);
 (name_privtoLowerCase, privtoLowerCase);
 (name_privtoPrecision, privtoPrecision);
 (name_privtoPrecisionLambda, privtoPrecisionLambda);
 (name_privtoUpperCase, privtoUpperCase);
 (name_privtuclambda, privtuclambda);
 (name_privtwoArgObj, privtwoArgObj);
 (name_privunescape, privunescape);
 (name_privunescapeLambda, privunescapeLambda);
 (name_privunshift, privunshift);
 (name_privunshiftlambda, privunshiftlambda);
 (name_privvalueOf, privvalueOf);
 (name_privvalueOfLambda, privvalueOfLambda);
 (name_privvalueOflambda, privvalueOflambda);
 (name_copy_access_desc, copy_access_desc);
 (name_copy_data_desc, copy_data_desc);
 (name_copy_when_defined, copy_when_defined);
 (name_isAccessorDescriptor, isAccessorDescriptor);
 (name_isAccessorField, isAccessorField);
 (name_isDataDescriptor, isDataDescriptor);
 (name_isDataField, isDataField);
 (name_isGenericDescriptor, isGenericDescriptor);
 (name_isGenericField, isGenericField)]
.
Definition store_items := [
(0, {|object_attrs :=
      {|oattrs_proto := value_null;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("make", 
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
                                             ("%LocalTime", privLocalTime);
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
                                             ("%SetterValue", privSetterValue);
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
                                             ("%stringToStringlambda", privstringToStringlambda);
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
                                            None ["%"] ex_getter);
                                           attributes_accessor_set :=
                                           value_undefined;
                                           attributes_accessor_enumerable :=
                                           false;
                                           attributes_accessor_configurable :=
                                           false|})]|});
(1, {|object_attrs :=
      {|oattrs_proto := value_null;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 35;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("hasOwnProperty", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 44;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isPrototypeOf", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 45;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("propertyIsEnumerable", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 41;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("toLocaleString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 42;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 40;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("valueOf", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 43;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})]|});
(2, {|object_attrs :=
      {|oattrs_proto := value_object 1;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("Array", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 107;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Boolean", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 33;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Date", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 177;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Error", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 23;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("EvalError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 49;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Function", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 316;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Infinity", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number (JsNumber.of_int 0);
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("Math", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 261;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("NaN", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number (JsNumber.of_int 0);
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("Number", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 26;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Object", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 35;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("RangeError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 51;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("ReferenceError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 53;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("RegExp", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 254;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("String", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 29;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("SyntaxError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 48;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("TypeError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 55;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("URIError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 57;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("console", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 314;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("decodeURI", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 256;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("decodeURIComponent", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 257;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("encodeURI", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 258;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("encodeURIComponent", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 259;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("escape", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 321;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("eval", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 315;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isFinite", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 317;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isNaN", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 22;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("parseFloat", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 319;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("parseInt", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 255;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("print", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 16;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("undefined", 
                  attributes_data_of {|attributes_data_value :=
                                       value_undefined;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("unescape", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 323;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("window", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 2;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|})]|});
(3, {|object_attrs :=
      {|oattrs_proto := value_object 2;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties := from_list []|});
(4, {|object_attrs :=
      {|oattrs_proto := value_object 1;
        oattrs_class := "Function";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode1|};
      object_properties :=
      from_list [("apply", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 19;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("bind", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 156;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("call", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 18;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 316;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("length", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number (JsNumber.of_int 0);
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 5;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})]|});
(5, {|object_attrs :=
      {|oattrs_proto := value_object 4;
        oattrs_class := "Function";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := privfunctionToStringlambda|};
      object_properties :=
      from_list [("length", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number (JsNumber.of_int 0);
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|})]|});
(6, {|object_attrs :=
      {|oattrs_proto := value_object 1;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 23;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 24;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})]|});
(7, {|object_attrs :=
      {|oattrs_proto := value_object 6;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 55;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "TypeError";
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})]|});
(8, {|object_attrs :=
      {|oattrs_proto := value_object 4;
        oattrs_class := "Function";
        oattrs_extensible := false;
        oattrs_prim_value := value_undefined;
        oattrs_code := privThrowTypeErrorFun|};
      object_properties :=
      from_list [("length", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number (JsNumber.of_int 0);
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|})]|});
(9, {|object_attrs :=
      {|oattrs_proto := value_object 6;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_prim_value := value_undefined;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 53;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "ReferenceError";
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})]|});
(10, {|object_attrs :=
       {|oattrs_proto := value_object 6;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 48;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("name", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "SyntaxError";
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(11, {|object_attrs :=
       {|oattrs_proto := value_object 1;
         oattrs_class := "Boolean";
         oattrs_extensible := true;
         oattrs_prim_value := value_false;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 33;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 30;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("valueOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 302;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(12, {|object_attrs :=
       {|oattrs_proto := value_object 1;
         oattrs_class := "Number";
         oattrs_extensible := true;
         oattrs_prim_value := value_number (JsNumber.of_int 0);
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 26;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toExponential", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 309;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toFixed", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 304;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toLocaleString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 307;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toPrecision", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 311;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 159;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("valueOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 300;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(13, {|object_attrs :=
       {|oattrs_proto := value_object 1;
         oattrs_class := "String";
         oattrs_extensible := true;
         oattrs_prim_value := value_string "";
         oattrs_code := objCode|};
       object_properties :=
       from_list [("charAt", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 109;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("charCodeAt", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 112;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("concat", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 115;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 29;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("indexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 162;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("lastIndexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 164;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("localeCompare", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 165;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("replace", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 163;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("slice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 166;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("split", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 169;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("substring", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 118;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toLocaleLowerCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 167;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLocaleUpperCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 168;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLowerCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 167;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 27;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toUpperCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 168;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("valueOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 298;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(14, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode2|};
       object_properties := from_list []|});
(15, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := false;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode3|};
       object_properties := from_list []|});
(16, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privprintlambda|};
       object_properties := from_list []|});
(17, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privdefinePropertylambda|};
       object_properties := from_list []|});
(18, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privcalllambda|};
       object_properties := from_list []|});
(19, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privapplylambda|};
       object_properties := from_list []|});
(20, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 18;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(21, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 19;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(22, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisNaNlambda|};
       object_properties := from_list []|});
(23, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 6;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(24, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privetslambda|};
       object_properties := from_list []|});
(25, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 24;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(26, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privNumberConstructor|};
       object_properties :=
       from_list [("MAX_VALUE", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("MIN_VALUE", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("NEGATIVE_INFINITY", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("NaN", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("POSITIVE_INFINITY", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 12;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(27, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privstringToStringlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(28, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 27;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(29, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privStringConstructor|};
       object_properties :=
       from_list [("fromCharCode", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 80;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 13;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(30, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privbooleanToStringlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(31, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(32, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 30;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(33, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privBooleanConstructor|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 11;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(34, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 11;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(35, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privObjectConstructor|};
       object_properties :=
       from_list [("create", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 64;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("defineProperties", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 62;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("defineProperty", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 17;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("freeze", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 68;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("getOwnPropertyDescriptor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 38;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("getOwnPropertyNames", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 59;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("getPrototypeOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 36;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("isExtensible", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 76;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("isFrozen", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 72;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("isSealed", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 74;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("keys", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 78;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("preventExtensions", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 70;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 1;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("seal", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 66;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(36, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgpoLambda|};
       object_properties := from_list []|});
(37, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 36;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(38, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgopdLambda|};
       object_properties := from_list []|});
(39, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 38;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(40, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privobjectToStringlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(41, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpropEnumlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(42, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privtoLocaleStringlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(43, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privvalueOflambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(44, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privhasOwnPropertylambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(45, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privIsPrototypeOflambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(46, {|object_attrs :=
       {|oattrs_proto := value_object 6;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 49;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("name", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "EvalError";
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(47, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "SyntaxError";
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(48, {|object_attrs :=
       {|oattrs_proto := value_object 10;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privSyntaxErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 10;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(49, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privEvalErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 46;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(50, {|object_attrs :=
       {|oattrs_proto := value_object 6;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 51;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("name", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "RangeError";
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(51, {|object_attrs :=
       {|oattrs_proto := value_object 50;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privRangeErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 50;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(52, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "ReferenceError";
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(53, {|object_attrs :=
       {|oattrs_proto := value_object 9;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privReferenceErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 9;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(54, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "TypeError";
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(55, {|object_attrs :=
       {|oattrs_proto := value_object 7;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privTypeErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 7;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(56, {|object_attrs :=
       {|oattrs_proto := value_object 6;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 57;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("name", 
                   attributes_data_of {|attributes_data_value :=
                                        value_string "URIError";
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(57, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privURIErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 56;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(58, {|object_attrs :=
       {|oattrs_proto := value_object 1;
         oattrs_class := "Array";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("concat", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 101;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 107;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("every", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 144;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("filter", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 139;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("forEach", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 133;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("indexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 127;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("join", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 82;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("lastIndexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 130;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("map", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 136;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("pop", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 84;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("push", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 87;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("reduce", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 141;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("reduceRight", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 150;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("reverse", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 90;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("shift", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 93;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("slice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 153;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("some", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 147;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("sort", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 104;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("splice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 121;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toLocaleString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 99;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 96;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("unshift", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 124;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})]|});
(59, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privgopnLambda|};
       object_properties := from_list []|});
(60, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 59;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(61, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 17;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(62, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privdefinePropertiesLambda|};
       object_properties := from_list []|});
(63, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 62;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(64, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privcreateLambda|};
       object_properties := from_list []|});
(65, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 64;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(66, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privsealLambda|};
       object_properties := from_list []|});
(67, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 66;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(68, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privfreezelambda|};
       object_properties := from_list []|});
(69, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 68;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(70, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpreventExtensionsLambda|};
       object_properties := from_list []|});
(71, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 70;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(72, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisFrozenLambda|};
       object_properties := from_list []|});
(73, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 72;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(74, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisSealedLambda|};
       object_properties := from_list []|});
(75, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 74;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(76, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privisExtensibleLambda|};
       object_properties := from_list []|});
(77, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 76;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(78, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privkeysLambda|};
       object_properties := from_list []|});
(79, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 78;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(80, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privfromcclambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(81, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 80;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(82, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privjoinlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(83, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(84, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpoplambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(85, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(86, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 84;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(87, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privpushlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(88, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 1);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(89, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 87;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(90, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privreverselambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(91, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(92, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 90;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(93, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privshiftlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(94, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(95, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 93;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(96, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privarrayToStringlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(97, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 96;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(98, {|object_attrs :=
       {|oattrs_proto := value_null;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 82;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(99, {|object_attrs :=
       {|oattrs_proto := value_object 4;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_prim_value := value_undefined;
         oattrs_code := privarrayTLSlambda|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int 0);
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})]|});
(100, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 99;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(101, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privconcatLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(102, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(103, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 101;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(104, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsortlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(105, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(106, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 104;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(107, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privArrayConstructor|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("notinspec", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 68;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 58;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(108, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 107;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(109, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcharatlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(110, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(111, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 109;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(112, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcharcodeatlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(113, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(114, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 112;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(115, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privstrconcatlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(116, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(117, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 115;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(118, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsubstringlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(119, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(120, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 118;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(121, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsplicelambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(122, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(123, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 121;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(124, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privunshiftlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(125, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(126, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 124;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(127, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privaiolambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(128, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(129, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 127;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(130, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privaliolambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(131, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(132, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 130;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(133, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privforeachlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(134, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(135, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 133;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(136, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmaplambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(137, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(138, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 136;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(139, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privfilterlambda|};
        object_properties := from_list []|});
(140, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 139;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(141, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreducelambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(142, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(143, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 141;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(144, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := priveverylambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(145, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(146, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 144;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(147, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsomelambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(148, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(149, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 147;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(150, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreduceRightLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(151, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(152, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 150;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(153, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privslicelambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(154, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(155, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 153;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(156, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privbindLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(157, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(158, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 156;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(159, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privnumberToStringlambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(160, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(161, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 159;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(162, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privStringIndexOflambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(163, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privreplacelambda|};
        object_properties := from_list []|});
(164, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsliolambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(165, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privlocaleCompareLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(166, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privstringSliceLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(167, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtlclambda|};
        object_properties := from_list []|});
(168, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtuclambda|};
        object_properties := from_list []|});
(169, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsplitLambda|};
        object_properties := from_list []|});
(170, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 169;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(171, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privgetYearlambda|};
        object_properties := from_list []|});
(172, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privgetMonthlambda|};
        object_properties := from_list []|});
(173, {|object_attrs :=
        {|oattrs_proto := value_object 1;
          oattrs_class := "Date";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("getDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 182;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getDay", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 180;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 190;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 200;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 212;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 204;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 172;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("getSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 208;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getTime", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 188;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getTimezoneOffset", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 178;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 196;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCDay", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 198;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 192;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 202;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 214;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 206;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 194;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 210;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 171;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("setDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 234;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 242;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 230;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 218;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 226;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 238;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 222;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setTime", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 216;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 236;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 244;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 232;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 220;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 228;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 240;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 224;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 250;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toGMTString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 248;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 174;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toUTCString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 246;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("valueOf", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 176;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|})]|});
(174, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateToStringLambda|};
        object_properties := from_list []|});
(175, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 174;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(176, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateValueOfLambda|};
        object_properties := from_list []|});
(177, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privDateConstructor|};
        object_properties :=
        from_list [("UTC", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 186;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("parse", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 184;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 173;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(178, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdateGetTimezoneOffsetLambda|};
        object_properties := from_list []|});
(179, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 178;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(180, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdategetDayLambda|};
        object_properties := from_list []|});
(181, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 180;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(182, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdategetDateLambda|};
        object_properties := from_list []|});
(183, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 182;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(184, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode4|};
        object_properties := from_list []|});
(185, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 184;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(186, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode5|};
        object_properties := from_list []|});
(187, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 186;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(188, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode6|};
        object_properties := from_list []|});
(189, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 188;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(190, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode7|};
        object_properties := from_list []|});
(191, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 190;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(192, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode8|};
        object_properties := from_list []|});
(193, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 192;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(194, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode9|};
        object_properties := from_list []|});
(195, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 194;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(196, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode10|};
        object_properties := from_list []|});
(197, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 196;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(198, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode11|};
        object_properties := from_list []|});
(199, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 198;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(200, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode12|};
        object_properties := from_list []|});
(201, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 200;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(202, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode13|};
        object_properties := from_list []|});
(203, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 202;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(204, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode14|};
        object_properties := from_list []|});
(205, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 204;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(206, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode15|};
        object_properties := from_list []|});
(207, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 206;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(208, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode16|};
        object_properties := from_list []|});
(209, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 208;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(210, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode17|};
        object_properties := from_list []|});
(211, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 210;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(212, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode18|};
        object_properties := from_list []|});
(213, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 212;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(214, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode19|};
        object_properties := from_list []|});
(215, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 214;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(216, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode20|};
        object_properties := from_list []|});
(217, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 216;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(218, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode21|};
        object_properties := from_list []|});
(219, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 218;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(220, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode22|};
        object_properties := from_list []|});
(221, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 220;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(222, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode23|};
        object_properties := from_list []|});
(223, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 222;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(224, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode24|};
        object_properties := from_list []|});
(225, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 224;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(226, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode25|};
        object_properties := from_list []|});
(227, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 226;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(228, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode26|};
        object_properties := from_list []|});
(229, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 228;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(230, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode27|};
        object_properties := from_list []|});
(231, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 230;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(232, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode28|};
        object_properties := from_list []|});
(233, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 232;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(234, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode29|};
        object_properties := from_list []|});
(235, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 234;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(236, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode30|};
        object_properties := from_list []|});
(237, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 236;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(238, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode31|};
        object_properties := from_list []|});
(239, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 238;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(240, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode32|};
        object_properties := from_list []|});
(241, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 240;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(242, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode33|};
        object_properties := from_list []|});
(243, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 242;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(244, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode34|};
        object_properties := from_list []|});
(245, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 244;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(246, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode35|};
        object_properties := from_list []|});
(247, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 246;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(248, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode36|};
        object_properties := from_list []|});
(249, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 248;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(250, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode37|};
        object_properties := from_list []|});
(251, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 250;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(252, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtestlambda|};
        object_properties := from_list []|});
(253, {|object_attrs :=
        {|oattrs_proto := value_object 1;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("constructor", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 254;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("test", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 252;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(254, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privRegExpConstructor|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 253;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(255, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privparseIntlambda|};
        object_properties := from_list []|});
(256, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdecodeURILambda|};
        object_properties := from_list []|});
(257, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privdecodeURIComponentLambda|};
        object_properties := from_list []|});
(258, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privencodeURILambda|};
        object_properties := from_list []|});
(259, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privencodeURIComponentLambda|};
        object_properties := from_list []|});
(260, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privexplambda|};
        object_properties := from_list []|});
(261, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LN10", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LN2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 0);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LOG10E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 0);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LOG2E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("PI", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 3);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("SQRT1_2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 0);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("SQRT2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("abs", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 268;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("acos", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 270;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("asin", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 272;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("atan", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 274;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("atan2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 276;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("ceil", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 292;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("cos", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 278;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("exp", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 260;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("floor", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 294;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("log", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 290;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("max", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 265;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("min", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 262;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("pow", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 296;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("random", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 280;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("round", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 282;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("sin", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 284;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("sqrt", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 286;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("tan", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 288;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})]|});
(262, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathMinLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(263, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(264, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 262;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(265, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathMaxLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(266, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 2);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(267, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 265;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(268, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathAbsLambda|};
        object_properties := from_list []|});
(269, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 268;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(270, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privacosLambda|};
        object_properties := from_list []|});
(271, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 270;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(272, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privasinLambda|};
        object_properties := from_list []|});
(273, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 272;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(274, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privatanLambda|};
        object_properties := from_list []|});
(275, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 274;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(276, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privatan2Lambda|};
        object_properties := from_list []|});
(277, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 276;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(278, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privcosLambda|};
        object_properties := from_list []|});
(279, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 278;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(280, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privrandomLambda|};
        object_properties := from_list []|});
(281, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 280;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(282, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privroundLambda|};
        object_properties := from_list []|});
(283, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 282;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(284, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsinLambda|};
        object_properties := from_list []|});
(285, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 284;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(286, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privsqrtLambda|};
        object_properties := from_list []|});
(287, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 286;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(288, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtanLambda|};
        object_properties := from_list []|});
(289, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 288;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(290, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathLogLambda|};
        object_properties := from_list []|});
(291, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 290;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(292, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathCeilLambda|};
        object_properties := from_list []|});
(293, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 292;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(294, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathFloorLambda|};
        object_properties := from_list []|});
(295, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 294;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(296, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privmathPowLambda|};
        object_properties := from_list []|});
(297, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 296;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(298, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode38|};
        object_properties := from_list []|});
(299, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 298;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(300, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode39|};
        object_properties := from_list []|});
(301, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 300;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(302, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode40|};
        object_properties := from_list []|});
(303, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 302;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(304, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoFixedLambda|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})]|});
(305, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 1);
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(306, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 304;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(307, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privnumTLSLambda|};
        object_properties := from_list []|});
(308, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 307;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(309, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoExponentialLambda|};
        object_properties := from_list []|});
(310, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 309;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(311, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privtoPrecisionLambda|};
        object_properties := from_list []|});
(312, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 311;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(313, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privlogLambda|};
        object_properties := from_list []|});
(314, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("error", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 313;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("info", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 313;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("log", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 313;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("warn", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 313;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(315, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privevallambda|};
        object_properties := from_list []|});
(316, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privFunctionConstructor|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int 0);
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 4;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(317, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privisFiniteLambda|};
        object_properties := from_list []|});
(318, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 317;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(319, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privparseFloatLambda|};
        object_properties := from_list []|});
(320, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 319;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(321, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privescapeLambda|};
        object_properties := from_list []|});
(322, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 321;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|});
(323, {|object_attrs :=
        {|oattrs_proto := value_object 4;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := privunescapeLambda|};
        object_properties := from_list []|});
(324, {|object_attrs :=
        {|oattrs_proto := value_null;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_prim_value := value_undefined;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("configurable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("enumerable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("value", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 323;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})]|})
].