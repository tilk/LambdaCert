Require Import Utils.
Require Import LjsShared.
Require Import LjsSyntax.
Require Import String.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Definition ptr_privTypeErrorProto : object_ptr :=  4 .
Definition ptr_privBooleanProto : object_ptr :=  9 .
Definition ptr_privNumberProto : object_ptr :=  10 .
Definition ptr_privStringProto : object_ptr :=  11 .
Definition ptr_privArrayProto : object_ptr :=  52 .
Definition ptr_privRangeErrorProto : object_ptr :=  8 .
Definition ptr_privArrayGlobalFuncObj : object_ptr :=  101 .
Definition ptr_privconcat : object_ptr :=  95 .
Definition ptr_privBooleanGlobalFuncObj : object_ptr :=  31 .
Definition ptr_privDateProto : object_ptr :=  167 .
Definition ptr_privdateToString : object_ptr :=  168 .
Definition ptr_privDateGlobalFuncObj : object_ptr :=  171 .
Definition ptr_privglobal : object_ptr :=  2 .
Definition ptr_privObjectProto : object_ptr :=  1 .
Definition ptr_privReferenceErrorProto : object_ptr :=  5 .
Definition ptr_privmakeGlobalEnv : object_ptr :=  0 .
Definition ptr_priveval : object_ptr :=  310 .
Definition ptr_privThrowTypeError : object_ptr :=  14 .
Definition ptr_privglobalContext : object_ptr :=  307 .
Definition ptr_privSyntaxErrorProto : object_ptr :=  6 .
Definition ptr_privErrorProto : object_ptr :=  3 .
Definition ptr_privErrorGlobalFuncObj : object_ptr :=  44 .
Definition ptr_privEvalErrorProto : object_ptr :=  7 .
Definition ptr_privEvalErrorGlobalFuncObj : object_ptr :=  46 .
Definition ptr_privFunctionGlobalFuncObj : object_ptr :=  311 .
Definition ptr_privFunctionProto : object_ptr :=  12 .
Definition ptr_privMath : object_ptr :=  255 .
Definition ptr_privNumberGlobalFuncObj : object_ptr :=  24 .
Definition ptr_privObjectGlobalFuncObj : object_ptr :=  33 .
Definition ptr_privRangeErrorGlobalFuncObj : object_ptr :=  47 .
Definition ptr_privReferenceErrorGlobalFuncObj : object_ptr :=  48 .
Definition ptr_privRegExpProto : object_ptr :=  247 .
Definition ptr_privRegExpGlobalFuncObj : object_ptr :=  248 .
Definition ptr_privStringGlobalFuncObj : object_ptr :=  27 .
Definition ptr_privSyntaxErrorGlobalFuncObj : object_ptr :=  45 .
Definition ptr_privTypeErrorGlobalFuncObj : object_ptr :=  49 .
Definition ptr_privURIErrorProto : object_ptr :=  50 .
Definition ptr_privURIErrorGlobalFuncObj : object_ptr :=  51 .
Definition ptr_privacos : object_ptr :=  264 .
Definition ptr_privapply : object_ptr :=  18 .
Definition ptr_privarrayIndexOf : object_ptr :=  121 .
Definition ptr_privarrayLastIndexOf : object_ptr :=  124 .
Definition ptr_privarrayToLocaleString : object_ptr :=  93 .
Definition ptr_privarrayToString : object_ptr :=  90 .
Definition ptr_privasin : object_ptr :=  266 .
Definition ptr_privatan : object_ptr :=  268 .
Definition ptr_privatan2 : object_ptr :=  270 .
Definition ptr_privbind : object_ptr :=  150 .
Definition ptr_privslice : object_ptr :=  147 .
Definition ptr_privbooleanToString : object_ptr :=  28 .
Definition ptr_privbooleanValueOf : object_ptr :=  296 .
Definition ptr_privcall : object_ptr :=  17 .
Definition ptr_privcharAt : object_ptr :=  103 .
Definition ptr_privcharCodeAt : object_ptr :=  106 .
Definition ptr_privconsole : object_ptr :=  309 .
Definition ptr_privcos : object_ptr :=  272 .
Definition ptr_privcreate : object_ptr :=  58 .
Definition ptr_privdefineProperties : object_ptr :=  56 .
Definition ptr_privdateGetTimezoneOffset : object_ptr :=  172 .
Definition ptr_privdateValueOf : object_ptr :=  170 .
Definition ptr_privdategetDate : object_ptr :=  176 .
Definition ptr_privdategetDay : object_ptr :=  174 .
Definition ptr_privdecodeURI : object_ptr :=  250 .
Definition ptr_privdecodeURIComponent : object_ptr :=  251 .
Definition ptr_privdefineProperty : object_ptr :=  16 .
Definition ptr_privencodeURI : object_ptr :=  252 .
Definition ptr_privencodeURIComponent : object_ptr :=  253 .
Definition ptr_privescape : object_ptr :=  314 .
Definition ptr_privets : object_ptr :=  22 .
Definition ptr_privevery : object_ptr :=  138 .
Definition ptr_privexp : object_ptr :=  254 .
Definition ptr_privfilter : object_ptr :=  133 .
Definition ptr_privforeach : object_ptr :=  127 .
Definition ptr_privfreeze : object_ptr :=  62 .
Definition ptr_privfromCharCode : object_ptr :=  74 .
Definition ptr_privfunctionToString : object_ptr :=  13 .
Definition ptr_privgetMonth : object_ptr :=  166 .
Definition ptr_privgetYear : object_ptr :=  165 .
Definition ptr_privgopd : object_ptr :=  36 .
Definition ptr_privgopn : object_ptr :=  53 .
Definition ptr_privgpo : object_ptr :=  34 .
Definition ptr_privhasOwnProperty : object_ptr :=  42 .
Definition ptr_privisExtensible : object_ptr :=  70 .
Definition ptr_privisFinite : object_ptr :=  312 .
Definition ptr_privisFrozen : object_ptr :=  66 .
Definition ptr_privisNaN : object_ptr :=  21 .
Definition ptr_privisPrototypeOf : object_ptr :=  43 .
Definition ptr_privisSealed : object_ptr :=  68 .
Definition ptr_privjoin : object_ptr :=  76 .
Definition ptr_privkeys : object_ptr :=  72 .
Definition ptr_privlocaleCompare : object_ptr :=  159 .
Definition ptr_privlog : object_ptr :=  308 .
Definition ptr_privmap : object_ptr :=  130 .
Definition ptr_privmathAbs : object_ptr :=  262 .
Definition ptr_privmathCeil : object_ptr :=  286 .
Definition ptr_privmathFloor : object_ptr :=  288 .
Definition ptr_privmathLog : object_ptr :=  284 .
Definition ptr_privmathMax : object_ptr :=  259 .
Definition ptr_privmathMin : object_ptr :=  256 .
Definition ptr_privmathPow : object_ptr :=  290 .
Definition ptr_privnumTLS : object_ptr :=  301 .
Definition ptr_privtoLocaleString : object_ptr :=  40 .
Definition ptr_privnumberToString : object_ptr :=  153 .
Definition ptr_privnumberValueOf : object_ptr :=  294 .
Definition ptr_privobjectToString : object_ptr :=  38 .
Definition ptr_privobjectValueOf : object_ptr :=  41 .
Definition ptr_privparseFloat : object_ptr :=  313 .
Definition ptr_privparseInt : object_ptr :=  249 .
Definition ptr_privpop : object_ptr :=  78 .
Definition ptr_privpreventExtensions : object_ptr :=  64 .
Definition ptr_privprint : object_ptr :=  15 .
Definition ptr_privpropEnum : object_ptr :=  39 .
Definition ptr_privpush : object_ptr :=  81 .
Definition ptr_privrandom : object_ptr :=  274 .
Definition ptr_privreduce : object_ptr :=  135 .
Definition ptr_privreduceRight : object_ptr :=  144 .
Definition ptr_privreplace : object_ptr :=  157 .
Definition ptr_privstringIndexOf : object_ptr :=  156 .
Definition ptr_privsubstring : object_ptr :=  112 .
Definition ptr_privreverse : object_ptr :=  84 .
Definition ptr_privround : object_ptr :=  276 .
Definition ptr_privseal : object_ptr :=  60 .
Definition ptr_privshift : object_ptr :=  87 .
Definition ptr_privsin : object_ptr :=  278 .
Definition ptr_privsome : object_ptr :=  141 .
Definition ptr_privsort : object_ptr :=  98 .
Definition ptr_privsplice : object_ptr :=  115 .
Definition ptr_privsplit : object_ptr :=  163 .
Definition ptr_privsqrt : object_ptr :=  280 .
Definition ptr_privstringConcat : object_ptr :=  109 .
Definition ptr_privstringLastIndexOf : object_ptr :=  158 .
Definition ptr_privstringSlice : object_ptr :=  160 .
Definition ptr_privstringToString : object_ptr :=  25 .
Definition ptr_privstringValueOf : object_ptr :=  292 .
Definition ptr_privtan : object_ptr :=  282 .
Definition ptr_privtest : object_ptr :=  246 .
Definition ptr_privtoExponential : object_ptr :=  303 .
Definition ptr_privtoFixed : object_ptr :=  298 .
Definition ptr_privtoLowerCase : object_ptr :=  161 .
Definition ptr_privtoPrecision : object_ptr :=  305 .
Definition ptr_privtoUpperCase : object_ptr :=  162 .
Definition ptr_privunescape : object_ptr :=  316 .
Definition ptr_privunshift : object_ptr :=  118 .
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
   (expr_seq
    (expr_app (expr_id "%Delete")
     [expr_id "obj1"; expr_string "value"; expr_false])
    (expr_app (expr_id "%Delete")
     [expr_id "obj1"; expr_string "writable"; expr_false])))))
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
   (expr_seq
    (expr_app (expr_id "%Delete")
     [expr_id "obj1"; expr_string "get"; expr_false])
    (expr_app (expr_id "%Delete")
     [expr_id "obj1"; expr_string "set"; expr_false])))))
.
Definition ex_copy_when_defined := 
expr_if (expr_op2 binary_op_has_own_property (expr_id "obj2") (expr_id "s"))
(expr_set_attr pattr_value (expr_id "obj1") (expr_id "s")
 (expr_get_attr pattr_value (expr_id "obj2") (expr_id "s"))) expr_undefined
.
Definition ex_dataval := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined) 
[]
[("%AddAccessorField", property_data
                       (data_intro (expr_id "%AddAccessorField") expr_true
                        expr_false expr_false));
 ("%AddDataField", property_data
                   (data_intro (expr_id "%AddDataField") expr_true expr_false
                    expr_false));
 ("%AppExpr", property_data
              (data_intro (expr_id "%AppExpr") expr_true expr_false
               expr_false));
 ("%AppExprCheck", property_data
                   (data_intro (expr_id "%AppExprCheck") expr_true expr_false
                    expr_false));
 ("%AppMethodOp", property_data
                  (data_intro (expr_id "%AppMethodOp") expr_true expr_false
                   expr_false));
 ("%ArrayCall", property_data
                (data_intro (expr_id "%ArrayCall") expr_true expr_false
                 expr_false));
 ("%ArrayConstructor", property_data
                       (data_intro (expr_id "%ArrayConstructor") expr_true
                        expr_false expr_false));
 ("%ArrayGlobalFuncObj", property_data
                         (data_intro (expr_id "%ArrayGlobalFuncObj")
                          expr_true expr_false expr_false));
 ("%ArrayIdx", property_data
               (data_intro (expr_id "%ArrayIdx") expr_true expr_false
                expr_false));
 ("%ArrayLengthChange", property_data
                        (data_intro (expr_id "%ArrayLengthChange") expr_true
                         expr_false expr_false));
 ("%ArrayProto", property_data
                 (data_intro (expr_id "%ArrayProto") expr_true expr_false
                  expr_false));
 ("%BindConstructor", property_data
                      (data_intro (expr_id "%BindConstructor") expr_true
                       expr_false expr_false));
 ("%BindObjCall", property_data
                  (data_intro (expr_id "%BindObjCall") expr_true expr_false
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
 ("%BitwiseOr", property_data
                (data_intro (expr_id "%BitwiseOr") expr_true expr_false
                 expr_false));
 ("%BitwiseXor", property_data
                 (data_intro (expr_id "%BitwiseXor") expr_true expr_false
                  expr_false));
 ("%BooleanCall", property_data
                  (data_intro (expr_id "%BooleanCall") expr_true expr_false
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
 ("%ComputeLength", property_data
                    (data_intro (expr_id "%ComputeLength") expr_true
                     expr_false expr_false));
 ("%DateCall", property_data
               (data_intro (expr_id "%DateCall") expr_true expr_false
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
 ("%DeclEnvAddBinding", property_data
                        (data_intro (expr_id "%DeclEnvAddBinding") expr_true
                         expr_false expr_false));
 ("%DefaultCall", property_data
                  (data_intro (expr_id "%DefaultCall") expr_true expr_false
                   expr_false));
 ("%DefaultConstruct", property_data
                       (data_intro (expr_id "%DefaultConstruct") expr_true
                        expr_false expr_false));
 ("%Delete", property_data
             (data_intro (expr_id "%Delete") expr_true expr_false expr_false));
 ("%DeleteOp", property_data
               (data_intro (expr_id "%DeleteOp") expr_true expr_false
                expr_false));
 ("%EnvAppExpr", property_data
                 (data_intro (expr_id "%EnvAppExpr") expr_true expr_false
                  expr_false));
 ("%EnvAssign", property_data
                (data_intro (expr_id "%EnvAssign") expr_true expr_false
                 expr_false));
 ("%EnvCreateImmutableBinding", property_data
                                (data_intro
                                 (expr_id "%EnvCreateImmutableBinding")
                                 expr_true expr_false expr_false));
 ("%EnvCreateMutableBinding", property_data
                              (data_intro
                               (expr_id "%EnvCreateMutableBinding") expr_true
                               expr_false expr_false));
 ("%EnvCreateSetMutableBinding", property_data
                                 (data_intro
                                  (expr_id "%EnvCreateSetMutableBinding")
                                  expr_true expr_false expr_false));
 ("%EnvDefineArg", property_data
                   (data_intro (expr_id "%EnvDefineArg") expr_true expr_false
                    expr_false));
 ("%EnvDefineArgsObj", property_data
                       (data_intro (expr_id "%EnvDefineArgsObj") expr_true
                        expr_false expr_false));
 ("%EnvDefineArgsObjOk", property_data
                         (data_intro (expr_id "%EnvDefineArgsObjOk")
                          expr_true expr_false expr_false));
 ("%EnvDefineFunc", property_data
                    (data_intro (expr_id "%EnvDefineFunc") expr_true
                     expr_false expr_false));
 ("%EnvDefineVar", property_data
                   (data_intro (expr_id "%EnvDefineVar") expr_true expr_false
                    expr_false));
 ("%EnvDelete", property_data
                (data_intro (expr_id "%EnvDelete") expr_true expr_false
                 expr_false));
 ("%EnvGet", property_data
             (data_intro (expr_id "%EnvGet") expr_true expr_false expr_false));
 ("%EnvGetBindingValue", property_data
                         (data_intro (expr_id "%EnvGetBindingValue")
                          expr_true expr_false expr_false));
 ("%EnvGetId", property_data
               (data_intro (expr_id "%EnvGetId") expr_true expr_false
                expr_false));
 ("%EnvGetValue", property_data
                  (data_intro (expr_id "%EnvGetValue") expr_true expr_false
                   expr_false));
 ("%EnvHasBinding", property_data
                    (data_intro (expr_id "%EnvHasBinding") expr_true
                     expr_false expr_false));
 ("%EnvImplicitThis", property_data
                      (data_intro (expr_id "%EnvImplicitThis") expr_true
                       expr_false expr_false));
 ("%EnvInitializeImmutableBinding", property_data
                                    (data_intro
                                     (expr_id
                                      "%EnvInitializeImmutableBinding")
                                     expr_true expr_false expr_false));
 ("%EnvModify", property_data
                (data_intro (expr_id "%EnvModify") expr_true expr_false
                 expr_false));
 ("%EnvPrepostOp", property_data
                   (data_intro (expr_id "%EnvPrepostOp") expr_true expr_false
                    expr_false));
 ("%EnvPutValue", property_data
                  (data_intro (expr_id "%EnvPutValue") expr_true expr_false
                   expr_false));
 ("%EnvSetMutableBinding", property_data
                           (data_intro (expr_id "%EnvSetMutableBinding")
                            expr_true expr_false expr_false));
 ("%EnvTypeof", property_data
                (data_intro (expr_id "%EnvTypeof") expr_true expr_false
                 expr_false));
 ("%EqEq", property_data
           (data_intro (expr_id "%EqEq") expr_true expr_false expr_false));
 ("%ErrorConstructor", property_data
                       (data_intro (expr_id "%ErrorConstructor") expr_true
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
 ("%FunctionProtoCall", property_data
                        (data_intro (expr_id "%FunctionProtoCall") expr_true
                         expr_false expr_false));
 ("%GeOp", property_data
           (data_intro (expr_id "%GeOp") expr_true expr_false expr_false));
 ("%Get", property_data
          (data_intro (expr_id "%Get") expr_true expr_false expr_false));
 ("%Get1", property_data
           (data_intro (expr_id "%Get1") expr_true expr_false expr_false));
 ("%GetField", property_data
               (data_intro (expr_id "%GetField") expr_true expr_false
                expr_false));
 ("%GetOp", property_data
            (data_intro (expr_id "%GetOp") expr_true expr_false expr_false));
 ("%GetOwnProperty", property_data
                     (data_intro (expr_id "%GetOwnProperty") expr_true
                      expr_false expr_false));
 ("%GetPrim", property_data
              (data_intro (expr_id "%GetPrim") expr_true expr_false
               expr_false));
 ("%GetProperty", property_data
                  (data_intro (expr_id "%GetProperty") expr_true expr_false
                   expr_false));
 ("%GtOp", property_data
           (data_intro (expr_id "%GtOp") expr_true expr_false expr_false));
 ("%HasProperty", property_data
                  (data_intro (expr_id "%HasProperty") expr_true expr_false
                   expr_false));
 ("%InLeapYear", property_data
                 (data_intro (expr_id "%InLeapYear") expr_true expr_false
                  expr_false));
 ("%IsCallable", property_data
                 (data_intro (expr_id "%IsCallable") expr_true expr_false
                  expr_false));
 ("%IsFinite", property_data
               (data_intro (expr_id "%IsFinite") expr_true expr_false
                expr_false));
 ("%IsJSError", property_data
                (data_intro (expr_id "%IsJSError") expr_true expr_false
                 expr_false));
 ("%JSError", property_data
              (data_intro (expr_id "%JSError") expr_true expr_false
               expr_false));
 ("%LeOp", property_data
           (data_intro (expr_id "%LeOp") expr_true expr_false expr_false));
 ("%LeftShift", property_data
                (data_intro (expr_id "%LeftShift") expr_true expr_false
                 expr_false));
 ("%LocalTime", property_data
                (data_intro (expr_id "%LocalTime") expr_true expr_false
                 expr_false));
 ("%LtOp", property_data
           (data_intro (expr_id "%LtOp") expr_true expr_false expr_false));
 ("%MakeArray", property_data
                (data_intro (expr_id "%MakeArray") expr_true expr_false
                 expr_false));
 ("%MakeBind", property_data
               (data_intro (expr_id "%MakeBind") expr_true expr_false
                expr_false));
 ("%MakeBoolean", property_data
                  (data_intro (expr_id "%MakeBoolean") expr_true expr_false
                   expr_false));
 ("%MakeDate", property_data
               (data_intro (expr_id "%MakeDate") expr_true expr_false
                expr_false));
 ("%MakeDateDayTime", property_data
                      (data_intro (expr_id "%MakeDateDayTime") expr_true
                       expr_false expr_false));
 ("%MakeDay", property_data
              (data_intro (expr_id "%MakeDay") expr_true expr_false
               expr_false));
 ("%MakeFunctionObject", property_data
                         (data_intro (expr_id "%MakeFunctionObject")
                          expr_true expr_false expr_false));
 ("%MakeNativeError", property_data
                      (data_intro (expr_id "%MakeNativeError") expr_true
                       expr_false expr_false));
 ("%MakeNativeErrorProto", property_data
                           (data_intro (expr_id "%MakeNativeErrorProto")
                            expr_true expr_false expr_false));
 ("%MakeNumber", property_data
                 (data_intro (expr_id "%MakeNumber") expr_true expr_false
                  expr_false));
 ("%MakeObject", property_data
                 (data_intro (expr_id "%MakeObject") expr_true expr_false
                  expr_false));
 ("%MakeString", property_data
                 (data_intro (expr_id "%MakeString") expr_true expr_false
                  expr_false));
 ("%MakeTime", property_data
               (data_intro (expr_id "%MakeTime") expr_true expr_false
                expr_false));
 ("%Math", property_data
           (data_intro (expr_id "%Math") expr_true expr_false expr_false));
 ("%MonthFromTime", property_data
                    (data_intro (expr_id "%MonthFromTime") expr_true
                     expr_false expr_false));
 ("%NativeError", property_data
                  (data_intro (expr_id "%NativeError") expr_true expr_false
                   expr_false));
 ("%NativeErrorConstructor", property_data
                             (data_intro (expr_id "%NativeErrorConstructor")
                              expr_true expr_false expr_false));
 ("%NumberCall", property_data
                 (data_intro (expr_id "%NumberCall") expr_true expr_false
                  expr_false));
 ("%NumberCompareOp", property_data
                      (data_intro (expr_id "%NumberCompareOp") expr_true
                       expr_false expr_false));
 ("%NumberConstructor", property_data
                        (data_intro (expr_id "%NumberConstructor") expr_true
                         expr_false expr_false));
 ("%NumberGlobalFuncObj", property_data
                          (data_intro (expr_id "%NumberGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%NumberProto", property_data
                  (data_intro (expr_id "%NumberProto") expr_true expr_false
                   expr_false));
 ("%ObjectCall", property_data
                 (data_intro (expr_id "%ObjectCall") expr_true expr_false
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
 ("%PrepostOp", property_data
                (data_intro (expr_id "%PrepostOp") expr_true expr_false
                 expr_false));
 ("%PrimAdd", property_data
              (data_intro (expr_id "%PrimAdd") expr_true expr_false
               expr_false));
 ("%PrimComma", property_data
                (data_intro (expr_id "%PrimComma") expr_true expr_false
                 expr_false));
 ("%PrimDiv", property_data
              (data_intro (expr_id "%PrimDiv") expr_true expr_false
               expr_false));
 ("%PrimMod", property_data
              (data_intro (expr_id "%PrimMod") expr_true expr_false
               expr_false));
 ("%PrimMult", property_data
               (data_intro (expr_id "%PrimMult") expr_true expr_false
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
 ("%PrimitiveCompareOp", property_data
                         (data_intro (expr_id "%PrimitiveCompareOp")
                          expr_true expr_false expr_false));
 ("%PropertyAccess", property_data
                     (data_intro (expr_id "%PropertyAccess") expr_true
                      expr_false expr_false));
 ("%Put", property_data
          (data_intro (expr_id "%Put") expr_true expr_false expr_false));
 ("%Put1", property_data
           (data_intro (expr_id "%Put1") expr_true expr_false expr_false));
 ("%PutPrim", property_data
              (data_intro (expr_id "%PutPrim") expr_true expr_false
               expr_false));
 ("%RangeError", property_data
                 (data_intro (expr_id "%RangeError") expr_true expr_false
                  expr_false));
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
 ("%ReferenceError", property_data
                     (data_intro (expr_id "%ReferenceError") expr_true
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
 ("%RegExpCode", property_data
                 (data_intro (expr_id "%RegExpCode") expr_true expr_false
                  expr_false));
 ("%RegExpConstructor", property_data
                        (data_intro (expr_id "%RegExpConstructor") expr_true
                         expr_false expr_false));
 ("%RegExpGlobalFuncObj", property_data
                          (data_intro (expr_id "%RegExpGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%RegExpProto", property_data
                  (data_intro (expr_id "%RegExpProto") expr_true expr_false
                   expr_false));
 ("%RunSelfConstructorCall", property_data
                             (data_intro (expr_id "%RunSelfConstructorCall")
                              expr_true expr_false expr_false));
 ("%SetField", property_data
               (data_intro (expr_id "%SetField") expr_true expr_false
                expr_false));
 ("%SetOp", property_data
            (data_intro (expr_id "%SetOp") expr_true expr_false expr_false));
 ("%SignedRightShift", property_data
                       (data_intro (expr_id "%SignedRightShift") expr_true
                        expr_false expr_false));
 ("%StringCall", property_data
                 (data_intro (expr_id "%StringCall") expr_true expr_false
                  expr_false));
 ("%StringConstructor", property_data
                        (data_intro (expr_id "%StringConstructor") expr_true
                         expr_false expr_false));
 ("%StringGlobalFuncObj", property_data
                          (data_intro (expr_id "%StringGlobalFuncObj")
                           expr_true expr_false expr_false));
 ("%StringIndices", property_data
                    (data_intro (expr_id "%StringIndices") expr_true
                     expr_false expr_false));
 ("%StringProto", property_data
                  (data_intro (expr_id "%StringProto") expr_true expr_false
                   expr_false));
 ("%StxEq", property_data
            (data_intro (expr_id "%StxEq") expr_true expr_false expr_false));
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
 ("%ToPropertyDescriptor", property_data
                           (data_intro (expr_id "%ToPropertyDescriptor")
                            expr_true expr_false expr_false));
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
 ("%UnaryNot", property_data
               (data_intro (expr_id "%UnaryNot") expr_true expr_false
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
 ("%Void", property_data
           (data_intro (expr_id "%Void") expr_true expr_false expr_false));
 ("%YearFromTime", property_data
                   (data_intro (expr_id "%YearFromTime") expr_true expr_false
                    expr_false));
 ("%acos", property_data
           (data_intro (expr_id "%acos") expr_true expr_false expr_false));
 ("%acosCall", property_data
               (data_intro (expr_id "%acosCall") expr_true expr_false
                expr_false));
 ("%apply", property_data
            (data_intro (expr_id "%apply") expr_true expr_false expr_false));
 ("%applyCall", property_data
                (data_intro (expr_id "%applyCall") expr_true expr_false
                 expr_false));
 ("%arrayIndexOf", property_data
                   (data_intro (expr_id "%arrayIndexOf") expr_true expr_false
                    expr_false));
 ("%arrayIndexOfCall", property_data
                       (data_intro (expr_id "%arrayIndexOfCall") expr_true
                        expr_false expr_false));
 ("%arrayLastIndexOf", property_data
                       (data_intro (expr_id "%arrayLastIndexOf") expr_true
                        expr_false expr_false));
 ("%arrayLastIndexOfCall", property_data
                           (data_intro (expr_id "%arrayLastIndexOfCall")
                            expr_true expr_false expr_false));
 ("%arrayTLSCall", property_data
                   (data_intro (expr_id "%arrayTLSCall") expr_true expr_false
                    expr_false));
 ("%arrayToLocaleString", property_data
                          (data_intro (expr_id "%arrayToLocaleString")
                           expr_true expr_false expr_false));
 ("%arrayToString", property_data
                    (data_intro (expr_id "%arrayToString") expr_true
                     expr_false expr_false));
 ("%arrayToStringCall", property_data
                        (data_intro (expr_id "%arrayToStringCall") expr_true
                         expr_false expr_false));
 ("%asin", property_data
           (data_intro (expr_id "%asin") expr_true expr_false expr_false));
 ("%asinCall", property_data
               (data_intro (expr_id "%asinCall") expr_true expr_false
                expr_false));
 ("%assert", property_data
             (data_intro (expr_id "%assert") expr_true expr_false expr_false));
 ("%atan", property_data
           (data_intro (expr_id "%atan") expr_true expr_false expr_false));
 ("%atan2", property_data
            (data_intro (expr_id "%atan2") expr_true expr_false expr_false));
 ("%atan2Call", property_data
                (data_intro (expr_id "%atan2Call") expr_true expr_false
                 expr_false));
 ("%atanCall", property_data
               (data_intro (expr_id "%atanCall") expr_true expr_false
                expr_false));
 ("%bind", property_data
           (data_intro (expr_id "%bind") expr_true expr_false expr_false));
 ("%bindCall", property_data
               (data_intro (expr_id "%bindCall") expr_true expr_false
                expr_false));
 ("%booleanToString", property_data
                      (data_intro (expr_id "%booleanToString") expr_true
                       expr_false expr_false));
 ("%booleanToStringCall", property_data
                          (data_intro (expr_id "%booleanToStringCall")
                           expr_true expr_false expr_false));
 ("%booleanValueOf", property_data
                     (data_intro (expr_id "%booleanValueOf") expr_true
                      expr_false expr_false));
 ("%call", property_data
           (data_intro (expr_id "%call") expr_true expr_false expr_false));
 ("%callCall", property_data
               (data_intro (expr_id "%callCall") expr_true expr_false
                expr_false));
 ("%charAt", property_data
             (data_intro (expr_id "%charAt") expr_true expr_false expr_false));
 ("%charAtCall", property_data
                 (data_intro (expr_id "%charAtCall") expr_true expr_false
                  expr_false));
 ("%charCodeAt", property_data
                 (data_intro (expr_id "%charCodeAt") expr_true expr_false
                  expr_false));
 ("%charCodeAtCall", property_data
                     (data_intro (expr_id "%charCodeAtCall") expr_true
                      expr_false expr_false));
 ("%concat", property_data
             (data_intro (expr_id "%concat") expr_true expr_false expr_false));
 ("%concatCall", property_data
                 (data_intro (expr_id "%concatCall") expr_true expr_false
                  expr_false));
 ("%configurableEval", property_data
                       (data_intro (expr_id "%configurableEval") expr_true
                        expr_false expr_false));
 ("%console", property_data
              (data_intro (expr_id "%console") expr_true expr_false
               expr_false));
 ("%cos", property_data
          (data_intro (expr_id "%cos") expr_true expr_false expr_false));
 ("%cosCall", property_data
              (data_intro (expr_id "%cosCall") expr_true expr_false
               expr_false));
 ("%create", property_data
             (data_intro (expr_id "%create") expr_true expr_false expr_false));
 ("%createCall", property_data
                 (data_intro (expr_id "%createCall") expr_true expr_false
                  expr_false));
 ("%dateGetTimezoneOffset", property_data
                            (data_intro (expr_id "%dateGetTimezoneOffset")
                             expr_true expr_false expr_false));
 ("%dateGetTimezoneOffsetCall", property_data
                                (data_intro
                                 (expr_id "%dateGetTimezoneOffsetCall")
                                 expr_true expr_false expr_false));
 ("%dateToString", property_data
                   (data_intro (expr_id "%dateToString") expr_true expr_false
                    expr_false));
 ("%dateToStringCall", property_data
                       (data_intro (expr_id "%dateToStringCall") expr_true
                        expr_false expr_false));
 ("%dateValueOf", property_data
                  (data_intro (expr_id "%dateValueOf") expr_true expr_false
                   expr_false));
 ("%dateValueOfCall", property_data
                      (data_intro (expr_id "%dateValueOfCall") expr_true
                       expr_false expr_false));
 ("%dategetDate", property_data
                  (data_intro (expr_id "%dategetDate") expr_true expr_false
                   expr_false));
 ("%dategetDateCall", property_data
                      (data_intro (expr_id "%dategetDateCall") expr_true
                       expr_false expr_false));
 ("%dategetDay", property_data
                 (data_intro (expr_id "%dategetDay") expr_true expr_false
                  expr_false));
 ("%dategetDayCall", property_data
                     (data_intro (expr_id "%dategetDayCall") expr_true
                      expr_false expr_false));
 ("%decodeURI", property_data
                (data_intro (expr_id "%decodeURI") expr_true expr_false
                 expr_false));
 ("%decodeURICall", property_data
                    (data_intro (expr_id "%decodeURICall") expr_true
                     expr_false expr_false));
 ("%decodeURIComponent", property_data
                         (data_intro (expr_id "%decodeURIComponent")
                          expr_true expr_false expr_false));
 ("%decodeURIComponentCall", property_data
                             (data_intro (expr_id "%decodeURIComponentCall")
                              expr_true expr_false expr_false));
 ("%define15Property", property_data
                       (data_intro (expr_id "%define15Property") expr_true
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
 ("%definePropertiesCall", property_data
                           (data_intro (expr_id "%definePropertiesCall")
                            expr_true expr_false expr_false));
 ("%defineProperty", property_data
                     (data_intro (expr_id "%defineProperty") expr_true
                      expr_false expr_false));
 ("%definePropertyCall", property_data
                         (data_intro (expr_id "%definePropertyCall")
                          expr_true expr_false expr_false));
 ("%encodeURI", property_data
                (data_intro (expr_id "%encodeURI") expr_true expr_false
                 expr_false));
 ("%encodeURICall", property_data
                    (data_intro (expr_id "%encodeURICall") expr_true
                     expr_false expr_false));
 ("%encodeURIComponent", property_data
                         (data_intro (expr_id "%encodeURIComponent")
                          expr_true expr_false expr_false));
 ("%encodeURIComponentCall", property_data
                             (data_intro (expr_id "%encodeURIComponentCall")
                              expr_true expr_false expr_false));
 ("%escape", property_data
             (data_intro (expr_id "%escape") expr_true expr_false expr_false));
 ("%escapeCall", property_data
                 (data_intro (expr_id "%escapeCall") expr_true expr_false
                  expr_false));
 ("%ets", property_data
          (data_intro (expr_id "%ets") expr_true expr_false expr_false));
 ("%etsCall", property_data
              (data_intro (expr_id "%etsCall") expr_true expr_false
               expr_false));
 ("%eval", property_data
           (data_intro (expr_id "%eval") expr_true expr_false expr_false));
 ("%evalCall", property_data
               (data_intro (expr_id "%evalCall") expr_true expr_false
                expr_false));
 ("%every", property_data
            (data_intro (expr_id "%every") expr_true expr_false expr_false));
 ("%everyCall", property_data
                (data_intro (expr_id "%everyCall") expr_true expr_false
                 expr_false));
 ("%exp", property_data
          (data_intro (expr_id "%exp") expr_true expr_false expr_false));
 ("%expCall", property_data
              (data_intro (expr_id "%expCall") expr_true expr_false
               expr_false));
 ("%filter", property_data
             (data_intro (expr_id "%filter") expr_true expr_false expr_false));
 ("%filterCall", property_data
                 (data_intro (expr_id "%filterCall") expr_true expr_false
                  expr_false));
 ("%foreach", property_data
              (data_intro (expr_id "%foreach") expr_true expr_false
               expr_false));
 ("%foreachCall", property_data
                  (data_intro (expr_id "%foreachCall") expr_true expr_false
                   expr_false));
 ("%freeze", property_data
             (data_intro (expr_id "%freeze") expr_true expr_false expr_false));
 ("%freezeCall", property_data
                 (data_intro (expr_id "%freezeCall") expr_true expr_false
                  expr_false));
 ("%fromCharCode", property_data
                   (data_intro (expr_id "%fromCharCode") expr_true expr_false
                    expr_false));
 ("%fromccCall", property_data
                 (data_intro (expr_id "%fromccCall") expr_true expr_false
                  expr_false));
 ("%functionToString", property_data
                       (data_intro (expr_id "%functionToString") expr_true
                        expr_false expr_false));
 ("%functionToStringCall", property_data
                           (data_intro (expr_id "%functionToStringCall")
                            expr_true expr_false expr_false));
 ("%getCurrentUTC", property_data
                    (data_intro (expr_id "%getCurrentUTC") expr_true
                     expr_false expr_false));
 ("%getMonth", property_data
               (data_intro (expr_id "%getMonth") expr_true expr_false
                expr_false));
 ("%getMonthCall", property_data
                   (data_intro (expr_id "%getMonthCall") expr_true expr_false
                    expr_false));
 ("%getYear", property_data
              (data_intro (expr_id "%getYear") expr_true expr_false
               expr_false));
 ("%getYearCall", property_data
                  (data_intro (expr_id "%getYearCall") expr_true expr_false
                   expr_false));
 ("%global", property_data
             (data_intro (expr_id "%global") expr_true expr_false expr_false));
 ("%globalContext", property_data
                    (data_intro (expr_id "%globalContext") expr_true
                     expr_false expr_false));
 ("%gopd", property_data
           (data_intro (expr_id "%gopd") expr_true expr_false expr_false));
 ("%gopdCall", property_data
               (data_intro (expr_id "%gopdCall") expr_true expr_false
                expr_false));
 ("%gopn", property_data
           (data_intro (expr_id "%gopn") expr_true expr_false expr_false));
 ("%gopnCall", property_data
               (data_intro (expr_id "%gopnCall") expr_true expr_false
                expr_false));
 ("%gpo", property_data
          (data_intro (expr_id "%gpo") expr_true expr_false expr_false));
 ("%gpoCall", property_data
              (data_intro (expr_id "%gpoCall") expr_true expr_false
               expr_false));
 ("%hasOwnProperty", property_data
                     (data_intro (expr_id "%hasOwnProperty") expr_true
                      expr_false expr_false));
 ("%hasOwnPropertyCall", property_data
                         (data_intro (expr_id "%hasOwnPropertyCall")
                          expr_true expr_false expr_false));
 ("%in", property_data
         (data_intro (expr_id "%in") expr_true expr_false expr_false));
 ("%instanceof", property_data
                 (data_intro (expr_id "%instanceof") expr_true expr_false
                  expr_false));
 ("%isExtensible", property_data
                   (data_intro (expr_id "%isExtensible") expr_true expr_false
                    expr_false));
 ("%isExtensibleCall", property_data
                       (data_intro (expr_id "%isExtensibleCall") expr_true
                        expr_false expr_false));
 ("%isFinite", property_data
               (data_intro (expr_id "%isFinite") expr_true expr_false
                expr_false));
 ("%isFiniteCall", property_data
                   (data_intro (expr_id "%isFiniteCall") expr_true expr_false
                    expr_false));
 ("%isFrozen", property_data
               (data_intro (expr_id "%isFrozen") expr_true expr_false
                expr_false));
 ("%isFrozenCall", property_data
                   (data_intro (expr_id "%isFrozenCall") expr_true expr_false
                    expr_false));
 ("%isNaN", property_data
            (data_intro (expr_id "%isNaN") expr_true expr_false expr_false));
 ("%isNaNCall", property_data
                (data_intro (expr_id "%isNaNCall") expr_true expr_false
                 expr_false));
 ("%isPrototypeOf", property_data
                    (data_intro (expr_id "%isPrototypeOf") expr_true
                     expr_false expr_false));
 ("%isPrototypeOfCall", property_data
                        (data_intro (expr_id "%isPrototypeOfCall") expr_true
                         expr_false expr_false));
 ("%isSealed", property_data
               (data_intro (expr_id "%isSealed") expr_true expr_false
                expr_false));
 ("%isSealedCall", property_data
                   (data_intro (expr_id "%isSealedCall") expr_true expr_false
                    expr_false));
 ("%join", property_data
           (data_intro (expr_id "%join") expr_true expr_false expr_false));
 ("%joinCall", property_data
               (data_intro (expr_id "%joinCall") expr_true expr_false
                expr_false));
 ("%keys", property_data
           (data_intro (expr_id "%keys") expr_true expr_false expr_false));
 ("%keysCall", property_data
               (data_intro (expr_id "%keysCall") expr_true expr_false
                expr_false));
 ("%len", property_data
          (data_intro (expr_id "%len") expr_true expr_false expr_false));
 ("%localeCompare", property_data
                    (data_intro (expr_id "%localeCompare") expr_true
                     expr_false expr_false));
 ("%localeCompareCall", property_data
                        (data_intro (expr_id "%localeCompareCall") expr_true
                         expr_false expr_false));
 ("%log", property_data
          (data_intro (expr_id "%log") expr_true expr_false expr_false));
 ("%logCall", property_data
              (data_intro (expr_id "%logCall") expr_true expr_false
               expr_false));
 ("%makeGlobalEnv", property_data
                    (data_intro (expr_id "%makeGlobalEnv") expr_true
                     expr_false expr_false));
 ("%map", property_data
          (data_intro (expr_id "%map") expr_true expr_false expr_false));
 ("%mapCall", property_data
              (data_intro (expr_id "%mapCall") expr_true expr_false
               expr_false));
 ("%mathAbs", property_data
              (data_intro (expr_id "%mathAbs") expr_true expr_false
               expr_false));
 ("%mathAbsCall", property_data
                  (data_intro (expr_id "%mathAbsCall") expr_true expr_false
                   expr_false));
 ("%mathCeil", property_data
               (data_intro (expr_id "%mathCeil") expr_true expr_false
                expr_false));
 ("%mathCeilCall", property_data
                   (data_intro (expr_id "%mathCeilCall") expr_true expr_false
                    expr_false));
 ("%mathFloor", property_data
                (data_intro (expr_id "%mathFloor") expr_true expr_false
                 expr_false));
 ("%mathFloorCall", property_data
                    (data_intro (expr_id "%mathFloorCall") expr_true
                     expr_false expr_false));
 ("%mathLog", property_data
              (data_intro (expr_id "%mathLog") expr_true expr_false
               expr_false));
 ("%mathLogCall", property_data
                  (data_intro (expr_id "%mathLogCall") expr_true expr_false
                   expr_false));
 ("%mathMax", property_data
              (data_intro (expr_id "%mathMax") expr_true expr_false
               expr_false));
 ("%mathMaxCall", property_data
                  (data_intro (expr_id "%mathMaxCall") expr_true expr_false
                   expr_false));
 ("%mathMin", property_data
              (data_intro (expr_id "%mathMin") expr_true expr_false
               expr_false));
 ("%mathMinCall", property_data
                  (data_intro (expr_id "%mathMinCall") expr_true expr_false
                   expr_false));
 ("%mathPow", property_data
              (data_intro (expr_id "%mathPow") expr_true expr_false
               expr_false));
 ("%mathPowCall", property_data
                  (data_intro (expr_id "%mathPowCall") expr_true expr_false
                   expr_false));
 ("%max", property_data
          (data_intro (expr_id "%max") expr_true expr_false expr_false));
 ("%min", property_data
          (data_intro (expr_id "%min") expr_true expr_false expr_false));
 ("%minMaxCall", property_data
                 (data_intro (expr_id "%minMaxCall") expr_true expr_false
                  expr_false));
 ("%mkArgsObj", property_data
                (data_intro (expr_id "%mkArgsObj") expr_true expr_false
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
 ("%newDeclEnvRec", property_data
                    (data_intro (expr_id "%newDeclEnvRec") expr_true
                     expr_false expr_false));
 ("%newObjEnvRec", property_data
                   (data_intro (expr_id "%newObjEnvRec") expr_true expr_false
                    expr_false));
 ("%notEqEq", property_data
              (data_intro (expr_id "%notEqEq") expr_true expr_false
               expr_false));
 ("%notStxEq", property_data
               (data_intro (expr_id "%notStxEq") expr_true expr_false
                expr_false));
 ("%numTLS", property_data
             (data_intro (expr_id "%numTLS") expr_true expr_false expr_false));
 ("%numTLSCall", property_data
                 (data_intro (expr_id "%numTLSCall") expr_true expr_false
                  expr_false));
 ("%numToStringAbstract", property_data
                          (data_intro (expr_id "%numToStringAbstract")
                           expr_true expr_false expr_false));
 ("%numberPrimval", property_data
                    (data_intro (expr_id "%numberPrimval") expr_true
                     expr_false expr_false));
 ("%numberToString", property_data
                     (data_intro (expr_id "%numberToString") expr_true
                      expr_false expr_false));
 ("%numberToStringCall", property_data
                         (data_intro (expr_id "%numberToStringCall")
                          expr_true expr_false expr_false));
 ("%numberValueOf", property_data
                    (data_intro (expr_id "%numberValueOf") expr_true
                     expr_false expr_false));
 ("%objectToString", property_data
                     (data_intro (expr_id "%objectToString") expr_true
                      expr_false expr_false));
 ("%objectToStringCall", property_data
                         (data_intro (expr_id "%objectToStringCall")
                          expr_true expr_false expr_false));
 ("%objectValueOf", property_data
                    (data_intro (expr_id "%objectValueOf") expr_true
                     expr_false expr_false));
 ("%objectValueOfCall", property_data
                        (data_intro (expr_id "%objectValueOfCall") expr_true
                         expr_false expr_false));
 ("%oneArgObj", property_data
                (data_intro (expr_id "%oneArgObj") expr_true expr_false
                 expr_false));
 ("%parse", property_data
            (data_intro (expr_id "%parse") expr_true expr_false expr_false));
 ("%parseFloat", property_data
                 (data_intro (expr_id "%parseFloat") expr_true expr_false
                  expr_false));
 ("%parseFloatCall", property_data
                     (data_intro (expr_id "%parseFloatCall") expr_true
                      expr_false expr_false));
 ("%parseInt", property_data
               (data_intro (expr_id "%parseInt") expr_true expr_false
                expr_false));
 ("%parseIntCall", property_data
                   (data_intro (expr_id "%parseIntCall") expr_true expr_false
                    expr_false));
 ("%pop", property_data
          (data_intro (expr_id "%pop") expr_true expr_false expr_false));
 ("%popCall", property_data
              (data_intro (expr_id "%popCall") expr_true expr_false
               expr_false));
 ("%preventExtensions", property_data
                        (data_intro (expr_id "%preventExtensions") expr_true
                         expr_false expr_false));
 ("%preventExtensionsCall", property_data
                            (data_intro (expr_id "%preventExtensionsCall")
                             expr_true expr_false expr_false));
 ("%primEach", property_data
               (data_intro (expr_id "%primEach") expr_true expr_false
                expr_false));
 ("%print", property_data
            (data_intro (expr_id "%print") expr_true expr_false expr_false));
 ("%printCall", property_data
                (data_intro (expr_id "%printCall") expr_true expr_false
                 expr_false));
 ("%propEnum", property_data
               (data_intro (expr_id "%propEnum") expr_true expr_false
                expr_false));
 ("%propEnumCall", property_data
                   (data_intro (expr_id "%propEnumCall") expr_true expr_false
                    expr_false));
 ("%propertyNames", property_data
                    (data_intro (expr_id "%propertyNames") expr_true
                     expr_false expr_false));
 ("%protoOfField", property_data
                   (data_intro (expr_id "%protoOfField") expr_true expr_false
                    expr_false));
 ("%push", property_data
           (data_intro (expr_id "%push") expr_true expr_false expr_false));
 ("%pushCall", property_data
               (data_intro (expr_id "%pushCall") expr_true expr_false
                expr_false));
 ("%random", property_data
             (data_intro (expr_id "%random") expr_true expr_false expr_false));
 ("%randomCall", property_data
                 (data_intro (expr_id "%randomCall") expr_true expr_false
                  expr_false));
 ("%reduce", property_data
             (data_intro (expr_id "%reduce") expr_true expr_false expr_false));
 ("%reduceCall", property_data
                 (data_intro (expr_id "%reduceCall") expr_true expr_false
                  expr_false));
 ("%reduceRight", property_data
                  (data_intro (expr_id "%reduceRight") expr_true expr_false
                   expr_false));
 ("%reduceRightCall", property_data
                      (data_intro (expr_id "%reduceRightCall") expr_true
                       expr_false expr_false));
 ("%replace", property_data
              (data_intro (expr_id "%replace") expr_true expr_false
               expr_false));
 ("%replaceCall", property_data
                  (data_intro (expr_id "%replaceCall") expr_true expr_false
                   expr_false));
 ("%resolveThis", property_data
                  (data_intro (expr_id "%resolveThis") expr_true expr_false
                   expr_false));
 ("%reverse", property_data
              (data_intro (expr_id "%reverse") expr_true expr_false
               expr_false));
 ("%reverseCall", property_data
                  (data_intro (expr_id "%reverseCall") expr_true expr_false
                   expr_false));
 ("%round", property_data
            (data_intro (expr_id "%round") expr_true expr_false expr_false));
 ("%roundCall", property_data
                (data_intro (expr_id "%roundCall") expr_true expr_false
                 expr_false));
 ("%runConstruct", property_data
                   (data_intro (expr_id "%runConstruct") expr_true expr_false
                    expr_false));
 ("%seal", property_data
           (data_intro (expr_id "%seal") expr_true expr_false expr_false));
 ("%sealCall", property_data
               (data_intro (expr_id "%sealCall") expr_true expr_false
                expr_false));
 ("%set-property", property_data
                   (data_intro (expr_id "%set-property") expr_true expr_false
                    expr_false));
 ("%shift", property_data
            (data_intro (expr_id "%shift") expr_true expr_false expr_false));
 ("%shiftCall", property_data
                (data_intro (expr_id "%shiftCall") expr_true expr_false
                 expr_false));
 ("%sin", property_data
          (data_intro (expr_id "%sin") expr_true expr_false expr_false));
 ("%sinCall", property_data
              (data_intro (expr_id "%sinCall") expr_true expr_false
               expr_false));
 ("%slice", property_data
            (data_intro (expr_id "%slice") expr_true expr_false expr_false));
 ("%sliceCall", property_data
                (data_intro (expr_id "%sliceCall") expr_true expr_false
                 expr_false));
 ("%slice_internal", property_data
                     (data_intro (expr_id "%slice_internal") expr_true
                      expr_false expr_false));
 ("%some", property_data
           (data_intro (expr_id "%some") expr_true expr_false expr_false));
 ("%someCall", property_data
               (data_intro (expr_id "%someCall") expr_true expr_false
                expr_false));
 ("%sort", property_data
           (data_intro (expr_id "%sort") expr_true expr_false expr_false));
 ("%sortCall", property_data
               (data_intro (expr_id "%sortCall") expr_true expr_false
                expr_false));
 ("%splice", property_data
             (data_intro (expr_id "%splice") expr_true expr_false expr_false));
 ("%spliceCall", property_data
                 (data_intro (expr_id "%spliceCall") expr_true expr_false
                  expr_false));
 ("%split", property_data
            (data_intro (expr_id "%split") expr_true expr_false expr_false));
 ("%splitCall", property_data
                (data_intro (expr_id "%splitCall") expr_true expr_false
                 expr_false));
 ("%sqrt", property_data
           (data_intro (expr_id "%sqrt") expr_true expr_false expr_false));
 ("%sqrtCall", property_data
               (data_intro (expr_id "%sqrtCall") expr_true expr_false
                expr_false));
 ("%stringConcat", property_data
                   (data_intro (expr_id "%stringConcat") expr_true expr_false
                    expr_false));
 ("%stringConcatCall", property_data
                       (data_intro (expr_id "%stringConcatCall") expr_true
                        expr_false expr_false));
 ("%stringIndexOf", property_data
                    (data_intro (expr_id "%stringIndexOf") expr_true
                     expr_false expr_false));
 ("%stringIndexOfCall", property_data
                        (data_intro (expr_id "%stringIndexOfCall") expr_true
                         expr_false expr_false));
 ("%stringLastIndexOf", property_data
                        (data_intro (expr_id "%stringLastIndexOf") expr_true
                         expr_false expr_false));
 ("%stringLastIndexOfCall", property_data
                            (data_intro (expr_id "%stringLastIndexOfCall")
                             expr_true expr_false expr_false));
 ("%stringSlice", property_data
                  (data_intro (expr_id "%stringSlice") expr_true expr_false
                   expr_false));
 ("%stringSliceCall", property_data
                      (data_intro (expr_id "%stringSliceCall") expr_true
                       expr_false expr_false));
 ("%stringToString", property_data
                     (data_intro (expr_id "%stringToString") expr_true
                      expr_false expr_false));
 ("%stringToStringCall", property_data
                         (data_intro (expr_id "%stringToStringCall")
                          expr_true expr_false expr_false));
 ("%stringValueOf", property_data
                    (data_intro (expr_id "%stringValueOf") expr_true
                     expr_false expr_false));
 ("%substring", property_data
                (data_intro (expr_id "%substring") expr_true expr_false
                 expr_false));
 ("%substringCall", property_data
                    (data_intro (expr_id "%substringCall") expr_true
                     expr_false expr_false));
 ("%tan", property_data
          (data_intro (expr_id "%tan") expr_true expr_false expr_false));
 ("%tanCall", property_data
              (data_intro (expr_id "%tanCall") expr_true expr_false
               expr_false));
 ("%test", property_data
           (data_intro (expr_id "%test") expr_true expr_false expr_false));
 ("%testCall", property_data
               (data_intro (expr_id "%testCall") expr_true expr_false
                expr_false));
 ("%toExponential", property_data
                    (data_intro (expr_id "%toExponential") expr_true
                     expr_false expr_false));
 ("%toExponentialCall", property_data
                        (data_intro (expr_id "%toExponentialCall") expr_true
                         expr_false expr_false));
 ("%toFixed", property_data
              (data_intro (expr_id "%toFixed") expr_true expr_false
               expr_false));
 ("%toFixedCall", property_data
                  (data_intro (expr_id "%toFixedCall") expr_true expr_false
                   expr_false));
 ("%toLocaleString", property_data
                     (data_intro (expr_id "%toLocaleString") expr_true
                      expr_false expr_false));
 ("%toLocaleStringCall", property_data
                         (data_intro (expr_id "%toLocaleStringCall")
                          expr_true expr_false expr_false));
 ("%toLowerCase", property_data
                  (data_intro (expr_id "%toLowerCase") expr_true expr_false
                   expr_false));
 ("%toLowerCaseCall", property_data
                      (data_intro (expr_id "%toLowerCaseCall") expr_true
                       expr_false expr_false));
 ("%toPrecision", property_data
                  (data_intro (expr_id "%toPrecision") expr_true expr_false
                   expr_false));
 ("%toPrecisionCall", property_data
                      (data_intro (expr_id "%toPrecisionCall") expr_true
                       expr_false expr_false));
 ("%toUpperCase", property_data
                  (data_intro (expr_id "%toUpperCase") expr_true expr_false
                   expr_false));
 ("%toUpperCaseCall", property_data
                      (data_intro (expr_id "%toUpperCaseCall") expr_true
                       expr_false expr_false));
 ("%twoArgObj", property_data
                (data_intro (expr_id "%twoArgObj") expr_true expr_false
                 expr_false));
 ("%unescape", property_data
               (data_intro (expr_id "%unescape") expr_true expr_false
                expr_false));
 ("%unescapeCall", property_data
                   (data_intro (expr_id "%unescapeCall") expr_true expr_false
                    expr_false));
 ("%unshift", property_data
              (data_intro (expr_id "%unshift") expr_true expr_false
               expr_false));
 ("%unshiftCall", property_data
                  (data_intro (expr_id "%unshiftCall") expr_true expr_false
                   expr_false));
 ("%valueOfCall", property_data
                  (data_intro (expr_id "%valueOfCall") expr_true expr_false
                   expr_false));
 ("%zeroArgObj", property_data
                 (data_intro (expr_id "%zeroArgObj") expr_true expr_false
                  expr_false));
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
Definition ex_internal := 
expr_let "cproto1"
(expr_app (expr_id "%Get1") [expr_id "constr"; expr_string "prototype"])
(expr_let "cproto"
 (expr_if (expr_op1 unary_op_is_object (expr_id "cproto1"))
  (expr_id "cproto1") (expr_id "%ObjectProto"))
 (expr_let "newobj"
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true (expr_id "cproto")
    expr_undefined) [] [])
  (expr_let "constr_ret"
   (expr_app (expr_id "%AppExpr")
    [expr_id "constr"; expr_id "newobj"; expr_id "args"])
   (expr_if (expr_op1 unary_op_is_object (expr_id "constr_ret"))
    (expr_id "constr_ret") (expr_id "newobj")))))
.
Definition ex_internal1 := 
expr_app (expr_id "%MakeNumber")
[expr_if
 (expr_op2 binary_op_stx_eq
  (expr_app (expr_id "%ComputeLength") [expr_id "args"])
  (expr_number (JsNumber.of_int (0)))) (expr_number (JsNumber.of_int (0)))
 (expr_app (expr_id "%ToNumber")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])]
.
Definition ex_internal10 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal11 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal12 := 
expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op2 binary_op_ge (expr_id "argCount")
    (expr_number (JsNumber.of_int (2))))
   (expr_let "rtnobj"
    (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
    (expr_recc "init"
     (expr_lambda ["n"]
      (expr_seq
       (expr_set_attr pattr_value (expr_id "rtnobj")
        (expr_op1 unary_op_prim_to_str (expr_id "n"))
        (expr_get_attr pattr_value (expr_id "args")
         (expr_op1 unary_op_prim_to_str (expr_id "n"))))
       (expr_if
        (expr_op2 binary_op_gt (expr_id "n")
         (expr_number (JsNumber.of_int (0))))
        (expr_app (expr_id "init")
         [expr_op2 binary_op_sub (expr_id "n")
          (expr_number (JsNumber.of_int (1)))]) expr_undefined)))
     (expr_seq (expr_app (expr_id "init") [expr_id "argCount"])
      (expr_seq
       (expr_set_attr pattr_value (expr_id "rtnobj") (expr_string "length")
        (expr_id "argCount")) (expr_break "ret" (expr_id "rtnobj"))))))
   expr_null)
  (expr_let "c1"
   (expr_op2 binary_op_stx_eq
    (expr_op1 unary_op_typeof
     (expr_get_attr pattr_value (expr_id "args") (expr_string "0")))
    (expr_string "number"))
   (expr_let "c2"
    (expr_if (expr_id "c1")
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq
       (expr_app (expr_id "%ToUint32")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
       (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))))
     expr_false)
    (expr_if (expr_id "c2")
     (expr_throw
      (expr_app (expr_id "%JSError")
       [expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "%RangeErrorProto") expr_undefined) [] []]))
     (expr_if (expr_id "c1")
      (expr_break "ret"
       (expr_app (expr_id "%MakeArray")
        [expr_app (expr_id "%ToUint32")
         [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]]))
      (expr_let "rtn" (expr_app (expr_id "%MakeArray") [expr_id "argCount"])
       (expr_seq
        (expr_app (expr_id "%defineOwnProperty")
         [expr_id "rtn";
          expr_string "0";
          expr_object
          (objattrs_intro (expr_string "Object") expr_true expr_null
           expr_undefined) []
          [("value", property_data
                     (data_intro
                      (expr_get_attr pattr_value (expr_id "args")
                       (expr_string "0")) expr_true expr_false expr_false));
           ("writable", property_data
                        (data_intro expr_true expr_true expr_false expr_false));
           ("enumerable", property_data
                          (data_intro expr_true expr_true expr_false
                           expr_false));
           ("configurable", property_data
                            (data_intro expr_true expr_true expr_false
                             expr_false))]])
        (expr_break "ret" (expr_id "rtn"))))))))))
.
Definition ex_internal13 := 
expr_let "nargs" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "nargs")
  (expr_number (JsNumber.of_int (0))))
 (expr_app (expr_id "%MakeDate") [expr_app (expr_id "%getCurrentUTC") []])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "nargs")
   (expr_number (JsNumber.of_int (1))))
  (expr_let "v"
   (expr_app (expr_id "%ToPrimitive")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "V"
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "v"))
      (expr_string "string")) (expr_app (expr_id "%parse") [expr_id "v"])
     (expr_app (expr_id "%ToNumber") [expr_id "v"]))
    (expr_let "clipped" (expr_app (expr_id "%TimeClip") [expr_id "V"])
     (expr_object
      (objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
       expr_undefined) [("primval", expr_id "clipped")] []))))
  (expr_let "y"
   (expr_app (expr_id "%ToNumber")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "m"
    (expr_app (expr_id "%ToNumber")
     [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
    (expr_let "dt"
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_attr pattr_value (expr_id "args") (expr_string "2"))
       expr_undefined) (expr_number (JsNumber.of_int (1)))
      (expr_app (expr_id "%ToNumber")
       [expr_get_attr pattr_value (expr_id "args") (expr_string "2")]))
     (expr_let "h"
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_attr pattr_value (expr_id "args") (expr_string "3"))
        expr_undefined) (expr_number (JsNumber.of_int (0)))
       (expr_app (expr_id "%ToNumber")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "3")]))
      (expr_let "min"
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_attr pattr_value (expr_id "args") (expr_string "4"))
         expr_undefined) (expr_number (JsNumber.of_int (0)))
        (expr_app (expr_id "%ToNumber")
         [expr_get_attr pattr_value (expr_id "args") (expr_string "4")]))
       (expr_let "s"
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_attr pattr_value (expr_id "args") (expr_string "5"))
          expr_undefined) (expr_number (JsNumber.of_int (0)))
         (expr_app (expr_id "%ToNumber")
          [expr_get_attr pattr_value (expr_id "args") (expr_string "5")]))
        (expr_let "milli"
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_attr pattr_value (expr_id "args") (expr_string "6"))
           expr_undefined) (expr_number (JsNumber.of_int (0)))
          (expr_app (expr_id "%ToNumber")
           [expr_get_attr pattr_value (expr_id "args") (expr_string "6")]))
         (expr_let "yr"
          (expr_let "tiy" (expr_app (expr_id "%ToInteger") [expr_id "y"])
           (expr_let "rangecond1"
            (expr_if
             (expr_op2 binary_op_lt (expr_number (JsNumber.of_int (0)))
              (expr_id "tiy")) expr_true
             (expr_op2 binary_op_stx_eq (expr_number (JsNumber.of_int (0)))
              (expr_id "tiy")))
            (expr_let "rangecond2"
             (expr_if
              (expr_op2 binary_op_lt (expr_id "tiy")
               (expr_number (JsNumber.of_int (99)))) expr_true
              (expr_op2 binary_op_stx_eq (expr_id "tiy")
               (expr_number (JsNumber.of_int (99)))))
             (expr_if
              (expr_if
               (expr_if
                (expr_op1 unary_op_not
                 (expr_op2 binary_op_stx_eq (expr_id "y") (expr_id "y")))
                (expr_id "rangecond1") expr_false) (expr_id "rangecond2")
               expr_false)
              (expr_op2 binary_op_add (expr_number (JsNumber.of_int (1900)))
               (expr_id "tiy")) (expr_id "y")))))
          (expr_let "finalDate"
           (expr_app (expr_id "%MakeDateDayTime")
            [expr_app (expr_id "%MakeDay")
             [expr_id "yr"; expr_id "m"; expr_id "dt"];
             expr_app (expr_id "%MakeTime")
             [expr_id "h"; expr_id "min"; expr_id "s"; expr_id "milli"]])
           (expr_let "primval"
            (expr_app (expr_id "%TimeClip")
             [expr_app (expr_id "%UTC") [expr_id "finalDate"]])
            (expr_object
             (objattrs_intro (expr_string "Date") expr_true
              (expr_id "%DateProto") expr_undefined)
             [("primval", expr_id "primval")] [])))))))))))))
.
Definition ex_internal14 := 
expr_object
(objattrs_intro (expr_string "Object") expr_true (expr_id "%RegExpProto")
 expr_undefined) [] []
.
Definition ex_internal15 := 
expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_recc "formArgString"
 (expr_lambda ["n"; "result"]
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "n")
    (expr_op2 binary_op_sub (expr_id "argCount")
     (expr_number (JsNumber.of_int (1))))) (expr_id "result")
   (expr_let "currentArg"
    (expr_app (expr_id "%ToString")
     [expr_get_attr pattr_value (expr_id "args")
      (expr_op1 unary_op_prim_to_str (expr_id "n"))])
    (expr_let "next"
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_op2 binary_op_sub (expr_id "argCount")
        (expr_number (JsNumber.of_int (2)))))
      (expr_op2 binary_op_string_plus (expr_id "result")
       (expr_id "currentArg"))
      (expr_op2 binary_op_string_plus
       (expr_op2 binary_op_string_plus (expr_id "result")
        (expr_id "currentArg")) (expr_string ",")))
     (expr_app (expr_id "formArgString")
      [expr_op2 binary_op_add (expr_id "n")
       (expr_number (JsNumber.of_int (1)));
       expr_id "next"])))))
 (expr_let "body"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "argCount")
    (expr_number (JsNumber.of_int (0)))) (expr_string "")
   (expr_get_attr pattr_value (expr_id "args")
    (expr_op1 unary_op_prim_to_str
     (expr_op2 binary_op_sub (expr_id "argCount")
      (expr_number (JsNumber.of_int (1)))))))
  (expr_let "P"
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "argCount")
      (expr_number (JsNumber.of_int (0)))) expr_true
     (expr_op2 binary_op_stx_eq (expr_id "argCount")
      (expr_number (JsNumber.of_int (1))))) (expr_string "")
    (expr_app (expr_id "formArgString")
     [expr_number (JsNumber.of_int (0)); expr_string ""]))
   (expr_let "prefix"
    (expr_op2 binary_op_string_plus
     (expr_string "((function(){ return function (")
     (expr_op2 binary_op_string_plus (expr_id "P") (expr_string "){")))
    (expr_let "final"
     (expr_op2 binary_op_string_plus (expr_id "prefix")
      (expr_op2 binary_op_string_plus (expr_id "body")
       (expr_string "}; })());")))
     (expr_app (expr_id "%evalCall")
      [expr_undefined;
       expr_object
       (objattrs_intro (expr_string "Object") expr_true expr_null
        expr_undefined) []
       [("0", property_data
              (data_intro (expr_id "final") expr_false expr_false expr_false))]]))))))
.
Definition ex_internal2 := 
expr_app (expr_id "%MakeString")
[expr_app (expr_id "%StringCall")
 [expr_undefined; expr_undefined; expr_id "args"]]
.
Definition ex_internal3 := 
expr_app (expr_id "%MakeBoolean")
[expr_app (expr_id "%ToBoolean")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]]
.
Definition ex_internal4 := 
expr_app (expr_id "%ObjectCall")
[expr_id "constr"; expr_undefined; expr_id "args"]
.
Definition ex_internal5 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal6 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal7 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal8 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_internal9 := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_isAccessorDescriptor := 
expr_if
(expr_op2 binary_op_has_own_property (expr_id "attr-obj") (expr_string "get"))
expr_true
(expr_op2 binary_op_has_own_property (expr_id "attr-obj") (expr_string "set"))
.
Definition ex_isAccessorField := 
expr_if
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_setter (expr_id "obj") (expr_id "field"))
  expr_undefined)) expr_true
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_getter (expr_id "obj") (expr_id "field"))
  expr_undefined))
.
Definition ex_isDataDescriptor := 
expr_if
(expr_op2 binary_op_has_own_property (expr_id "attr-obj")
 (expr_string "value")) expr_true
(expr_op2 binary_op_has_own_property (expr_id "attr-obj")
 (expr_string "writable"))
.
Definition ex_isDataField := 
expr_if
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "obj") (expr_id "field"))
  expr_undefined)) expr_true
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_writable (expr_id "obj") (expr_id "field"))
  expr_undefined))
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
Definition ex_objCode1 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
.
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
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
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
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
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
expr_app (expr_id "%valueOfCall")
[expr_id "this"; expr_id "args"; expr_id "%StringProto"; expr_string "string"]
.
Definition ex_objCode36 := 
expr_app (expr_id "%valueOfCall")
[expr_id "this"; expr_id "args"; expr_id "%NumberProto"; expr_string "number"]
.
Definition ex_objCode37 := 
expr_app (expr_id "%valueOfCall")
[expr_id "this";
 expr_id "args";
 expr_id "%BooleanProto";
 expr_string "boolean"]
.
Definition ex_objCode4 := 
expr_app (expr_id "%TypeError")
[expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]
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
Definition ex_privAddAccessorField := 
expr_seq
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "name"))
 (expr_fail "property already exists in %AddAccessorField") expr_undefined)
(expr_seq
 (expr_set_attr pattr_getter (expr_id "obj") (expr_id "name") (expr_id "g"))
 (expr_seq
  (expr_set_attr pattr_setter (expr_id "obj") (expr_id "name") (expr_id "s"))
  (expr_seq
   (expr_set_attr pattr_enum (expr_id "obj") (expr_id "name") (expr_id "e"))
   (expr_seq
    (expr_set_attr pattr_config (expr_id "obj") (expr_id "name")
     (expr_id "c")) expr_undefined))))
.
Definition ex_privAddDataField := 
expr_seq
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "name"))
 (expr_fail "property already exists in %AddDataField") expr_undefined)
(expr_seq
 (expr_set_attr pattr_value (expr_id "obj") (expr_id "name") (expr_id "v"))
 (expr_seq
  (expr_set_attr pattr_writable (expr_id "obj") (expr_id "name")
   (expr_id "w"))
  (expr_seq
   (expr_set_attr pattr_enum (expr_id "obj") (expr_id "name") (expr_id "e"))
   (expr_seq
    (expr_set_attr pattr_config (expr_id "obj") (expr_id "name")
     (expr_id "c")) expr_undefined))))
.
Definition ex_privAppExpr := 
expr_app (expr_id "fun") [expr_id "this"; expr_id "args"]
.
Definition ex_privAppExprCheck := 
expr_if (expr_app (expr_id "%IsCallable") [expr_id "fun"])
(expr_app (expr_id "%AppExpr")
 [expr_id "fun"; expr_id "this"; expr_id "args"])
(expr_app (expr_id "%TypeError") [expr_string "Not a function"])
.
Definition ex_privAppMethodOp := 
expr_lambda ["v"; "fld"; "strict"]
(expr_let "fun" (expr_app (expr_id "%GetField") [expr_id "v"; expr_id "fld"])
 (expr_let "args" (expr_app (expr_id "fargs") [])
  (expr_app (expr_id "%AppExprCheck")
   [expr_id "fun"; expr_id "v"; expr_id "args"])))
.
Definition ex_privArrayCall := 
expr_app (expr_id "%ArrayConstructor") [expr_id "obj"; expr_id "args"]
.
Definition ex_privArrayConstructor := 
expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op2 binary_op_ge (expr_id "argCount")
    (expr_number (JsNumber.of_int (2))))
   (expr_let "rtnobj"
    (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
    (expr_recc "init"
     (expr_lambda ["n"]
      (expr_seq
       (expr_set_attr pattr_value (expr_id "rtnobj")
        (expr_op1 unary_op_prim_to_str (expr_id "n"))
        (expr_get_attr pattr_value (expr_id "args")
         (expr_op1 unary_op_prim_to_str (expr_id "n"))))
       (expr_if
        (expr_op2 binary_op_gt (expr_id "n")
         (expr_number (JsNumber.of_int (0))))
        (expr_app (expr_id "init")
         [expr_op2 binary_op_sub (expr_id "n")
          (expr_number (JsNumber.of_int (1)))]) expr_undefined)))
     (expr_seq (expr_app (expr_id "init") [expr_id "argCount"])
      (expr_seq
       (expr_set_attr pattr_value (expr_id "rtnobj") (expr_string "length")
        (expr_id "argCount")) (expr_break "ret" (expr_id "rtnobj"))))))
   expr_null)
  (expr_let "c1"
   (expr_op2 binary_op_stx_eq
    (expr_op1 unary_op_typeof
     (expr_get_attr pattr_value (expr_id "args") (expr_string "0")))
    (expr_string "number"))
   (expr_let "c2"
    (expr_if (expr_id "c1")
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq
       (expr_app (expr_id "%ToUint32")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
       (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))))
     expr_false)
    (expr_if (expr_id "c2")
     (expr_throw
      (expr_app (expr_id "%JSError")
       [expr_object
        (objattrs_intro (expr_string "Object") expr_true
         (expr_id "%RangeErrorProto") expr_undefined) [] []]))
     (expr_if (expr_id "c1")
      (expr_break "ret"
       (expr_app (expr_id "%MakeArray")
        [expr_app (expr_id "%ToUint32")
         [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]]))
      (expr_let "rtn" (expr_app (expr_id "%MakeArray") [expr_id "argCount"])
       (expr_seq
        (expr_app (expr_id "%defineOwnProperty")
         [expr_id "rtn";
          expr_string "0";
          expr_object
          (objattrs_intro (expr_string "Object") expr_true expr_null
           expr_undefined) []
          [("value", property_data
                     (data_intro
                      (expr_get_attr pattr_value (expr_id "args")
                       (expr_string "0")) expr_true expr_false expr_false));
           ("writable", property_data
                        (data_intro expr_true expr_true expr_false expr_false));
           ("enumerable", property_data
                          (data_intro expr_true expr_true expr_false
                           expr_false));
           ("configurable", property_data
                            (data_intro expr_true expr_true expr_false
                             expr_false))]])
        (expr_break "ret" (expr_id "rtn"))))))))))
.
Definition ex_privArrayIdx := 
expr_if (expr_op2 binary_op_has_own_property (expr_id "arr") (expr_id "idx"))
(expr_get_attr pattr_value (expr_id "arr") (expr_id "idx")) expr_undefined
.
Definition ex_privArrayLengthChange := 
expr_let "oldlen"
(expr_app (expr_id "%ToUint32")
 [expr_app (expr_id "%Get1") [expr_id "arr"; expr_string "length"]])
(expr_recc "fix"
 (expr_lambda ["i"]
  (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "oldlen"))
   (expr_seq
    (expr_app (expr_id "%Delete")
     [expr_id "arr"; expr_op1 unary_op_prim_to_str (expr_id "i"); expr_false])
    (expr_app (expr_id "fix")
     [expr_op2 binary_op_add (expr_id "i")
      (expr_number (JsNumber.of_int (1)))])) expr_undefined))
 (expr_app (expr_id "fix") [expr_id "newlen"]))
.
Definition ex_privBindConstructor := 
expr_let "concatted"
(expr_app (expr_id "%concat")
 [expr_get_internal "boundArgs" (expr_id "constr"); expr_id "args"])
(expr_app (expr_id "%PrimNew")
 [expr_get_internal "target" (expr_id "constr"); expr_id "concatted"])
.
Definition ex_privBindObjCall := 
expr_let "concatted"
(expr_app (expr_id "%concat")
 [expr_get_internal "boundArgs" (expr_id "obj"); expr_id "args"])
(expr_app (expr_id "%AppExprCheck")
 [expr_get_internal "target" (expr_id "obj");
  expr_get_internal "boundThis" (expr_id "obj");
  expr_id "concatted"])
.
Definition ex_privBitwiseAnd := 
expr_app (expr_id "%BitwiseInfix")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_band (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privBitwiseInfix := 
expr_let "lnum" (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_let "rnum" (expr_app (expr_id "%ToInt32") [expr_id "r"])
 (expr_app (expr_id "op") [expr_id "lnum"; expr_id "rnum"]))
.
Definition ex_privBitwiseNot := 
expr_op1 unary_op_bnot (expr_app (expr_id "%ToInt32") [expr_id "expr"])
.
Definition ex_privBitwiseOr := 
expr_app (expr_id "%BitwiseInfix")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_bor (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privBitwiseXor := 
expr_app (expr_id "%BitwiseInfix")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_bxor (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privBooleanCall := 
expr_app (expr_id "%ToBoolean")
[expr_get_attr pattr_value (expr_id "args") (expr_string "0")]
.
Definition ex_privBooleanConstructor := 
expr_app (expr_id "%MakeBoolean")
[expr_app (expr_id "%ToBoolean")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]]
.
Definition ex_privCheckObjectCoercible := 
expr_if
(expr_if (expr_op2 binary_op_stx_eq (expr_id "o") expr_undefined) expr_true
 (expr_op2 binary_op_stx_eq (expr_id "o") expr_null))
(expr_app (expr_id "%TypeError") [expr_string "Not object coercible"])
expr_empty
.
Definition ex_privCompareOp := 
expr_let "px" (expr_app (expr_id "%ToPrimitive") [expr_id "l"])
(expr_let "py" (expr_app (expr_id "%ToPrimitive") [expr_id "r"])
 (expr_let "res"
  (expr_if (expr_id "swap")
   (expr_app (expr_id "%PrimitiveCompareOp") [expr_id "py"; expr_id "px"])
   (expr_app (expr_id "%PrimitiveCompareOp") [expr_id "px"; expr_id "py"]))
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "res") expr_undefined)
   expr_false
   (expr_if (expr_id "neg") (expr_op1 unary_op_not (expr_id "res"))
    (expr_id "res")))))
.
Definition ex_privComputeLength := 
expr_recc "loop"
(expr_lambda ["iter"]
 (expr_let "strx" (expr_op1 unary_op_prim_to_str (expr_id "iter"))
  (expr_if
   (expr_op2 binary_op_has_own_property (expr_id "args") (expr_id "strx"))
   (expr_app (expr_id "loop")
    [expr_op2 binary_op_add (expr_id "iter")
     (expr_number (JsNumber.of_int (1)))]) (expr_id "iter"))))
(expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
.
Definition ex_privDateCall := 
expr_let "o"
(expr_app (expr_id "%MakeDate") [expr_app (expr_id "%getCurrentUTC") []])
(expr_app (expr_id "%dateToString")
 [expr_id "o";
  expr_object
  (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
  [] []])
.
Definition ex_privDateConstructor := 
expr_let "nargs" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "nargs")
  (expr_number (JsNumber.of_int (0))))
 (expr_app (expr_id "%MakeDate") [expr_app (expr_id "%getCurrentUTC") []])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "nargs")
   (expr_number (JsNumber.of_int (1))))
  (expr_let "v"
   (expr_app (expr_id "%ToPrimitive")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "V"
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "v"))
      (expr_string "string")) (expr_app (expr_id "%parse") [expr_id "v"])
     (expr_app (expr_id "%ToNumber") [expr_id "v"]))
    (expr_let "clipped" (expr_app (expr_id "%TimeClip") [expr_id "V"])
     (expr_object
      (objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
       expr_undefined) [("primval", expr_id "clipped")] []))))
  (expr_let "y"
   (expr_app (expr_id "%ToNumber")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "m"
    (expr_app (expr_id "%ToNumber")
     [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
    (expr_let "dt"
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_attr pattr_value (expr_id "args") (expr_string "2"))
       expr_undefined) (expr_number (JsNumber.of_int (1)))
      (expr_app (expr_id "%ToNumber")
       [expr_get_attr pattr_value (expr_id "args") (expr_string "2")]))
     (expr_let "h"
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_attr pattr_value (expr_id "args") (expr_string "3"))
        expr_undefined) (expr_number (JsNumber.of_int (0)))
       (expr_app (expr_id "%ToNumber")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "3")]))
      (expr_let "min"
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_attr pattr_value (expr_id "args") (expr_string "4"))
         expr_undefined) (expr_number (JsNumber.of_int (0)))
        (expr_app (expr_id "%ToNumber")
         [expr_get_attr pattr_value (expr_id "args") (expr_string "4")]))
       (expr_let "s"
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_attr pattr_value (expr_id "args") (expr_string "5"))
          expr_undefined) (expr_number (JsNumber.of_int (0)))
         (expr_app (expr_id "%ToNumber")
          [expr_get_attr pattr_value (expr_id "args") (expr_string "5")]))
        (expr_let "milli"
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_attr pattr_value (expr_id "args") (expr_string "6"))
           expr_undefined) (expr_number (JsNumber.of_int (0)))
          (expr_app (expr_id "%ToNumber")
           [expr_get_attr pattr_value (expr_id "args") (expr_string "6")]))
         (expr_let "yr"
          (expr_let "tiy" (expr_app (expr_id "%ToInteger") [expr_id "y"])
           (expr_let "rangecond1"
            (expr_if
             (expr_op2 binary_op_lt (expr_number (JsNumber.of_int (0)))
              (expr_id "tiy")) expr_true
             (expr_op2 binary_op_stx_eq (expr_number (JsNumber.of_int (0)))
              (expr_id "tiy")))
            (expr_let "rangecond2"
             (expr_if
              (expr_op2 binary_op_lt (expr_id "tiy")
               (expr_number (JsNumber.of_int (99)))) expr_true
              (expr_op2 binary_op_stx_eq (expr_id "tiy")
               (expr_number (JsNumber.of_int (99)))))
             (expr_if
              (expr_if
               (expr_if
                (expr_op1 unary_op_not
                 (expr_op2 binary_op_stx_eq (expr_id "y") (expr_id "y")))
                (expr_id "rangecond1") expr_false) (expr_id "rangecond2")
               expr_false)
              (expr_op2 binary_op_add (expr_number (JsNumber.of_int (1900)))
               (expr_id "tiy")) (expr_id "y")))))
          (expr_let "finalDate"
           (expr_app (expr_id "%MakeDateDayTime")
            [expr_app (expr_id "%MakeDay")
             [expr_id "yr"; expr_id "m"; expr_id "dt"];
             expr_app (expr_id "%MakeTime")
             [expr_id "h"; expr_id "min"; expr_id "s"; expr_id "milli"]])
           (expr_let "primval"
            (expr_app (expr_id "%TimeClip")
             [expr_app (expr_id "%UTC") [expr_id "finalDate"]])
            (expr_object
             (objattrs_intro (expr_string "Date") expr_true
              (expr_id "%DateProto") expr_undefined)
             [("primval", expr_id "primval")] [])))))))))))))
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
   (expr_number (JsNumber.of_int (0))))
  (expr_op2 binary_op_add (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
   (expr_number (JsNumber.of_int (1))))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "mft")
    (expr_number (JsNumber.of_int (1))))
   (expr_op2 binary_op_sub
    (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
    (expr_number (JsNumber.of_int (30))))
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "mft")
     (expr_number (JsNumber.of_int (2))))
    (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (58))])
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "mft")
      (expr_number (JsNumber.of_int (3))))
     (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (89))])
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "mft")
       (expr_number (JsNumber.of_int (4))))
      (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (119))])
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "mft")
        (expr_number (JsNumber.of_int (5))))
       (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (150))])
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "mft")
         (expr_number (JsNumber.of_int (6))))
        (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (180))])
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "mft")
          (expr_number (JsNumber.of_int (7))))
         (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (211))])
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "mft")
           (expr_number (JsNumber.of_int (8))))
          (expr_app (expr_id "CalcDay") [expr_number (JsNumber.of_int (242))])
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "mft")
            (expr_number (JsNumber.of_int (9))))
           (expr_app (expr_id "CalcDay")
            [expr_number (JsNumber.of_int (272))])
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "mft")
             (expr_number (JsNumber.of_int (10))))
            (expr_app (expr_id "CalcDay")
             [expr_number (JsNumber.of_int (303))])
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "mft")
              (expr_number (JsNumber.of_int (11))))
             (expr_app (expr_id "CalcDay")
              [expr_number (JsNumber.of_int (333))])
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
 (expr_op2 binary_op_mul (expr_number (JsNumber.of_int (365)))
  (expr_op2 binary_op_sub (expr_id "y")
   (expr_number (JsNumber.of_int (1970)))))
 (expr_let "part1"
  (expr_app (expr_id "fragment")
   [expr_number (JsNumber.of_int (1969)); expr_number (JsNumber.of_int (4))])
  (expr_let "part2"
   (expr_app (expr_id "fragment")
    [expr_number (JsNumber.of_int (1901));
     expr_number (JsNumber.of_int (100))])
   (expr_let "part3"
    (expr_app (expr_id "fragment")
     [expr_number (JsNumber.of_int (1601));
      expr_number (JsNumber.of_int (400))])
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
(expr_op2 binary_op_mod (expr_id "m") (expr_number (JsNumber.of_int (12))))
(expr_if
 (expr_if
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "m")
     (expr_number (JsNumber.of_int (3)))) expr_true
    (expr_op2 binary_op_stx_eq (expr_id "m")
     (expr_number (JsNumber.of_int (5))))) expr_true
   (expr_op2 binary_op_stx_eq (expr_id "m")
    (expr_number (JsNumber.of_int (8))))) expr_true
  (expr_op2 binary_op_stx_eq (expr_id "m")
   (expr_number (JsNumber.of_int (10)))))
 (expr_number (JsNumber.of_int (30)))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "m")
   (expr_number (JsNumber.of_int (1))))
  (expr_op2 binary_op_add (expr_number (JsNumber.of_int (28)))
   (expr_id "leap")) (expr_number (JsNumber.of_int (31)))))
.
Definition ex_privDaysInYear := 
expr_if
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq
  (expr_op2 binary_op_mod (expr_id "y") (expr_number (JsNumber.of_int (4))))
  (expr_number (JsNumber.of_int (0))))) (expr_number (JsNumber.of_int (365)))
(expr_if
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_op2 binary_op_mod (expr_id "y")
    (expr_number (JsNumber.of_int (400))))
   (expr_number (JsNumber.of_int (0)))) expr_true
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq
    (expr_op2 binary_op_mod (expr_id "y")
     (expr_number (JsNumber.of_int (100))))
    (expr_number (JsNumber.of_int (0))))))
 (expr_number (JsNumber.of_int (366))) (expr_number (JsNumber.of_int (365))))
.
Definition ex_privDeclEnvAddBinding := 
expr_app (expr_id "%AddDataField")
[expr_id "context";
 expr_id "name";
 expr_id "val";
 expr_id "mutable";
 expr_true;
 expr_id "deletable"]
.
Definition ex_privDefaultCall := 
expr_app (expr_get_internal "usercode" (expr_id "obj"))
[expr_id "obj";
 expr_app (expr_id "%resolveThis")
 [expr_get_internal "strict" (expr_id "obj"); expr_id "this"];
 expr_id "args"]
.
Definition ex_privDefaultConstruct := 
expr_let "cproto1"
(expr_app (expr_id "%Get1") [expr_id "constr"; expr_string "prototype"])
(expr_let "cproto"
 (expr_if (expr_op1 unary_op_is_object (expr_id "cproto1"))
  (expr_id "cproto1") (expr_id "%ObjectProto"))
 (expr_let "newobj"
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true (expr_id "cproto")
    expr_undefined) [] [])
  (expr_let "constr_ret"
   (expr_app (expr_id "%AppExpr")
    [expr_id "constr"; expr_id "newobj"; expr_id "args"])
   (expr_if (expr_op1 unary_op_is_object (expr_id "constr_ret"))
    (expr_id "constr_ret") (expr_id "newobj")))))
.
Definition ex_privDelete := 
expr_if
(expr_op1 unary_op_not
 (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "fld")))
expr_true
(expr_if
 (expr_op1 unary_op_not
  (expr_get_attr pattr_config (expr_id "obj") (expr_id "fld")))
 (expr_if (expr_id "strict")
  (expr_app (expr_id "%TypeError")
   [expr_string "unconfigurable delete in strict mode"]) expr_false)
 (expr_seq (expr_delete_field (expr_id "obj") (expr_id "fld")) expr_true))
.
Definition ex_privDeleteOp := 
expr_app (expr_id "%Delete")
[expr_app (expr_id "%ToObject") [expr_id "obj"];
 expr_id "fld";
 expr_id "strict"]
.
Definition ex_privEnvAppExpr := 
expr_let "f"
(expr_lambda ["context"]
 (expr_let "fun"
  (expr_app (expr_id "%EnvGetValue")
   [expr_id "context"; expr_id "id"; expr_id "strict"])
  (expr_let "args" (expr_app (expr_id "args_thunk") [])
   (expr_if
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "id") (expr_string "eval"))
     (expr_op2 binary_op_stx_eq (expr_id "fun") (expr_id "%eval")) expr_false)
    (expr_app (expr_id "%configurableEval")
     [expr_id "this";
      expr_id "pcontext";
      expr_id "vcontext";
      expr_id "strict";
      expr_id "args"])
    (expr_if (expr_app (expr_id "%IsCallable") [expr_id "fun"])
     (expr_app (expr_id "%AppExpr")
      [expr_id "fun";
       expr_app (expr_id "%EnvImplicitThis") [expr_id "context"];
       expr_id "args"])
     (expr_app (expr_id "%TypeError") [expr_string "Not a function"]))))))
(expr_app (expr_id "%EnvGetId")
 [expr_id "pcontext"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvAssign := 
expr_let "f"
(expr_lambda ["context"]
 (expr_let "val" (expr_app (expr_id "val_thunk") [])
  (expr_seq
   (expr_app (expr_id "%EnvPutValue")
    [expr_id "context"; expr_id "id"; expr_id "val"; expr_id "strict"])
   (expr_id "val"))))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvCreateImmutableBinding := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_seq
 (expr_app (expr_id "%DeclEnvAddBinding")
  [expr_id "context"; expr_id "id"; expr_empty; expr_true; expr_false])
 expr_empty)
(expr_fail "[env] Context not well formed! In %EnvCreateImutableBinding")
.
Definition ex_privEnvCreateMutableBinding := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_seq
 (expr_app (expr_id "%DeclEnvAddBinding")
  [expr_id "context";
   expr_id "id";
   expr_undefined;
   expr_true;
   expr_id "configurable"]) expr_empty)
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "ObjEnvRec"))
 (expr_app (expr_id "%AddDataField")
  [expr_get_internal "bindings" (expr_id "context");
   expr_id "id";
   expr_undefined;
   expr_true;
   expr_true;
   expr_id "configurable"])
 (expr_throw
  (expr_string "[env] Context not well formed! In %EnvCreateMutableBinding")))
.
Definition ex_privEnvCreateSetMutableBinding := 
expr_seq
(expr_app (expr_id "%EnvCreateMutableBinding")
 [expr_id "context"; expr_id "id"; expr_id "configurable"])
(expr_app (expr_id "%EnvSetMutableBinding")
 [expr_id "context"; expr_id "id"; expr_id "val"; expr_id "strict"])
.
Definition ex_privEnvDefineArg := 
expr_seq
(expr_if
 (expr_op1 unary_op_not
  (expr_app (expr_id "%EnvHasBinding") [expr_id "context"; expr_id "id"]))
 (expr_app (expr_id "%EnvCreateMutableBinding")
  [expr_id "context"; expr_id "id"; expr_false]) expr_undefined)
(expr_seq
 (expr_app (expr_id "%EnvSetMutableBinding")
  [expr_id "context"; expr_id "id"; expr_id "val"; expr_id "strict"])
 expr_empty)
.
Definition ex_privEnvDefineArgsObj := 
expr_seq
(expr_if
 (expr_op1 unary_op_not
  (expr_op2 binary_op_stx_eq
   (expr_get_obj_attr oattr_class (expr_id "context"))
   (expr_string "DeclEnvRec")))
 (expr_fail "[env] %EnvDefineArgsObj needs a declarative env record")
 expr_undefined)
(expr_if
 (expr_op1 unary_op_not
  (expr_app (expr_id "%EnvHasBinding")
   [expr_id "context"; expr_string "arguments"]))
 (expr_app (expr_id "%EnvDefineArgsObjOk")
  [expr_id "context";
   expr_id "ids";
   expr_id "args";
   expr_id "obj";
   expr_id "strict"]) expr_undefined)
.
Definition ex_privEnvDefineArgsObjOk := 
expr_let "aobj"
(expr_app (expr_id "%mkArgsObj")
 [expr_id "context";
  expr_id "ids";
  expr_id "args";
  expr_id "obj";
  expr_id "strict"])
(expr_if (expr_id "strict")
 (expr_seq
  (expr_app (expr_id "%EnvCreateImmutableBinding")
   [expr_id "context"; expr_string "arguments"])
  (expr_app (expr_id "%EnvInitializeImmutableBinding")
   [expr_id "context"; expr_string "arguments"; expr_id "aobj"]))
 (expr_app (expr_id "%EnvCreateSetMutableBinding")
  [expr_id "context";
   expr_string "arguments";
   expr_id "aobj";
   expr_false;
   expr_false]))
.
Definition ex_privEnvDefineFunc := 
expr_seq
(expr_if
 (expr_op1 unary_op_not
  (expr_app (expr_id "%EnvHasBinding") [expr_id "context"; expr_id "id"]))
 (expr_app (expr_id "%EnvCreateMutableBinding")
  [expr_id "context"; expr_id "id"; expr_id "configurableBindings"])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "context") (expr_id "%globalContext"))
  (expr_if (expr_get_attr pattr_config (expr_id "%global") (expr_id "id"))
   (expr_app (expr_id "%AddDataField")
    [expr_id "%global";
     expr_id "id";
     expr_undefined;
     expr_true;
     expr_true;
     expr_id "configurableBindings"])
   (expr_if
    (expr_if
     (expr_if
      (expr_op2 binary_op_is_accessor (expr_id "%global") (expr_id "id"))
      expr_true
      (expr_op1 unary_op_not
       (expr_get_attr pattr_writable (expr_id "%global") (expr_id "id"))))
     expr_true
     (expr_op1 unary_op_not
      (expr_get_attr pattr_enum (expr_id "%global") (expr_id "id"))))
    (expr_app (expr_id "%TypeError") [expr_string "cannot redefine function"])
    expr_undefined)) expr_undefined))
(expr_app (expr_id "%EnvSetMutableBinding")
 [expr_id "context"; expr_id "id"; expr_id "fo"; expr_id "strict"])
.
Definition ex_privEnvDefineVar := 
expr_seq
(expr_if
 (expr_op1 unary_op_not
  (expr_app (expr_id "%EnvHasBinding") [expr_id "context"; expr_id "id"]))
 (expr_app (expr_id "%EnvCreateSetMutableBinding")
  [expr_id "context";
   expr_id "id";
   expr_undefined;
   expr_id "configurableBindings";
   expr_id "strict"]) expr_undefined) expr_empty
.
Definition ex_privEnvDelete := 
expr_let "f"
(expr_lambda ["context"]
 (expr_seq
  (expr_if (expr_id "strict")
   (expr_app (expr_id "%SyntaxError")
    [expr_string "unqualified name delete in strict mode"]) expr_undefined)
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "context") expr_null)
   expr_true
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_class (expr_id "context"))
     (expr_string "DeclEnvRec"))
    (expr_if (expr_get_attr pattr_config (expr_id "context") (expr_id "id"))
     (expr_seq (expr_delete_field (expr_id "context") (expr_id "id"))
      expr_true) expr_false)
    (expr_if
     (expr_op2 binary_op_stx_eq
      (expr_get_obj_attr oattr_class (expr_id "context"))
      (expr_string "ObjEnvRec"))
     (expr_app (expr_id "%Delete")
      [expr_get_internal "bindings" (expr_id "context");
       expr_id "id";
       expr_false])
     (expr_throw (expr_string "[env] Context not well formed! In %EnvDelete")))))))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvGet := 
expr_let "f"
(expr_lambda ["context"]
 (expr_app (expr_id "%EnvGetValue")
  [expr_id "context"; expr_id "id"; expr_id "strict"]))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvGetBindingValue := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "context") (expr_id "id")) expr_empty)
 (expr_if (expr_id "strict")
  (expr_app (expr_id "%ReferenceError")
   [expr_string "reading an uninitialized binding"]) expr_undefined)
 (expr_get_attr pattr_value (expr_id "context") (expr_id "id")))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "ObjEnvRec"))
 (expr_let "bindings" (expr_get_internal "bindings" (expr_id "context"))
  (expr_if
   (expr_app (expr_id "%HasProperty") [expr_id "bindings"; expr_id "id"])
   (expr_app (expr_id "%Get1") [expr_id "bindings"; expr_id "id"])
   (expr_if (expr_id "strict")
    (expr_app (expr_id "%ReferenceError")
     [expr_string "reading nonexistent binding"]) expr_undefined)))
 (expr_throw
  (expr_string "[env] Context not well formed! In %EnvGetBindingValue")))
.
Definition ex_privEnvGetId := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "context") expr_null)
(expr_app (expr_id "f") [expr_id "context"])
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "DeclEnvRec"))
 (expr_if
  (expr_op2 binary_op_has_own_property (expr_id "context") (expr_id "id"))
  (expr_app (expr_id "f") [expr_id "context"])
  (expr_app (expr_id "%EnvGetId")
   [expr_get_internal "parent" (expr_id "context"); expr_id "id"; expr_id "f"]))
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_obj_attr oattr_class (expr_id "context"))
   (expr_string "ObjEnvRec"))
  (expr_let "bindings" (expr_get_internal "bindings" (expr_id "context"))
   (expr_if
    (expr_app (expr_id "%HasProperty") [expr_id "bindings"; expr_id "id"])
    (expr_app (expr_id "f") [expr_id "context"])
    (expr_app (expr_id "%EnvGetId")
     [expr_get_internal "parent" (expr_id "context");
      expr_id "id";
      expr_id "f"])))
  (expr_throw (expr_string "[env] Context not well formed! In %EnvGetId"))))
.
Definition ex_privEnvGetValue := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "context") expr_null)
(expr_app (expr_id "%UnboundId") [expr_id "id"])
(expr_app (expr_id "%EnvGetBindingValue")
 [expr_id "context"; expr_id "id"; expr_id "strict"])
.
Definition ex_privEnvHasBinding := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_op2 binary_op_has_own_property (expr_id "context") (expr_id "id"))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "ObjEnvRec"))
 (expr_app (expr_id "%HasProperty")
  [expr_get_internal "bindings" (expr_id "context"); expr_id "id"])
 (expr_throw (expr_string "[env] Context not well formed! In %EnvHasBinding")))
.
Definition ex_privEnvImplicitThis := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec")) expr_undefined
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "ObjEnvRec"))
 (expr_if (expr_get_internal "provideThis" (expr_id "context"))
  (expr_get_internal "bindings" (expr_id "context")) expr_undefined)
 (expr_throw
  (expr_string "[env] Context not well formed! In %EnvImplicitThis")))
.
Definition ex_privEnvInitializeImmutableBinding := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_seq
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq
    (expr_get_attr pattr_value (expr_id "context") (expr_id "id")) expr_empty))
  (expr_fail "Not an immutable binding") expr_undefined)
 (expr_seq
  (expr_set_attr pattr_value (expr_id "context") (expr_id "id")
   (expr_id "val"))
  (expr_seq
   (expr_set_attr pattr_writable (expr_id "context") (expr_id "id")
    expr_false) expr_empty)))
(expr_fail "[env] Context not well formed! In %EnvInitializeImmutableBinding")
.
Definition ex_privEnvModify := 
expr_let "f"
(expr_lambda ["context"]
 (expr_let "val"
  (expr_app (expr_id "op")
   [expr_app (expr_id "%EnvGetValue")
    [expr_id "context"; expr_id "id"; expr_id "strict"];
    expr_app (expr_id "val_thunk") []])
  (expr_seq
   (expr_app (expr_id "%EnvPutValue")
    [expr_id "context"; expr_id "id"; expr_id "val"; expr_id "strict"])
   (expr_id "val"))))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvPrepostOp := 
expr_let "f"
(expr_lambda ["context"]
 (expr_let "oldValue"
  (expr_app (expr_id "%ToNumber")
   [expr_app (expr_id "%EnvGetValue")
    [expr_id "context"; expr_id "id"; expr_id "strict"]])
  (expr_let "newValue"
   (expr_app (expr_id "op")
    [expr_id "oldValue"; expr_number (JsNumber.of_int (1))])
   (expr_seq
    (expr_app (expr_id "%EnvPutValue")
     [expr_id "context"; expr_id "id"; expr_id "newValue"; expr_id "strict"])
    (expr_if (expr_id "is_pre") (expr_id "newValue") (expr_id "oldValue"))))))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEnvPutValue := 
expr_if (expr_op2 binary_op_stx_eq (expr_id "context") expr_null)
(expr_if (expr_id "strict") (expr_app (expr_id "%UnboundId") [expr_id "id"])
 (expr_set_attr pattr_value (expr_id "%global") (expr_id "id")
  (expr_id "val")))
(expr_app (expr_id "%EnvSetMutableBinding")
 [expr_id "context"; expr_id "id"; expr_id "val"; expr_id "strict"])
.
Definition ex_privEnvSetMutableBinding := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_obj_attr oattr_class (expr_id "context"))
 (expr_string "DeclEnvRec"))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "context") (expr_id "id")) expr_empty)
 (expr_if (expr_id "strict")
  (expr_app (expr_id "%TypeError")
   [expr_op2 binary_op_string_plus (expr_id "id")
    (expr_string " is (uninitialized) read-only")]) expr_empty)
 (expr_if (expr_get_attr pattr_writable (expr_id "context") (expr_id "id"))
  (expr_seq
   (expr_set_attr pattr_value (expr_id "context") (expr_id "id")
    (expr_id "val")) expr_empty)
  (expr_if (expr_id "strict")
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus (expr_id "id")
     (expr_string " is read-only")]) expr_empty)))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_obj_attr oattr_class (expr_id "context"))
  (expr_string "ObjEnvRec"))
 (expr_app (expr_id "%Put1")
  [expr_get_internal "bindings" (expr_id "context");
   expr_id "id";
   expr_id "val";
   expr_id "strict"])
 (expr_throw
  (expr_string "[env] Context not well formed! In %EnvSetMutableBinding")))
.
Definition ex_privEnvTypeof := 
expr_let "f"
(expr_lambda ["context"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "context") expr_null)
  (expr_string "undefined")
  (expr_app (expr_id "%Typeof")
   [expr_app (expr_id "%EnvGetBindingValue")
    [expr_id "context"; expr_id "id"; expr_id "strict"]])))
(expr_app (expr_id "%EnvGetId")
 [expr_id "context"; expr_id "id"; expr_id "f"])
.
Definition ex_privEqEq := 
expr_let "t1" (expr_op1 unary_op_typeof (expr_id "x1"))
(expr_let "t2" (expr_op1 unary_op_typeof (expr_id "x2"))
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_id "t2"))
  (expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2"))
  (expr_if
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "undefined"))
     (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "null"))
     expr_false) expr_true
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "null"))
     (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "undefined"))
     expr_false)) expr_true
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "number"))
     (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "string"))
     expr_false)
    (expr_op2 binary_op_stx_eq (expr_id "x1")
     (expr_op1 unary_op_prim_to_num (expr_id "x2")))
    (expr_if
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "string"))
      (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "number"))
      expr_false)
     (expr_op2 binary_op_stx_eq
      (expr_op1 unary_op_prim_to_num (expr_id "x1")) (expr_id "x2"))
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "boolean"))
      (expr_app (expr_id "%EqEq")
       [expr_op1 unary_op_prim_to_num (expr_id "x1"); expr_id "x2"])
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "boolean"))
       (expr_app (expr_id "%EqEq")
        [expr_id "x1"; expr_op1 unary_op_prim_to_num (expr_id "x2")])
       (expr_if
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "string"))
          expr_true
          (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "number")))
         (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "object"))
         expr_false)
        (expr_app (expr_id "%EqEq")
         [expr_id "x1"; expr_app (expr_id "%ToPrimitive") [expr_id "x2"]])
        (expr_if
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "string"))
           expr_true
           (expr_op2 binary_op_stx_eq (expr_id "t2") (expr_string "number")))
          (expr_op2 binary_op_stx_eq (expr_id "t1") (expr_string "object"))
          expr_false)
         (expr_app (expr_id "%EqEq")
          [expr_app (expr_id "%ToPrimitive") [expr_id "x1"]; expr_id "x2"])
         expr_false)))))))))
.
Definition ex_privErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privEvalErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privFunctionConstructor := 
expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_recc "formArgString"
 (expr_lambda ["n"; "result"]
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "n")
    (expr_op2 binary_op_sub (expr_id "argCount")
     (expr_number (JsNumber.of_int (1))))) (expr_id "result")
   (expr_let "currentArg"
    (expr_app (expr_id "%ToString")
     [expr_get_attr pattr_value (expr_id "args")
      (expr_op1 unary_op_prim_to_str (expr_id "n"))])
    (expr_let "next"
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_op2 binary_op_sub (expr_id "argCount")
        (expr_number (JsNumber.of_int (2)))))
      (expr_op2 binary_op_string_plus (expr_id "result")
       (expr_id "currentArg"))
      (expr_op2 binary_op_string_plus
       (expr_op2 binary_op_string_plus (expr_id "result")
        (expr_id "currentArg")) (expr_string ",")))
     (expr_app (expr_id "formArgString")
      [expr_op2 binary_op_add (expr_id "n")
       (expr_number (JsNumber.of_int (1)));
       expr_id "next"])))))
 (expr_let "body"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "argCount")
    (expr_number (JsNumber.of_int (0)))) (expr_string "")
   (expr_get_attr pattr_value (expr_id "args")
    (expr_op1 unary_op_prim_to_str
     (expr_op2 binary_op_sub (expr_id "argCount")
      (expr_number (JsNumber.of_int (1)))))))
  (expr_let "P"
   (expr_if
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "argCount")
      (expr_number (JsNumber.of_int (0)))) expr_true
     (expr_op2 binary_op_stx_eq (expr_id "argCount")
      (expr_number (JsNumber.of_int (1))))) (expr_string "")
    (expr_app (expr_id "formArgString")
     [expr_number (JsNumber.of_int (0)); expr_string ""]))
   (expr_let "prefix"
    (expr_op2 binary_op_string_plus
     (expr_string "((function(){ return function (")
     (expr_op2 binary_op_string_plus (expr_id "P") (expr_string "){")))
    (expr_let "final"
     (expr_op2 binary_op_string_plus (expr_id "prefix")
      (expr_op2 binary_op_string_plus (expr_id "body")
       (expr_string "}; })());")))
     (expr_app (expr_id "%evalCall")
      [expr_undefined;
       expr_object
       (objattrs_intro (expr_string "Object") expr_true expr_null
        expr_undefined) []
       [("0", property_data
              (data_intro (expr_id "final") expr_false expr_false expr_false))]]))))))
.
Definition ex_privFunctionProtoCall :=  expr_undefined .
Definition ex_privGeOp := 
expr_app (expr_id "%CompareOp")
[expr_id "l"; expr_id "r"; expr_false; expr_true]
.
Definition ex_privGet := 
expr_app (expr_id "%GetProperty")
[expr_id "obj";
 expr_id "fld";
 expr_lambda ["v"; "w"; "e"; "c"] (expr_id "v");
 expr_lambda ["g"; "s"; "e"; "c"]
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "g") expr_undefined)
  expr_undefined
  (expr_app (expr_id "%AppExpr")
   [expr_id "g"; expr_id "this"; expr_app (expr_id "%zeroArgObj") []]));
 expr_lambda [] expr_undefined]
.
Definition ex_privGet1 := 
expr_app (expr_id "%Get") [expr_id "obj"; expr_id "obj"; expr_id "fld"]
.
Definition ex_privGetField := 
expr_if
(expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "v"))
 (expr_string "object"))
(expr_app (expr_id "%Get1") [expr_id "v"; expr_id "fld"])
(expr_app (expr_id "%GetPrim") [expr_id "v"; expr_id "fld"])
.
Definition ex_privGetOp := 
expr_app (expr_id "%GetField") [expr_id "v"; expr_id "fld"]
.
Definition ex_privGetOwnProperty := 
expr_if (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "id"))
(expr_if (expr_op2 binary_op_is_accessor (expr_id "obj") (expr_id "id"))
 (expr_app (expr_id "f_acc")
  [expr_get_attr pattr_getter (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_setter (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_enum (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_config (expr_id "obj") (expr_id "id")])
 (expr_app (expr_id "f_data")
  [expr_get_attr pattr_value (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_writable (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_enum (expr_id "obj") (expr_id "id");
   expr_get_attr pattr_config (expr_id "obj") (expr_id "id")]))
(expr_app (expr_id "f_undef") [])
.
Definition ex_privGetPrim := 
expr_app (expr_id "%Get")
[expr_app (expr_id "%ToObject") [expr_id "obj"]; expr_id "obj"; expr_id "fld"]
.
Definition ex_privGetProperty := 
expr_app (expr_id "%GetOwnProperty")
[expr_id "obj";
 expr_id "id";
 expr_id "f_data";
 expr_id "f_acc";
 expr_lambda []
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_proto (expr_id "obj"))
   expr_null) (expr_app (expr_id "f_undef") [])
  (expr_app (expr_id "%GetProperty")
   [expr_get_obj_attr oattr_proto (expr_id "obj");
    expr_id "id";
    expr_id "f_data";
    expr_id "f_acc";
    expr_id "f_undef"]))]
.
Definition ex_privGtOp := 
expr_app (expr_id "%CompareOp")
[expr_id "l"; expr_id "r"; expr_true; expr_false]
.
Definition ex_privHasProperty := 
expr_if (expr_op2 binary_op_has_own_property (expr_id "obj") (expr_id "id"))
expr_true
(expr_if
 (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_proto (expr_id "obj"))
  expr_null) expr_false
 (expr_app (expr_id "%HasProperty")
  [expr_get_obj_attr oattr_proto (expr_id "obj"); expr_id "id"]))
.
Definition ex_privInLeapYear := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "%DaysInYear")
  [expr_app (expr_id "%YearFromTime") [expr_id "t"]])
 (expr_number (JsNumber.of_int (365)))) (expr_number (JsNumber.of_int (0)))
(expr_number (JsNumber.of_int (1)))
.
Definition ex_privIsCallable := 
expr_op2 binary_op_stx_eq (expr_app (expr_id "%Typeof") [expr_id "o"])
(expr_string "function")
.
Definition ex_privIsFinite := 
expr_op1 unary_op_not
(expr_if
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n"))) expr_true
  (expr_op2 binary_op_stx_eq (expr_id "n") (expr_number JsNumber.infinity)))
 expr_true
 (expr_op2 binary_op_stx_eq (expr_id "n") (expr_number JsNumber.neg_infinity)))
.
Definition ex_privIsJSError := 
expr_if (expr_op1 unary_op_is_object (expr_id "thing"))
(expr_op2 binary_op_has_own_property (expr_id "thing")
 (expr_string "%js-exn")) expr_false
.
Definition ex_privJSError := 
expr_object
(objattrs_intro (expr_string "JSError") expr_false expr_null expr_undefined)
[]
[("%js-exn", property_data
             (data_intro (expr_id "err") expr_false expr_false expr_false))]
.
Definition ex_privLeOp := 
expr_app (expr_id "%CompareOp")
[expr_id "l"; expr_id "r"; expr_true; expr_true]
.
Definition ex_privLeftShift := 
expr_op2 binary_op_shiftl (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privLocalTime :=  expr_id "t" .
Definition ex_privLtOp := 
expr_app (expr_id "%CompareOp")
[expr_id "l"; expr_id "r"; expr_false; expr_false]
.
Definition ex_privMakeArray := 
expr_object
(objattrs_intro (expr_string "Array") expr_true (expr_id "%ArrayProto")
 expr_undefined) []
[("length", property_data
            (data_intro (expr_id "len") expr_true expr_false expr_false))]
.
Definition ex_privMakeBind := 
expr_let "len"
(expr_if
 (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_class (expr_id "obj"))
  (expr_string "Function"))
 (expr_let "L"
  (expr_op2 binary_op_sub
   (expr_get_attr pattr_value (expr_id "obj") (expr_string "length"))
   (expr_get_attr pattr_value (expr_id "args") (expr_string "length")))
  (expr_app (expr_id "%max") [expr_number (JsNumber.of_int (0)); expr_id "L"]))
 (expr_number (JsNumber.of_int (0))))
(expr_object
 (objattrs_intro (expr_string "Function") expr_true
  (expr_id "%FunctionProto") (expr_id "%BindObjCall"))
 [("construct", expr_id "%BindConstructor");
  ("target", expr_id "obj");
  ("boundThis", expr_id "this");
  ("boundArgs", expr_id "args")]
 [("caller", property_accessor
             (accessor_intro (expr_id "%ThrowTypeError")
              (expr_id "%ThrowTypeError") expr_false expr_false));
  ("arguments", property_accessor
                (accessor_intro (expr_id "%ThrowTypeError")
                 (expr_id "%ThrowTypeError") expr_false expr_false));
  ("length", property_data
             (data_intro (expr_id "len") expr_false expr_false expr_false))])
.
Definition ex_privMakeBoolean := 
expr_object
(objattrs_intro (expr_string "Boolean") expr_true (expr_id "%BooleanProto")
 expr_undefined) [("primval", expr_id "v")] []
.
Definition ex_privMakeDate := 
expr_object
(objattrs_intro (expr_string "Date") expr_true (expr_id "%DateProto")
 expr_undefined) [("primval", expr_id "v")] []
.
Definition ex_privMakeDateDayTime := 
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
(expr_number JsNumber.nan)
(expr_let "y" (expr_app (expr_id "%ToInteger") [expr_id "yr"])
 (expr_let "m" (expr_app (expr_id "%ToInteger") [expr_id "mt"])
  (expr_let "dt" (expr_app (expr_id "%ToInteger") [expr_id "date"])
   (expr_let "ym"
    (expr_op2 binary_op_add (expr_id "y")
     (expr_op1 unary_op_floor
      (expr_op2 binary_op_div (expr_id "m")
       (expr_number (JsNumber.of_int (12))))))
    (expr_let "mn"
     (expr_op2 binary_op_mod (expr_id "m")
      (expr_number (JsNumber.of_int (12))))
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
             (expr_number (JsNumber.of_int (1)));
             expr_id "leap"]))) (expr_id "t")))
       (expr_let "t"
        (expr_app (expr_id "loop")
         [expr_id "yt";
          expr_number (JsNumber.of_int (0));
          expr_app (expr_id "%InLeapYear") [expr_id "yt"]])
        (expr_if
         (expr_if
          (expr_if
           (expr_op1 unary_op_not
            (expr_op2 binary_op_stx_eq
             (expr_app (expr_id "%YearFromTime") [expr_id "t"])
             (expr_id "ym"))) expr_true
           (expr_op1 unary_op_not
            (expr_op2 binary_op_stx_eq
             (expr_app (expr_id "%MonthFromTime") [expr_id "t"])
             (expr_id "mn")))) expr_true
          (expr_op1 unary_op_not
           (expr_op2 binary_op_stx_eq
            (expr_app (expr_id "%DateFromTime") [expr_id "t"])
            (expr_number (JsNumber.of_int (1)))))) (expr_number JsNumber.nan)
         (expr_op2 binary_op_sub
          (expr_op2 binary_op_add (expr_app (expr_id "%Day") [expr_id "t"])
           (expr_id "dt")) (expr_number (JsNumber.of_int (1)))))))))))))
.
Definition ex_privMakeFunctionObject := 
expr_let "fobj"
(expr_object
 (objattrs_intro (expr_string "Function") expr_true
  (expr_id "%FunctionProto") (expr_id "%DefaultCall"))
 [("construct", expr_id "%DefaultConstruct");
  ("usercode", expr_id "body");
  ("codetxt", expr_id "codetxt");
  ("strict", expr_id "strict")]
 [("length", property_data
             (data_intro (expr_id "len") expr_false expr_false expr_false))])
(expr_let "proto"
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true (expr_id "%ObjectProto")
   expr_undefined) []
  [("constructor", property_data
                   (data_intro (expr_id "fobj") expr_true expr_false
                    expr_true))])
 (expr_seq
  (expr_app (expr_id "%AddDataField")
   [expr_id "fobj";
    expr_string "prototype";
    expr_id "proto";
    expr_true;
    expr_false;
    expr_false])
  (expr_seq
   (expr_if (expr_id "strict")
    (expr_seq
     (expr_app (expr_id "%AddAccessorField")
      [expr_id "fobj";
       expr_string "caller";
       expr_id "%ThrowTypeError";
       expr_id "%ThrowTypeError";
       expr_false;
       expr_false])
     (expr_app (expr_id "%AddAccessorField")
      [expr_id "fobj";
       expr_string "arguments";
       expr_id "%ThrowTypeError";
       expr_id "%ThrowTypeError";
       expr_false;
       expr_false])) expr_undefined) (expr_id "fobj"))))
.
Definition ex_privMakeNativeError := 
expr_let "exc"
(expr_object
 (objattrs_intro (expr_string "Error") expr_true (expr_id "proto")
  expr_undefined) [] [])
(expr_seq
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq (expr_id "msg") expr_undefined))
  (expr_seq
   (expr_set_attr pattr_value (expr_id "exc") (expr_string "message")
    (expr_id "msg"))
   (expr_set_attr pattr_enum (expr_id "exc") (expr_string "message")
    expr_false)) expr_undefined) (expr_id "exc"))
.
Definition ex_privMakeNativeErrorProto := 
expr_object
(objattrs_intro (expr_string "Error") expr_true (expr_id "%ErrorProto")
 expr_undefined) []
[("name", property_data
          (data_intro (expr_id "name") expr_true expr_false expr_true));
 ("message", property_data
             (data_intro (expr_string "") expr_true expr_false expr_true))]
.
Definition ex_privMakeNumber := 
expr_object
(objattrs_intro (expr_string "Number") expr_true (expr_id "%NumberProto")
 expr_undefined) [("primval", expr_id "v")] []
.
Definition ex_privMakeObject := 
expr_object
(objattrs_intro (expr_string "Object") expr_true (expr_id "%ObjectProto")
 expr_undefined) [] []
.
Definition ex_privMakeString := 
expr_let "obj"
(expr_object
 (objattrs_intro (expr_string "String") expr_true (expr_id "%StringProto")
  expr_undefined) [("primval", expr_id "v")]
 [("length", property_data
             (data_intro (expr_op1 unary_op_strlen (expr_id "v")) expr_true
              expr_false expr_false))])
(expr_seq (expr_app (expr_id "%StringIndices") [expr_id "obj"; expr_id "v"])
 (expr_id "obj"))
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
(expr_number JsNumber.nan)
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
   (expr_op2 binary_op_le (expr_number (JsNumber.of_int (0)))
    (expr_app (expr_id "%DayWithinYear") [expr_id "t"]))
   (expr_op2 binary_op_lt (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
    (expr_number (JsNumber.of_int (31)))) expr_false)
  (expr_number (JsNumber.of_int (0)))
  (expr_if
   (expr_if
    (expr_op2 binary_op_le (expr_number (JsNumber.of_int (31)))
     (expr_app (expr_id "%DayWithinYear") [expr_id "t"]))
    (expr_op2 binary_op_lt
     (expr_app (expr_id "%DayWithinYear") [expr_id "t"])
     (expr_op2 binary_op_add (expr_number (JsNumber.of_int (59)))
      (expr_app (expr_id "%InLeapYear") [expr_id "t"]))) expr_false)
   (expr_number (JsNumber.of_int (1)))
   (expr_if
    (expr_app (expr_id "CheckLeapRange")
     [expr_number (JsNumber.of_int (59)); expr_number (JsNumber.of_int (90))])
    (expr_number (JsNumber.of_int (2)))
    (expr_if
     (expr_app (expr_id "CheckLeapRange")
      [expr_number (JsNumber.of_int (90));
       expr_number (JsNumber.of_int (120))])
     (expr_number (JsNumber.of_int (3)))
     (expr_if
      (expr_app (expr_id "CheckLeapRange")
       [expr_number (JsNumber.of_int (120));
        expr_number (JsNumber.of_int (151))])
      (expr_number (JsNumber.of_int (4)))
      (expr_if
       (expr_app (expr_id "CheckLeapRange")
        [expr_number (JsNumber.of_int (151));
         expr_number (JsNumber.of_int (181))])
       (expr_number (JsNumber.of_int (5)))
       (expr_if
        (expr_app (expr_id "CheckLeapRange")
         [expr_number (JsNumber.of_int (181));
          expr_number (JsNumber.of_int (212))])
        (expr_number (JsNumber.of_int (6)))
        (expr_if
         (expr_app (expr_id "CheckLeapRange")
          [expr_number (JsNumber.of_int (212));
           expr_number (JsNumber.of_int (243))])
         (expr_number (JsNumber.of_int (7)))
         (expr_if
          (expr_app (expr_id "CheckLeapRange")
           [expr_number (JsNumber.of_int (243));
            expr_number (JsNumber.of_int (273))])
          (expr_number (JsNumber.of_int (8)))
          (expr_if
           (expr_app (expr_id "CheckLeapRange")
            [expr_number (JsNumber.of_int (273));
             expr_number (JsNumber.of_int (304))])
           (expr_number (JsNumber.of_int (9)))
           (expr_if
            (expr_app (expr_id "CheckLeapRange")
             [expr_number (JsNumber.of_int (304));
              expr_number (JsNumber.of_int (334))])
            (expr_number (JsNumber.of_int (10)))
            (expr_if
             (expr_app (expr_id "CheckLeapRange")
              [expr_number (JsNumber.of_int (334));
               expr_number (JsNumber.of_int (365))])
             (expr_number (JsNumber.of_int (11)))
             (expr_app (expr_id "%TypeError")
              [expr_string "Something terrible in date %MonthFromTime"]))))))))))))))
.
Definition ex_privNativeError := 
expr_throw
(expr_app (expr_id "%JSError")
 [expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"]])
.
Definition ex_privNativeErrorConstructor := 
expr_lambda ["this"; "args"]
(expr_let "msg"
 (expr_if
  (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  expr_undefined)
 (expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"]))
.
Definition ex_privNumberCall := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_app (expr_id "%ComputeLength") [expr_id "args"])
 (expr_number (JsNumber.of_int (0)))) (expr_number (JsNumber.of_int (0)))
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
.
Definition ex_privNumberCompareOp := 
expr_if
(expr_if
 (expr_op2 binary_op_same_value (expr_id "l") (expr_number JsNumber.nan))
 expr_true
 (expr_op2 binary_op_same_value (expr_id "r") (expr_number JsNumber.nan)))
expr_undefined
(expr_if (expr_op2 binary_op_same_value (expr_id "l") (expr_id "r"))
 expr_false
 (expr_if
  (expr_if
   (expr_op2 binary_op_same_value (expr_id "l")
    (expr_number (JsNumber.of_int (0))))
   (expr_op2 binary_op_same_value (expr_id "r")
    (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (0))))) expr_false)
  expr_false
  (expr_if
   (expr_if
    (expr_op2 binary_op_same_value (expr_id "l")
     (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (0)))))
    (expr_op2 binary_op_same_value (expr_id "r")
     (expr_number (JsNumber.of_int (0)))) expr_false) expr_false
   (expr_if
    (expr_op2 binary_op_same_value (expr_id "l")
     (expr_number JsNumber.infinity)) expr_false
    (expr_if
     (expr_op2 binary_op_same_value (expr_id "r")
      (expr_number JsNumber.infinity)) expr_true
     (expr_if
      (expr_op2 binary_op_same_value (expr_id "r")
       (expr_number JsNumber.neg_infinity)) expr_false
      (expr_if
       (expr_op2 binary_op_same_value (expr_id "l")
        (expr_number JsNumber.neg_infinity)) expr_true
       (expr_op2 binary_op_lt (expr_id "l") (expr_id "r")))))))))
.
Definition ex_privNumberConstructor := 
expr_app (expr_id "%MakeNumber")
[expr_if
 (expr_op2 binary_op_stx_eq
  (expr_app (expr_id "%ComputeLength") [expr_id "args"])
  (expr_number (JsNumber.of_int (0)))) (expr_number (JsNumber.of_int (0)))
 (expr_app (expr_id "%ToNumber")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])]
.
Definition ex_privObjectCall := 
expr_if
(expr_if
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "%ComputeLength") [expr_id "args"])
   (expr_number (JsNumber.of_int (0)))) expr_true
  (expr_op2 binary_op_stx_eq
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0")) expr_null))
 expr_true
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
  expr_undefined)) (expr_app (expr_id "%MakeObject") [])
(expr_app (expr_id "%ToObject")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
.
Definition ex_privObjectConstructor := 
expr_app (expr_id "%ObjectCall")
[expr_id "constr"; expr_undefined; expr_id "args"]
.
Definition ex_privObjectTypeCheck := 
expr_if (expr_op1 unary_op_is_object (expr_id "o")) expr_empty
(expr_app (expr_id "%TypeError")
 [expr_op2 binary_op_string_plus
  (expr_op1 unary_op_prim_to_str (expr_id "o"))
  (expr_string " is not an object")])
.
Definition ex_privPrepostOp := 
expr_let "oldValue"
(expr_app (expr_id "%ToNumber")
 [expr_app (expr_id "%GetField") [expr_id "obj"; expr_id "fld"]])
(expr_let "newValue"
 (expr_app (expr_id "op")
  [expr_id "oldValue"; expr_number (JsNumber.of_int (1))])
 (expr_seq
  (expr_app (expr_id "%SetField")
   [expr_id "obj"; expr_id "fld"; expr_id "newValue"])
  (expr_if (expr_id "is_pre") (expr_id "newValue") (expr_id "oldValue"))))
.
Definition ex_privPrimAdd := 
expr_let "l" (expr_app (expr_id "%ToPrimitive") [expr_id "l"])
(expr_let "r" (expr_app (expr_id "%ToPrimitive") [expr_id "r"])
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "l"))
   (expr_string "string"))
  (expr_op2 binary_op_string_plus
   (expr_op1 unary_op_prim_to_str (expr_id "l"))
   (expr_op1 unary_op_prim_to_str (expr_id "r")))
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "r"))
    (expr_string "string"))
   (expr_op2 binary_op_string_plus
    (expr_op1 unary_op_prim_to_str (expr_id "l"))
    (expr_op1 unary_op_prim_to_str (expr_id "r")))
   (expr_op2 binary_op_add (expr_op1 unary_op_prim_to_num (expr_id "l"))
    (expr_op1 unary_op_prim_to_num (expr_id "r"))))))
.
Definition ex_privPrimComma :=  expr_id "r" .
Definition ex_privPrimDiv := 
expr_app (expr_id "%PrimMultOp")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_div (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privPrimMod := 
expr_app (expr_id "%PrimMultOp")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_mod (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privPrimMult := 
expr_app (expr_id "%PrimMultOp")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_mul (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privPrimMultOp := 
expr_app (expr_id "op")
[expr_app (expr_id "%ToNumber") [expr_id "l"];
 expr_app (expr_id "%ToNumber") [expr_id "r"]]
.
Definition ex_privPrimNew := 
expr_if
(expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "constr")))
(expr_app (expr_id "%TypeError") [expr_string "not a constructor"])
(expr_if
 (expr_op1 unary_op_not
  (expr_op2 binary_op_has_internal (expr_id "constr")
   (expr_string "construct")))
 (expr_app (expr_id "%TypeError") [expr_string "not a constructor"])
 (expr_app (expr_id "%runConstruct") [expr_id "constr"; expr_id "args"]))
.
Definition ex_privPrimSub := 
expr_app (expr_id "%PrimMultOp")
[expr_id "l";
 expr_id "r";
 expr_lambda ["x1"; "x2"]
 (expr_op2 binary_op_sub (expr_id "x1") (expr_id "x2"))]
.
Definition ex_privPrimitiveCompareOp := 
expr_if
(expr_if
 (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "l"))
  (expr_string "string"))
 (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "r"))
  (expr_string "string")) expr_false)
(expr_op2 binary_op_string_lt (expr_id "l") (expr_id "r"))
(expr_app (expr_id "%NumberCompareOp")
 [expr_op1 unary_op_prim_to_num (expr_id "l");
  expr_op1 unary_op_prim_to_num (expr_id "r")])
.
Definition ex_privPropertyAccess := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "o"])
(expr_app (expr_id "cont")
 [expr_id "o";
  expr_app (expr_id "%ToString") [expr_id "fld"];
  expr_id "strict"])
.
Definition ex_privPut := 
expr_let "optTypeError"
(expr_lambda ["msg"]
 (expr_if (expr_id "strict")
  (expr_app (expr_id "%TypeError") [expr_id "msg"]) expr_empty))
(expr_app (expr_id "%GetOwnProperty")
 [expr_id "obj";
  expr_id "fld";
  expr_lambda ["v"; "w"; "e"; "c"]
  (expr_if (expr_id "w")
   (expr_seq
    (expr_set_attr pattr_value (expr_id "obj") (expr_id "fld")
     (expr_id "val")) expr_empty)
   (expr_app (expr_id "optTypeError")
    [expr_string "setting unwritable field"]));
  expr_lambda ["g"; "s"; "e"; "c"]
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "s") expr_undefined)
   (expr_app (expr_id "optTypeError")
    [expr_string "setting accessor field with no setter"])
   (expr_seq
    (expr_app (expr_id "%AppExpr")
     [expr_id "s";
      expr_id "this";
      expr_app (expr_id "%oneArgObj") [expr_id "val"]]) expr_empty));
  expr_lambda []
  (expr_app (expr_id "%GetProperty")
   [expr_id "obj";
    expr_id "fld";
    expr_lambda ["v"; "w"; "e"; "c"]
    (expr_if (expr_get_obj_attr oattr_extensible (expr_id "obj"))
     (expr_if (expr_id "w")
      (expr_seq
       (expr_app (expr_id "%AddDataField")
        [expr_id "obj";
         expr_id "fld";
         expr_id "val";
         expr_true;
         expr_true;
         expr_true]) expr_empty)
      (expr_app (expr_id "optTypeError")
       [expr_string "shadowing unwritable field"]))
     (expr_app (expr_id "optTypeError")
      [expr_string "adding a field to a non-extensible object"]));
    expr_lambda ["g"; "s"; "e"; "c"]
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "s") expr_undefined)
     (expr_app (expr_id "optTypeError")
      [expr_string "setting accessor field with no setter"])
     (expr_seq
      (expr_app (expr_id "%AppExpr")
       [expr_id "s";
        expr_id "this";
        expr_app (expr_id "%oneArgObj") [expr_id "val"]]) expr_empty));
    expr_lambda []
    (expr_if (expr_get_obj_attr oattr_extensible (expr_id "obj"))
     (expr_seq
      (expr_app (expr_id "%AddDataField")
       [expr_id "obj";
        expr_id "fld";
        expr_id "val";
        expr_true;
        expr_true;
        expr_true]) expr_empty)
     (expr_app (expr_id "optTypeError")
      [expr_string "adding a field to a non-extensible object"]))])])
.
Definition ex_privPut1 := 
expr_app (expr_id "%Put")
[expr_id "obj"; expr_id "obj"; expr_id "fld"; expr_id "val"; expr_id "strict"]
.
Definition ex_privPutPrim := 
expr_app (expr_id "%Put")
[expr_app (expr_id "%ToObject") [expr_id "v"];
 expr_id "v";
 expr_id "fld";
 expr_id "val";
 expr_id "strict"]
.
Definition ex_privRangeError := 
expr_app (expr_id "%NativeError") [expr_id "%RangeErrorProto"; expr_id "msg"]
.
Definition ex_privRangeErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privReferenceError := 
expr_app (expr_id "%NativeError")
[expr_id "%ReferenceErrorProto"; expr_id "msg"]
.
Definition ex_privReferenceErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privRegExpCode := 
expr_app (expr_id "%RegExpConstructor") [expr_id "obj"; expr_id "args"]
.
Definition ex_privRegExpConstructor := 
expr_object
(objattrs_intro (expr_string "Object") expr_true (expr_id "%RegExpProto")
 expr_undefined) [] []
.
Definition ex_privRunSelfConstructorCall := 
expr_app (expr_get_internal "construct" (expr_id "obj"))
[expr_id "this"; expr_id "args"]
.
Definition ex_privSetField := 
expr_if
(expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "v"))
 (expr_string "object"))
(expr_seq
 (expr_app (expr_id "%Put1")
  [expr_id "v"; expr_id "fld"; expr_id "val"; expr_id "strict"])
 (expr_id "val"))
(expr_seq
 (expr_app (expr_id "%PutPrim")
  [expr_id "v"; expr_id "fld"; expr_id "val"; expr_id "strict"])
 (expr_id "val"))
.
Definition ex_privSetOp := 
expr_lambda ["v"; "fld"; "strict"]
(expr_let "val" (expr_app (expr_id "cval") [])
 (expr_app (expr_id "%SetField")
  [expr_id "v"; expr_id "fld"; expr_id "val"; expr_id "strict"]))
.
Definition ex_privSignedRightShift := 
expr_op2 binary_op_shiftr (expr_app (expr_id "%ToInt32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privStringCall := 
expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
(expr_if
 (expr_op2 binary_op_stx_eq (expr_id "argCount")
  (expr_number (JsNumber.of_int (0)))) (expr_string "")
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]))
.
Definition ex_privStringConstructor := 
expr_app (expr_id "%MakeString")
[expr_app (expr_id "%StringCall")
 [expr_undefined; expr_undefined; expr_id "args"]]
.
Definition ex_privStringIndices := 
expr_let "len" (expr_op1 unary_op_strlen (expr_id "s"))
(expr_recc "loop"
 (expr_lambda ["i"]
  (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
   (expr_seq
    (expr_set_attr pattr_value (expr_id "obj")
     (expr_op1 unary_op_prim_to_str (expr_id "i"))
     (expr_op2 binary_op_char_at (expr_id "s") (expr_id "i")))
    (expr_app (expr_id "loop")
     [expr_op2 binary_op_add (expr_id "i")
      (expr_number (JsNumber.of_int (1)))])) expr_undefined))
 (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))]))
.
Definition ex_privStxEq := 
expr_op2 binary_op_stx_eq (expr_id "x1") (expr_id "x2")
.
Definition ex_privSyntaxError := 
expr_app (expr_id "%NativeError")
[expr_id "%SyntaxErrorProto"; expr_id "msg"]
.
Definition ex_privSyntaxErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privThrowTypeErrorFun := 
expr_let "msg" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_app (expr_id "%TypeError") [expr_id "msg"])
.
Definition ex_privTimeClip := 
expr_if
(expr_op1 unary_op_not
 (expr_if (expr_app (expr_id "%IsFinite") [expr_id "t"])
  (expr_op2 binary_op_le (expr_op1 unary_op_abs (expr_id "t"))
   (expr_number (JsNumber.of_int (8640000000000000)))) expr_false))
(expr_number JsNumber.nan) (expr_app (expr_id "%ToInteger") [expr_id "t"])
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
  (expr_number (JsNumber.of_int (2147483648))))
 (expr_op2 binary_op_sub (expr_id "int32bit")
  (expr_number (JsNumber.of_int (4294967296)))) (expr_id "int32bit"))
.
Definition ex_privToInteger := 
expr_let "num" (expr_app (expr_id "%ToNumber") [expr_id "i"])
(expr_if
 (expr_op2 binary_op_same_value (expr_id "num") (expr_number JsNumber.nan))
 (expr_number (JsNumber.of_int (0)))
 (expr_if
  (expr_if
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "num")
     (expr_number (JsNumber.of_int (0)))) expr_true
    (expr_op2 binary_op_stx_eq (expr_id "num")
     (expr_number JsNumber.infinity))) expr_true
   (expr_op2 binary_op_stx_eq (expr_id "num")
    (expr_number JsNumber.neg_infinity))) (expr_id "num")
  (expr_op2 binary_op_mul (expr_op1 unary_op_sign (expr_id "num"))
   (expr_op1 unary_op_floor (expr_op1 unary_op_abs (expr_id "num"))))))
.
Definition ex_privToNumber := 
expr_op1 unary_op_prim_to_num
(expr_app (expr_id "%ToPrimitiveHint") [expr_id "x"; expr_string "number"])
.
Definition ex_privToObject := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "o"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "null"))
 (expr_app (expr_id "%TypeError") [expr_string "%ToObject received null"])
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "undefined"))
  (expr_app (expr_id "%TypeError")
   [expr_string "%ToObject received undefined"])
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
   (expr_id "o")
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "string"))
    (expr_app (expr_id "%MakeString") [expr_id "o"])
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "number"))
     (expr_app (expr_id "%MakeNumber") [expr_id "o"])
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "boolean"))
      (expr_app (expr_id "%MakeBoolean") [expr_id "o"])
      (expr_throw (expr_string "[env] Invalid type in %ToObject"))))))))
.
Definition ex_privToPrimitive := 
expr_app (expr_id "%ToPrimitiveHint") [expr_id "val"; expr_string "number"]
.
Definition ex_privToPrimitiveHint := 
expr_if (expr_op1 unary_op_is_object (expr_id "val"))
(expr_let "check"
 (expr_lambda ["str"; "next"]
  (expr_lambda []
   (expr_let "f" (expr_app (expr_id "%Get1") [expr_id "val"; expr_id "str"])
    (expr_if (expr_app (expr_id "%IsCallable") [expr_id "f"])
     (expr_let "res"
      (expr_app (expr_id "%AppExpr")
       [expr_id "f"; expr_id "val"; expr_app (expr_id "%zeroArgObj") []])
      (expr_if (expr_op1 unary_op_is_primitive (expr_id "res"))
       (expr_id "res") (expr_app (expr_id "next") [])))
     (expr_app (expr_id "next") [])))))
 (expr_let "met1"
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "hint") (expr_string "string"))
   (expr_string "toString") (expr_string "valueOf"))
  (expr_let "met2"
   (expr_if
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq (expr_id "hint") (expr_string "string")))
    (expr_string "toString") (expr_string "valueOf"))
   (expr_app
    (expr_app (expr_id "check")
     [expr_id "met1";
      expr_app (expr_id "check")
      [expr_id "met2";
       expr_lambda []
       (expr_app (expr_id "%TypeError")
        [expr_string "valueOf and toString both absent in toPrimitive"])]])
    [])))) (expr_id "val")
.
Definition ex_privToPropertyDescriptor := 
expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "propobj"])
(expr_let "attrobj"
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
  [] [])
 (expr_seq
  (expr_if
   (expr_app (expr_id "%HasProperty")
    [expr_id "propobj"; expr_string "enumerable"])
   (expr_set_attr pattr_value (expr_id "attrobj") (expr_string "enumerable")
    (expr_app (expr_id "%ToBoolean")
     [expr_app (expr_id "%Get1")
      [expr_id "propobj"; expr_string "enumerable"]])) expr_undefined)
  (expr_seq
   (expr_if
    (expr_app (expr_id "%HasProperty")
     [expr_id "propobj"; expr_string "configurable"])
    (expr_set_attr pattr_value (expr_id "attrobj")
     (expr_string "configurable")
     (expr_app (expr_id "%ToBoolean")
      [expr_app (expr_id "%Get1")
       [expr_id "propobj"; expr_string "configurable"]])) expr_undefined)
   (expr_seq
    (expr_if
     (expr_app (expr_id "%HasProperty")
      [expr_id "propobj"; expr_string "value"])
     (expr_set_attr pattr_value (expr_id "attrobj") (expr_string "value")
      (expr_app (expr_id "%Get1") [expr_id "propobj"; expr_string "value"]))
     expr_undefined)
    (expr_seq
     (expr_if
      (expr_app (expr_id "%HasProperty")
       [expr_id "propobj"; expr_string "writable"])
      (expr_set_attr pattr_value (expr_id "attrobj") (expr_string "writable")
       (expr_app (expr_id "%ToBoolean")
        [expr_app (expr_id "%Get1")
         [expr_id "propobj"; expr_string "writable"]])) expr_undefined)
     (expr_seq
      (expr_if
       (expr_app (expr_id "%HasProperty")
        [expr_id "propobj"; expr_string "get"])
       (expr_let "get"
        (expr_app (expr_id "%Get1") [expr_id "propobj"; expr_string "get"])
        (expr_if
         (expr_if (expr_app (expr_id "%IsCallable") [expr_id "get"])
          expr_true
          (expr_op2 binary_op_stx_eq (expr_id "get") expr_undefined))
         (expr_set_attr pattr_value (expr_id "propobj") (expr_string "get")
          (expr_id "get"))
         (expr_app (expr_id "%TypeError") [expr_string "non-function getter"])))
       expr_undefined)
      (expr_seq
       (expr_if
        (expr_app (expr_id "%HasProperty")
         [expr_id "propobj"; expr_string "set"])
        (expr_let "set"
         (expr_app (expr_id "%Get1") [expr_id "propobj"; expr_string "set"])
         (expr_if
          (expr_if (expr_app (expr_id "%IsCallable") [expr_id "set"])
           expr_true
           (expr_op2 binary_op_stx_eq (expr_id "set") expr_undefined))
          (expr_set_attr pattr_value (expr_id "propobj") (expr_string "set")
           (expr_id "set"))
          (expr_app (expr_id "%TypeError")
           [expr_string "non-function setter"]))) expr_undefined)
       (expr_seq
        (expr_if
         (expr_if (expr_app (expr_id "isDataDescriptor") [expr_id "attrobj"])
          (expr_app (expr_id "isAccessorDescriptor") [expr_id "attrobj"])
          expr_false)
         (expr_app (expr_id "%TypeError")
          [expr_string
           "The attributes given to defineProperty were inconsistent"])
         expr_undefined) (expr_id "attrobj")))))))))
.
Definition ex_privToString := 
expr_op1 unary_op_prim_to_str
(expr_app (expr_id "%ToPrimitiveHint") [expr_id "val"; expr_string "string"])
.
Definition ex_privToUint := 
expr_let "number" (expr_app (expr_id "%ToNumber") [expr_id "n"])
(expr_if
 (expr_if
  (expr_if
   (expr_if
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq (expr_id "number") (expr_id "number")))
    expr_true
    (expr_op2 binary_op_stx_eq (expr_id "number")
     (expr_number (JsNumber.of_int (0))))) expr_true
   (expr_op2 binary_op_stx_eq (expr_id "number")
    (expr_number JsNumber.infinity))) expr_true
  (expr_op2 binary_op_stx_eq (expr_id "number")
   (expr_number JsNumber.neg_infinity))) (expr_number (JsNumber.of_int (0)))
 (expr_let "sign" (expr_op1 unary_op_sign (expr_id "number"))
  (expr_let "posInt"
   (expr_op2 binary_op_mul (expr_id "sign")
    (expr_op1 unary_op_floor (expr_op1 unary_op_abs (expr_id "number"))))
   (expr_if
    (expr_op2 binary_op_lt (expr_id "sign")
     (expr_number (JsNumber.of_int (0))))
    (expr_let "close"
     (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))
     (expr_op2 binary_op_add (expr_id "close") (expr_id "limit")))
    (expr_op2 binary_op_mod (expr_id "posInt") (expr_id "limit"))))))
.
Definition ex_privToUint16 := 
expr_app (expr_id "%ToUint")
[expr_id "n"; expr_number (JsNumber.of_int (65536))]
.
Definition ex_privToUint32 := 
expr_app (expr_id "%ToUint")
[expr_id "n"; expr_number (JsNumber.of_int (4294967296))]
.
Definition ex_privTypeError := 
expr_app (expr_id "%NativeError") [expr_id "%TypeErrorProto"; expr_id "msg"]
.
Definition ex_privTypeErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privTypeof := 
expr_let "tp" (expr_op1 unary_op_typeof (expr_id "val"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "object"))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_code (expr_id "val"))
   expr_undefined) (expr_string "object") (expr_string "function"))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "undefined"))
  (expr_string "undefined")
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "null"))
   (expr_string "object")
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "boolean"))
    (expr_string "boolean")
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "number"))
     (expr_string "number")
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "tp") (expr_string "string"))
      (expr_string "string")
      (expr_throw (expr_string "[env] invalid value in %Typeof"))))))))
.
Definition ex_privURIErrorConstructor := 
expr_let "msg"
(expr_if
 (expr_op2 binary_op_has_own_property (expr_id "args") (expr_string "0"))
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 expr_undefined)
(expr_app (expr_id "%MakeNativeError") [expr_id "proto"; expr_id "msg"])
.
Definition ex_privUTC :=  expr_id "t" .
Definition ex_privUnaryNeg := 
expr_op1 unary_op_neg (expr_app (expr_id "%ToNumber") [expr_id "expr"])
.
Definition ex_privUnaryNot := 
expr_op1 unary_op_not (expr_app (expr_id "%ToBoolean") [expr_id "expr"])
.
Definition ex_privUnaryPlus := 
expr_app (expr_id "%ToNumber") [expr_id "expr"]
.
Definition ex_privUnboundId := 
expr_app (expr_id "%ReferenceError")
[expr_op2 binary_op_string_plus (expr_string "Unbound identifier: ")
 (expr_id "id")]
.
Definition ex_privUnsignedRightShift := 
expr_op2 binary_op_zfshiftr (expr_app (expr_id "%ToUint32") [expr_id "l"])
(expr_app (expr_id "%ToUint32") [expr_id "r"])
.
Definition ex_privVoid :=  expr_undefined .
Definition ex_privYearFromTime := 
expr_let "sign" (expr_op1 unary_op_sign (expr_id "t"))
(expr_let "start"
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_id "sign")
   (expr_number (JsNumber.of_int (1))))
  (expr_number (JsNumber.of_int (1969)))
  (expr_number (JsNumber.of_int (1970))))
 (expr_recc "loop"
  (expr_lambda ["y"]
   (expr_if
    (expr_if
     (expr_op2 binary_op_le
      (expr_app (expr_id "%TimeFromYear") [expr_id "y"]) (expr_id "t"))
     (expr_op2 binary_op_gt
      (expr_app (expr_id "%TimeFromYear")
       [expr_op2 binary_op_add (expr_number (JsNumber.of_int (1)))
        (expr_id "y")]) (expr_id "t")) expr_false) (expr_id "y")
    (expr_app (expr_id "loop")
     [expr_op2 binary_op_add (expr_id "y") (expr_id "sign")])))
  (expr_app (expr_id "loop") [expr_id "start"])))
.
Definition ex_privacosCall :=  expr_string "acos NYI" .
Definition ex_privapplyCall := 
expr_let "applyArgs1"
(expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
(expr_let "applyArgs"
 (expr_if
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_op1 unary_op_typeof (expr_id "applyArgs1"))
    (expr_string "undefined")) expr_true
   (expr_op2 binary_op_stx_eq (expr_id "applyArgs1") expr_null))
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
   [] []) (expr_id "applyArgs1"))
 (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "applyArgs"])
  (expr_app (expr_id "this")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0");
    expr_id "applyArgs"])))
.
Definition ex_privarrayIndexOfCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "len")
      (expr_number (JsNumber.of_int (0))))
     (expr_break "ret"
      (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
     expr_undefined)
    (expr_let "n"
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
       expr_undefined) (expr_number (JsNumber.of_int (0)))
      (expr_app (expr_id "%ToInteger")
       [expr_get_attr pattr_value (expr_id "args") (expr_string "1")]))
     (expr_seq
      (expr_if (expr_op2 binary_op_ge (expr_id "n") (expr_id "len"))
       (expr_break "ret"
        (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
       expr_undefined)
      (expr_recc "loop"
       (expr_lambda ["k"]
        (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
         (expr_let "kStr" (expr_app (expr_id "%ToString") [expr_id "k"])
          (expr_if
           (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "kStr"])
           (expr_seq
            (expr_let "elementK"
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "kStr"])
             (expr_if
              (expr_op2 binary_op_stx_eq
               (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
               (expr_id "elementK")) (expr_break "ret" (expr_id "k"))
              expr_undefined))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)))]))
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "k")
             (expr_number (JsNumber.of_int (1)))]))) expr_undefined))
       (expr_let "start"
        (expr_if
         (expr_op2 binary_op_ge (expr_id "n")
          (expr_number (JsNumber.of_int (0)))) (expr_id "n")
         (expr_app (expr_id "%max")
          [expr_op2 binary_op_sub (expr_id "len")
           (expr_op1 unary_op_abs (expr_id "n"));
           expr_number (JsNumber.of_int (0))]))
        (expr_seq (expr_app (expr_id "loop") [expr_id "start"])
         (expr_break "ret"
          (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1))))))))))))))
.
Definition ex_privarrayLastIndexOfCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "len")
      (expr_number (JsNumber.of_int (0))))
     (expr_break "ret"
      (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
     expr_undefined)
    (expr_seq
     (expr_let "n"
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
        expr_undefined)
       (expr_op2 binary_op_sub (expr_id "len")
        (expr_number (JsNumber.of_int (1))))
       (expr_app (expr_id "%ToInteger")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "1")]))
      (expr_recc "loop"
       (expr_lambda ["k"]
        (expr_if
         (expr_op2 binary_op_ge (expr_id "k")
          (expr_number (JsNumber.of_int (0))))
         (expr_let "kstr" (expr_app (expr_id "%ToString") [expr_id "k"])
          (expr_if
           (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "kstr"])
           (expr_if
            (expr_op2 binary_op_stx_eq
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "kstr"])
             (expr_get_attr pattr_value (expr_id "args") (expr_string "0")))
            (expr_break "ret" (expr_id "k"))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_sub (expr_id "k")
              (expr_number (JsNumber.of_int (1)))]))
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_sub (expr_id "k")
             (expr_number (JsNumber.of_int (1)))]))) expr_undefined))
       (expr_let "start"
        (expr_if
         (expr_op2 binary_op_ge (expr_id "n")
          (expr_number (JsNumber.of_int (0))))
         (expr_app (expr_id "%min")
          [expr_id "n";
           expr_op2 binary_op_sub (expr_id "len")
           (expr_number (JsNumber.of_int (1)))])
         (expr_op2 binary_op_sub (expr_id "len")
          (expr_op1 unary_op_abs (expr_id "n"))))
        (expr_app (expr_id "loop") [expr_id "start"]))))
     (expr_break "ret"
      (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1))))))))))
.
Definition ex_privarrayTLSCall := 
expr_let "isCallable"
(expr_lambda ["o"]
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "o")))
    (expr_break "ret" expr_false) expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_code (expr_id "o"))
      expr_null) (expr_break "ret" expr_false) expr_null)
    (expr_break "ret" expr_true)))))
(expr_let "array" (expr_app (expr_id "%ToObject") [expr_id "this"])
 (expr_let "arrayLen"
  (expr_app (expr_id "%Get1") [expr_id "array"; expr_string "length"])
  (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "arrayLen"])
   (expr_let "separator" (expr_string " ")
    (expr_label "ret"
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "len")
        (expr_number (JsNumber.of_int (0))))
       (expr_break "ret" (expr_string "")) expr_null)
      (expr_let "firstElement"
       (expr_app (expr_id "%Get1") [expr_id "array"; expr_string "0"])
       (expr_let "R"
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq (expr_id "firstElement") expr_null)
          expr_true
          (expr_op2 binary_op_stx_eq (expr_id "firstElement") expr_undefined))
         (expr_string "")
         (expr_let "elementObj"
          (expr_app (expr_id "%ToObject") [expr_id "firstElement"])
          (expr_let "funcc"
           (expr_app (expr_id "%Get1")
            [expr_id "elementObj"; expr_string "toLocaleString"])
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
               expr_undefined) [] []])))))
        (expr_recc "inner"
         (expr_lambda ["k"; "r"]
          (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "len"))
           (expr_id "r")
           (expr_let "S"
            (expr_op2 binary_op_string_plus
             (expr_op1 unary_op_prim_to_str (expr_id "r"))
             (expr_id "separator"))
            (expr_let "nextElement"
             (expr_app (expr_id "%Get1")
              [expr_id "array"; expr_op1 unary_op_prim_to_str (expr_id "k")])
             (expr_let "toAppend"
              (expr_if
               (expr_if
                (expr_op2 binary_op_stx_eq (expr_id "nextElement") expr_null)
                expr_true
                (expr_op2 binary_op_stx_eq (expr_id "nextElement")
                 expr_undefined)) (expr_string "")
               (expr_let "elementObj"
                (expr_app (expr_id "%ToObject") [expr_id "nextElement"])
                (expr_let "funcc"
                 (expr_app (expr_id "%Get1")
                  [expr_id "elementObj"; expr_string "toLocaleString"])
                 (expr_seq
                  (expr_if
                   (expr_op1 unary_op_not
                    (expr_app (expr_id "isCallable") [expr_id "funcc"]))
                   (expr_throw
                    (expr_app (expr_id "%JSError")
                     [expr_object
                      (objattrs_intro (expr_string "Object") expr_true
                       (expr_id "%TypeErrorProto") expr_undefined) [] 
                      []])) expr_null)
                  (expr_app (expr_id "funcc")
                   [expr_id "elementObj";
                    expr_object
                    (objattrs_intro (expr_string "Object") expr_true
                     expr_null expr_undefined) [] []])))))
              (expr_app (expr_id "inner")
               [expr_op2 binary_op_add (expr_id "k")
                (expr_number (JsNumber.of_int (1)));
                expr_op2 binary_op_string_plus
                (expr_op1 unary_op_prim_to_str (expr_id "r"))
                (expr_op1 unary_op_prim_to_str (expr_id "toAppend"))]))))))
         (expr_break "ret"
          (expr_app (expr_id "inner")
           [expr_number (JsNumber.of_int (1)); expr_id "R"])))))))))))
.
Definition ex_privarrayToStringCall := 
expr_let "array" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "thefunc"
 (expr_get_attr pattr_value (expr_id "array") (expr_string "join"))
 (expr_let "ffunc"
  (expr_if
   (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "thefunc")))
   (expr_id "%objectToStringCall")
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_code (expr_id "thefunc")) expr_null)
    (expr_id "%objectToStringCall") (expr_id "thefunc")))
  (expr_app (expr_id "ffunc")
   [expr_id "array";
    expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
    [] []])))
.
Definition ex_privasinCall :=  expr_string "asin NYI" .
Definition ex_privassert := 
expr_if (expr_id "b") expr_true (expr_throw (expr_id "s"))
.
Definition ex_privatan2Call :=  expr_string "atan2 NYI" .
Definition ex_privatanCall :=  expr_string "atan NYI" .
Definition ex_privbindCall := 
expr_seq
(expr_if
 (expr_op1 unary_op_not (expr_app (expr_id "%IsCallable") [expr_id "this"]))
 (expr_app (expr_id "%TypeError") [expr_string "this not function in bind"])
 expr_undefined)
(expr_let "thisArg"
 (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
 (expr_let "A"
  (expr_app (expr_id "%slice")
   [expr_id "args";
    expr_app (expr_id "%oneArgObj") [expr_number (JsNumber.of_int (1))]])
  (expr_app (expr_id "%MakeBind")
   [expr_id "this"; expr_id "thisArg"; expr_id "A"])))
.
Definition ex_privbooleanToStringCall := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "this"))
(expr_let "b"
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "boolean"))
  (expr_id "this")
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_obj_attr oattr_class (expr_id "this")) (expr_string "Boolean"))
    (expr_get_internal "primval" (expr_id "this"))
    (expr_app (expr_id "%TypeError")
     [expr_string "Boolean.prototype.toString got non-boolean object"]))
   (expr_app (expr_id "%TypeError")
    [expr_op2 binary_op_string_plus
     (expr_string "Boolean.prototype.toString got ") (expr_id "t")])))
 (expr_if (expr_id "b") (expr_string "true") (expr_string "false")))
.
Definition ex_privcallCall := 
expr_let "callArgs"
(expr_app (expr_id "%slice_internal")
 [expr_id "args";
  expr_number (JsNumber.of_int (1));
  expr_app (expr_id "%len") [expr_id "args"]])
(expr_app (expr_id "this")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0");
  expr_id "callArgs"])
.
Definition ex_privcharAtCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "position"
  (expr_app (expr_id "%ToInteger")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_let "size" (expr_op1 unary_op_strlen (expr_id "S"))
   (expr_if
    (expr_if
     (expr_op2 binary_op_lt (expr_id "position")
      (expr_number (JsNumber.of_int (0)))) expr_true
     (expr_op2 binary_op_ge (expr_id "position") (expr_id "size")))
    (expr_string "")
    (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position"))))))
.
Definition ex_privcharCodeAtCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "position"
  (expr_app (expr_id "%ToInteger")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_let "size" (expr_op1 unary_op_strlen (expr_id "S"))
   (expr_if
    (expr_if
     (expr_op2 binary_op_lt (expr_id "position")
      (expr_number (JsNumber.of_int (0)))) expr_true
     (expr_op2 binary_op_ge (expr_id "position") (expr_id "size")))
    (expr_number JsNumber.nan)
    (expr_op1 unary_op_ascii_cton
     (expr_op2 binary_op_char_at (expr_id "S") (expr_id "position")))))))
.
Definition ex_privconcatCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "emptyobj"
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
  [] [])
 (expr_let "A"
  (expr_app (expr_id "%ArrayConstructor")
   [expr_id "emptyobj"; expr_id "emptyobj"])
  (expr_recc "procElt"
   (expr_lambda ["obj"; "elt"; "n"]
    (expr_let "procNormalElt"
     (expr_lambda ["nelt"; "k"]
      (expr_seq
       (expr_app (expr_id "%Put1")
        [expr_id "obj";
         expr_op1 unary_op_prim_to_str (expr_id "k");
         expr_id "nelt";
         expr_true])
       (expr_op2 binary_op_add (expr_id "k")
        (expr_number (JsNumber.of_int (1))))))
     (expr_recc "procArrayElt"
      (expr_lambda ["arr"; "fromIndex"; "toIndex"]
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_app (expr_id "%Get1")
          [expr_id "arr"; expr_op1 unary_op_prim_to_str (expr_id "fromIndex")])
         expr_undefined) (expr_id "toIndex")
        (expr_seq
         (expr_app (expr_id "%Put1")
          [expr_id "obj";
           expr_op1 unary_op_prim_to_str (expr_id "toIndex");
           expr_app (expr_id "%Get1")
           [expr_id "arr";
            expr_op1 unary_op_prim_to_str (expr_id "fromIndex")];
           expr_true])
         (expr_app (expr_id "procArrayElt")
          [expr_id "arr";
           expr_op2 binary_op_add (expr_id "fromIndex")
           (expr_number (JsNumber.of_int (1)));
           expr_op2 binary_op_add (expr_id "toIndex")
           (expr_number (JsNumber.of_int (1)))]))))
      (expr_if (expr_op1 unary_op_is_object (expr_id "elt"))
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_obj_attr oattr_class (expr_id "elt"))
         (expr_string "Array"))
        (expr_app (expr_id "procArrayElt")
         [expr_id "elt"; expr_number (JsNumber.of_int (0)); expr_id "n"])
        (expr_app (expr_id "procNormalElt") [expr_id "elt"; expr_id "n"]))
       (expr_app (expr_id "procNormalElt") [expr_id "elt"; expr_id "n"])))))
   (expr_recc "procAllElts"
    (expr_lambda ["from"; "fromIndex"; "toIndex"]
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq
        (expr_app (expr_id "%Get1")
         [expr_id "from"; expr_op1 unary_op_prim_to_str (expr_id "fromIndex")])
        expr_undefined))
      (expr_let "nextI"
       (expr_app (expr_id "procElt")
        [expr_id "A";
         expr_app (expr_id "%Get1")
         [expr_id "from"; expr_op1 unary_op_prim_to_str (expr_id "fromIndex")];
         expr_id "toIndex"])
       (expr_app (expr_id "procAllElts")
        [expr_id "from";
         expr_op2 binary_op_add (expr_id "fromIndex")
         (expr_number (JsNumber.of_int (1)));
         expr_id "nextI"])) (expr_id "toIndex")))
    (expr_let "halftime"
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_obj_attr oattr_class (expr_id "O")) (expr_string "Array"))
      (expr_app (expr_id "procAllElts")
       [expr_id "O";
        expr_number (JsNumber.of_int (0));
        expr_number (JsNumber.of_int (0))])
      (expr_seq
       (expr_set_attr pattr_value (expr_id "A") (expr_string "0")
        (expr_id "O")) (expr_number (JsNumber.of_int (1)))))
     (expr_let "end"
      (expr_app (expr_id "procAllElts")
       [expr_id "args"; expr_number (JsNumber.of_int (0)); expr_id "halftime"])
      (expr_seq
       (expr_set_attr pattr_value (expr_id "A") (expr_string "length")
        (expr_id "end")) (expr_id "A"))))))))
.
Definition ex_privconfigurableEval := 
expr_let "evalStr"
(expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_let "evalStr"
 (expr_if (expr_id "useStrict")
  (expr_op2 binary_op_string_plus (expr_string "'use strict';")
   (expr_id "evalStr")) (expr_id "evalStr"))
 (expr_let "globalEnv"
  (expr_app
   (expr_get_attr pattr_value (expr_id "%makeGlobalEnv") (expr_string "make"))
   [])
  (expr_seq
   (expr_set_attr pattr_value (expr_id "globalEnv") (expr_string "$this")
    (expr_id "this"))
   (expr_seq
    (expr_set_attr pattr_value (expr_id "globalEnv") (expr_string "$context")
     (expr_id "context"))
    (expr_seq
     (expr_set_attr pattr_value (expr_id "globalEnv")
      (expr_string "$vcontext") (expr_id "vcontext"))
     (expr_seq
      (expr_set_attr pattr_value (expr_id "globalEnv")
       (expr_string "evalCode") expr_true)
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_op1 unary_op_typeof (expr_id "evalStr")) (expr_string "string"))
       (expr_let "ret" (expr_eval (expr_id "evalStr") (expr_id "globalEnv"))
        (expr_if (expr_op2 binary_op_stx_eq (expr_id "ret") expr_empty)
         expr_undefined (expr_id "ret"))) (expr_id "evalStr"))))))))
.
Definition ex_privcosCall :=  expr_string "cos NYI" .
Definition ex_privcreateCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_let "t" (expr_op1 unary_op_typeof (expr_id "O"))
 (expr_if
  (expr_if
   (expr_op1 unary_op_not
    (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object")))
   (expr_op1 unary_op_not
    (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "null")))
   expr_false)
  (expr_app (expr_id "%TypeError") [expr_string "Object.create failed"])
  (expr_let "obj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true (expr_id "O")
     expr_undefined) [] [])
   (expr_if
    (expr_if
     (expr_op2 binary_op_ge
      (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
      (expr_number (JsNumber.of_int (2))))
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq
       (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
       expr_undefined)) expr_false)
    (expr_let "Properties"
     (expr_app (expr_id "%ToObject")
      [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
     (expr_let "argsObj"
      (expr_object
       (objattrs_intro (expr_string "Object") expr_true expr_null
        expr_undefined) [] [])
      (expr_seq
       (expr_set_attr pattr_value (expr_id "argsObj") (expr_string "0")
        (expr_id "obj"))
       (expr_seq
        (expr_set_attr pattr_value (expr_id "argsObj") (expr_string "1")
         (expr_id "Properties"))
        (expr_seq
         (expr_set_attr pattr_value (expr_id "argsObj")
          (expr_string "length") (expr_number (JsNumber.of_int (2))))
         (expr_seq
          (expr_app (expr_id "%defineProperties")
           [expr_null; expr_id "argsObj"]) (expr_id "obj")))))))
    (expr_id "obj")))))
.
Definition ex_privdateGetTimezoneOffsetCall := 
expr_let "t" (expr_get_internal "primval" (expr_id "this"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number JsNumber.nan))
 (expr_number JsNumber.nan) (expr_number (JsNumber.of_int (0))))
.
Definition ex_privdateToStringCall :=  expr_string "Date toString NYI" .
Definition ex_privdateValueOfCall := 
expr_get_internal "primval" (expr_id "this")
.
Definition ex_privdategetDateCall := 
expr_let "t" (expr_get_internal "primval" (expr_id "this"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_number JsNumber.nan))
 (expr_id "t")
 (expr_app (expr_id "%DateFromTime")
  [expr_app (expr_id "%LocalTime") [expr_id "t"]]))
.
Definition ex_privdategetDayCall := 
expr_let "day"
(expr_op1 unary_op_floor
 (expr_op2 binary_op_div (expr_get_internal "primval" (expr_id "this"))
  (expr_id "%msPerDay")))
(expr_let "weekday"
 (expr_op2 binary_op_mod
  (expr_op2 binary_op_add (expr_id "day") (expr_number (JsNumber.of_int (4))))
  (expr_number (JsNumber.of_int (7)))) (expr_id "weekday"))
.
Definition ex_privdecodeURICall :=  expr_string "decodeURI NYI" .
Definition ex_privdecodeURIComponentCall := 
expr_string "decodeURIComponent NYI"
.
Definition ex_privdefine15Property := 
expr_let "%mkPropObj"
(expr_lambda ["value"; "writable"; "enumerable"; "configurable"]
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq (expr_id "value") expr_null))
  (expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
   []
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
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
   []
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
  (expr_op2 binary_op_stx_eq (expr_app (expr_id "%Typeof") [expr_id "obj"])
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
Definition ex_privdefineNYIProperty := 
expr_let "unimplFunc"
(expr_lambda ["obj"; "this"; "args"]
 (expr_app (expr_id "%TypeError")
  [expr_op2 binary_op_string_plus (expr_id "name") (expr_string " NYI")]))
(expr_let "unimplObj"
 (expr_object
  (objattrs_intro (expr_string "Function") expr_true
   (expr_id "%FunctionProto") (expr_id "unimplFunc")) [] [])
 (expr_app (expr_id "%define15Property")
  [expr_id "base"; expr_id "name"; expr_id "unimplObj"]))
.
Definition ex_privdefineOwnProperty := 
expr_seq
(expr_if
 (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "obj")))
 (expr_throw (expr_string "defineOwnProperty didn't get object"))
 expr_undefined)
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
        (expr_if
         (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
          (expr_string "value"))
         (expr_set_attr pattr_value (expr_id "obj") (expr_id "fstr")
          (expr_get_attr pattr_value (expr_id "attr-obj")
           (expr_string "value"))) expr_undefined)
        (expr_if
         (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
          (expr_string "writable"))
         (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
          (expr_app (expr_id "%ToBoolean")
           [expr_get_attr pattr_value (expr_id "attr-obj")
            (expr_string "writable")])) expr_undefined))
       (expr_if
        (expr_app (expr_id "isAccessorDescriptor") [expr_id "attr-obj"])
        (expr_seq
         (expr_if
          (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
           (expr_string "get"))
          (expr_set_attr pattr_getter (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "attr-obj")
            (expr_string "get"))) expr_undefined)
         (expr_if
          (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
           (expr_string "set"))
          (expr_set_attr pattr_setter (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "attr-obj")
            (expr_string "set"))) expr_undefined)) expr_undefined))
      (expr_seq
       (expr_if
        (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
         (expr_string "enumerable"))
        (expr_set_attr pattr_enum (expr_id "obj") (expr_id "fstr")
         (expr_app (expr_id "%ToBoolean")
          [expr_get_attr pattr_value (expr_id "attr-obj")
           (expr_string "enumerable")])) expr_undefined)
       (expr_seq
        (expr_if
         (expr_op2 binary_op_has_own_property (expr_id "attr-obj")
          (expr_string "configurable"))
         (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr")
          (expr_app (expr_id "%ToBoolean")
           [expr_get_attr pattr_value (expr_id "attr-obj")
            (expr_string "configurable")])) expr_undefined) expr_true)))))
   (expr_app (expr_id "%TypeError")
    [expr_string
     "(defineOwnProperty) Attempt to add a property to a non-extensible object."]))
  (expr_let "current-prop"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
    []
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
      (expr_set_attr pattr_value (expr_id "current-prop") (expr_string "get")
       (expr_get_attr pattr_getter (expr_id "obj") (expr_id "fstr")))
      (expr_set_attr pattr_value (expr_id "current-prop") (expr_string "set")
       (expr_get_attr pattr_setter (expr_id "obj") (expr_id "fstr"))))
     (expr_seq
      (expr_set_attr pattr_value (expr_id "current-prop")
       (expr_string "writable")
       (expr_get_attr pattr_writable (expr_id "obj") (expr_id "fstr")))
      (expr_set_attr pattr_value (expr_id "current-prop")
       (expr_string "value")
       (expr_get_attr pattr_value (expr_id "obj") (expr_id "fstr")))))
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq
       (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
       expr_false)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq
         (expr_get_attr pattr_value (expr_id "attr-obj")
          (expr_string "configurable")) expr_true)
        (expr_app (expr_id "%TypeError")
         [expr_string "escalating configurable from false to true"])
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_attr pattr_value (expr_id "attr-obj")
           (expr_string "enumerable"))
          (expr_op2 binary_op_stx_eq
           (expr_get_attr pattr_enum (expr_id "obj") (expr_id "fstr"))
           expr_false))
         (expr_app (expr_id "%TypeError")
          [expr_string
           "(defineOwnPoperty) Can't change enumerable of a non-configurable property"])
         expr_undefined))
       (expr_if
        (expr_op1 unary_op_not
         (expr_op2 binary_op_stx_eq
          (expr_app (expr_id "isDataDescriptor") [expr_id "current-prop"])
          (expr_app (expr_id "isDataDescriptor") [expr_id "attr-obj"])))
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
         (expr_get_attr pattr_value (expr_id "current-prop")
          (expr_string "configurable")) expr_false)
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_get_attr pattr_value (expr_id "current-prop")
           (expr_string "writable")) expr_false)
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_get_attr pattr_value (expr_id "attr-obj")
            (expr_string "writable")) expr_true)
          (expr_app (expr_id "%TypeError")
           [expr_string
            "(defineOwnProperty) Cannot escalate writable from false to true."])
          (expr_if
           (expr_op2 binary_op_stx_eq
            (expr_op2 binary_op_same_value
             (expr_get_attr pattr_value (expr_id "attr-obj")
              (expr_string "value"))
             (expr_get_attr pattr_value (expr_id "current-prop")
              (expr_string "value"))) expr_false)
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
         (expr_get_attr pattr_value (expr_id "current-prop")
          (expr_string "configurable")) expr_false)
        (expr_if
         (expr_if
          (expr_op2 binary_op_stx_eq
           (expr_op2 binary_op_same_value
            (expr_get_attr pattr_value (expr_id "current-prop")
             (expr_string "set"))
            (expr_get_attr pattr_value (expr_id "attr-obj")
             (expr_string "set"))) expr_false) expr_true
          (expr_op2 binary_op_stx_eq
           (expr_op2 binary_op_same_value
            (expr_get_attr pattr_value (expr_id "current-prop")
             (expr_string "get"))
            (expr_get_attr pattr_value (expr_id "attr-obj")
             (expr_string "get"))) expr_false))
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
            (expr_get_attr pattr_value (expr_id "current-prop")
             (expr_string "value"))) expr_false)
          (expr_set_attr pattr_value (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "value"))) expr_undefined)
         (expr_if
          (expr_op1 unary_op_not
           (expr_op2 binary_op_stx_eq
            (expr_get_attr pattr_writable (expr_id "obj") (expr_id "fstr"))
            (expr_get_attr pattr_value (expr_id "current-prop")
             (expr_string "writable"))))
          (expr_set_attr pattr_writable (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "writable"))) expr_undefined))
        (expr_if
         (expr_app (expr_id "isAccessorDescriptor") [expr_id "current-prop"])
         (expr_seq
          (expr_set_attr pattr_getter (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "get")))
          (expr_set_attr pattr_setter (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "set")))) expr_undefined))
       (expr_seq
        (expr_if
         (expr_op1 unary_op_not
          (expr_op2 binary_op_stx_eq
           (expr_get_attr pattr_enum (expr_id "obj") (expr_id "fstr"))
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "enumerable"))))
         (expr_set_attr pattr_enum (expr_id "obj") (expr_id "fstr")
          (expr_get_attr pattr_value (expr_id "current-prop")
           (expr_string "enumerable"))) expr_undefined)
        (expr_seq
         (expr_if
          (expr_op1 unary_op_not
           (expr_op2 binary_op_stx_eq
            (expr_get_attr pattr_config (expr_id "obj") (expr_id "fstr"))
            (expr_get_attr pattr_value (expr_id "current-prop")
             (expr_string "configurable"))))
          (expr_set_attr pattr_config (expr_id "obj") (expr_id "fstr")
           (expr_get_attr pattr_value (expr_id "current-prop")
            (expr_string "configurable"))) expr_undefined) expr_true)))))))))
.
Definition ex_privdefinePropertiesCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_seq
  (expr_let "props"
   (expr_app (expr_id "%ToObject")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
   (expr_let "names" (expr_own_field_names (expr_id "props"))
    (expr_let "len"
     (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
     (expr_recc "loop"
      (expr_lambda ["i"]
       (expr_label "ret"
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
         (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
          (expr_let "name"
           (expr_app (expr_id "%Get1") [expr_id "names"; expr_id "indx"])
           (expr_if
            (expr_get_attr pattr_enum (expr_id "props") (expr_id "name"))
            (expr_let "argsObj"
             (expr_object
              (objattrs_intro (expr_string "Object") expr_true expr_null
               expr_undefined) [] [])
             (expr_seq
              (expr_set_attr pattr_value (expr_id "argsObj")
               (expr_string "0") (expr_id "O"))
              (expr_seq
               (expr_set_attr pattr_value (expr_id "argsObj")
                (expr_string "1") (expr_id "name"))
               (expr_seq
                (expr_set_attr pattr_value (expr_id "argsObj")
                 (expr_string "2")
                 (expr_app (expr_id "%Get1")
                  [expr_id "props"; expr_id "name"]))
                (expr_seq
                 (expr_set_attr pattr_value (expr_id "argsObj")
                  (expr_string "length") (expr_number (JsNumber.of_int (3))))
                 (expr_seq
                  (expr_app (expr_id "%defineProperty")
                   [expr_null; expr_id "argsObj"])
                  (expr_break "ret"
                   (expr_app (expr_id "loop")
                    [expr_op2 binary_op_add (expr_id "i")
                     (expr_number (JsNumber.of_int (1)))]))))))))
            (expr_break "ret"
             (expr_app (expr_id "loop")
              [expr_op2 binary_op_add (expr_id "i")
               (expr_number (JsNumber.of_int (1)))])))))
         (expr_break "ret" expr_undefined))))
      (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))))
  (expr_id "O")))
.
Definition ex_privdefinePropertyCall := 
expr_let "obj" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_let "field"
 (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
 (expr_let "propobj"
  (expr_get_attr pattr_value (expr_id "args") (expr_string "2"))
  (expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "obj"])
   (expr_app (expr_id "%defineOwnProperty")
    [expr_id "obj";
     expr_app (expr_id "%ToString") [expr_id "field"];
     expr_app (expr_id "%ToPropertyDescriptor") [expr_id "propobj"]]))))
.
Definition ex_privencodeURICall :=  expr_string "encodeURI NYI" .
Definition ex_privencodeURIComponentCall := 
expr_string "encodeURIComponent NYI"
.
Definition ex_privescapeCall :=  expr_string "escape NYI" .
Definition ex_privetsCall := 
expr_if
(expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "this")))
(expr_app (expr_id "%TypeError")
 [expr_string "This not object in Error.prototype.toString"])
(expr_let "name"
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_app (expr_id "%Get1") [expr_id "this"; expr_string "name"])
   expr_undefined) (expr_string "Error")
  (expr_app (expr_id "%ToString")
   [expr_app (expr_id "%Get1") [expr_id "this"; expr_string "name"]]))
 (expr_let "msg"
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_app (expr_id "%Get1") [expr_id "this"; expr_string "message"])
    expr_undefined) (expr_string "")
   (expr_app (expr_id "%ToString")
    [expr_app (expr_id "%Get1") [expr_id "this"; expr_string "message"]]))
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
Definition ex_privevalCall := 
expr_app (expr_id "%configurableEval")
[expr_id "%global";
 expr_id "%globalContext";
 expr_id "%globalContext";
 expr_false;
 expr_id "args"]
.
Definition ex_priveveryCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op1 unary_op_not
       (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
      (expr_app (expr_id "%TypeError")
       [expr_string "Callback not function in every"]) expr_null)
     (expr_let "T"
      (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
      (expr_recc "loop"
       (expr_lambda ["k"]
        (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
         (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
          (expr_let "kPresent"
           (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
           (expr_if (expr_id "kPresent")
            (expr_let "kValue"
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
             (expr_let "argsObj"
              (expr_object
               (objattrs_intro (expr_string "Object") expr_true expr_null
                expr_undefined) [] [])
              (expr_seq
               (expr_set_attr pattr_value (expr_id "argsObj")
                (expr_string "0") (expr_id "kValue"))
               (expr_seq
                (expr_set_attr pattr_value (expr_id "argsObj")
                 (expr_string "1") (expr_id "k"))
                (expr_seq
                 (expr_set_attr pattr_value (expr_id "argsObj")
                  (expr_string "2") (expr_id "O"))
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "length") (expr_number (JsNumber.of_int (3))))
                  (expr_let "testResult"
                   (expr_app (expr_id "callbackfn")
                    [expr_id "T"; expr_id "argsObj"])
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_app (expr_id "%ToBoolean") [expr_id "testResult"])
                     expr_false) expr_false
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "k")
                      (expr_number (JsNumber.of_int (1)))])))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)))])))) expr_true))
       (expr_break "ret"
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))))))))
.
Definition ex_privexpCall :=  expr_undefined .
Definition ex_privfilterCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op1 unary_op_not
       (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
      (expr_app (expr_id "%TypeError")
       [expr_string "Callback not a function in filter"]) expr_null)
     (expr_let "T"
      (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
      (expr_let "A"
       (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
       (expr_recc "loop"
        (expr_lambda ["k"; "to"]
         (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
          (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
           (expr_if
            (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
            (expr_let "kValue"
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
             (expr_let "argsObj"
              (expr_object
               (objattrs_intro (expr_string "Object") expr_true expr_null
                expr_undefined) [] [])
              (expr_seq
               (expr_set_attr pattr_value (expr_id "argsObj")
                (expr_string "0") (expr_id "kValue"))
               (expr_seq
                (expr_set_attr pattr_value (expr_id "argsObj")
                 (expr_string "1") (expr_id "k"))
                (expr_seq
                 (expr_set_attr pattr_value (expr_id "argsObj")
                  (expr_string "2") (expr_id "O"))
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "length") (expr_number (JsNumber.of_int (3))))
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
                        expr_null expr_undefined) []
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
                       (expr_number (JsNumber.of_int (1)));
                       expr_op2 binary_op_add (expr_id "to")
                       (expr_number (JsNumber.of_int (1)))]))
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "k")
                      (expr_number (JsNumber.of_int (1)));
                      expr_id "to"])))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)));
              expr_id "to"])))
          (expr_set_attr pattr_value (expr_id "A") (expr_string "length")
           (expr_id "to"))))
        (expr_seq
         (expr_app (expr_id "loop")
          [expr_number (JsNumber.of_int (0));
           expr_number (JsNumber.of_int (0))])
         (expr_break "ret" (expr_id "A")))))))))))
.
Definition ex_privforeachCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op1 unary_op_not
       (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
      (expr_app (expr_id "%TypeError")
       [expr_string "Callback not a function in forEach"]) expr_undefined)
     (expr_seq
      (expr_let "T"
       (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
       (expr_recc "loop"
        (expr_lambda ["k"]
         (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
          (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
           (expr_if
            (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
            (expr_seq
             (expr_let "kValue"
              (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
              (expr_let "argslist"
               (expr_object
                (objattrs_intro (expr_string "Object") expr_true expr_null
                 expr_undefined) []
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
               (expr_number (JsNumber.of_int (1)))]))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)))]))) expr_undefined))
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))
      expr_undefined))))))
.
Definition ex_privfreezeCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "names" (expr_own_field_names (expr_id "O"))
  (expr_let "len"
   (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
   (expr_recc "loop"
    (expr_lambda ["i"]
     (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
      (expr_let "name"
       (expr_get_attr pattr_value (expr_id "names")
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
           (expr_number (JsNumber.of_int (1)))])))) expr_null))
    (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
     (expr_seq (expr_set_obj_attr oattr_extensible (expr_id "O") expr_false)
      (expr_id "O")))))))
.
Definition ex_privfromccCall := 
expr_if
(expr_op2 binary_op_stx_eq
 (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
 (expr_number (JsNumber.of_int (0)))) (expr_string "")
(expr_let "end"
 (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
 (expr_recc "loop"
  (expr_lambda ["i"; "soFar"]
   (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
    (expr_let "char"
     (expr_op1 unary_op_ascii_ntoc
      (expr_app (expr_id "%ToUint16")
       [expr_get_attr pattr_value (expr_id "args")
        (expr_op1 unary_op_prim_to_str (expr_id "i"))]))
     (expr_let "next"
      (expr_op2 binary_op_string_plus (expr_id "soFar") (expr_id "char"))
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int (1)));
        expr_id "next"]))) (expr_id "soFar")))
  (expr_app (expr_id "loop")
   [expr_number (JsNumber.of_int (0)); expr_string ""])))
.
Definition ex_privfunctionToStringCall := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "this"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_class (expr_id "this"))
   (expr_string "Function"))
  (expr_if
   (expr_op2 binary_op_has_internal (expr_id "this") (expr_string "codetxt"))
   (expr_get_internal "codetxt" (expr_id "this"))
   (expr_string "<internal function>"))
  (expr_app (expr_id "%TypeError")
   [expr_string "Function.prototype.toString got a non-function"]))
 (expr_app (expr_id "%TypeError")
  [expr_string "Function.prototype.toString got a non-object"]))
.
Definition ex_privgetCurrentUTC := 
expr_op1 unary_op_current_utc_millis expr_undefined
.
Definition ex_privgetMonthCall :=  expr_number (JsNumber.of_int (3)) .
Definition ex_privgetYearCall :=  expr_number (JsNumber.of_int (78)) .
Definition ex_privgopdCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "name"
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
  (expr_label "ret"
   (expr_seq
    (expr_if
     (expr_op1 unary_op_not
      (expr_op2 binary_op_has_own_property (expr_id "O") (expr_id "name")))
     (expr_break "ret" expr_undefined) expr_null)
    (expr_let "obj"
     (expr_object
      (objattrs_intro (expr_string "Object") expr_true
       (expr_id "%ObjectProto") expr_undefined) [] [])
     (expr_seq
      (expr_app (expr_id "%defineOwnProperty")
       [expr_id "obj";
        expr_string "enumerable";
        expr_object
        (objattrs_intro (expr_string "Object") expr_true expr_null
         expr_undefined) []
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
         (objattrs_intro (expr_string "Object") expr_true expr_null
          expr_undefined) []
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
            expr_undefined) []
           [("value", property_data
                      (data_intro
                       (expr_app (expr_id "%Get1")
                        [expr_id "O"; expr_id "name"]) expr_true expr_false
                       expr_false));
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
             expr_undefined) []
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
            expr_undefined) []
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
             expr_undefined) []
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
Definition ex_privgopnCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "props" (expr_own_field_names (expr_id "O"))
  (expr_let "len"
   (expr_get_attr pattr_value (expr_id "props") (expr_string "length"))
   (expr_let "A" (expr_app (expr_id "%MakeArray") [expr_id "len"])
    (expr_recc "loop"
     (expr_lambda ["i"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_seq
        (expr_let "to" (expr_op1 unary_op_prim_to_str (expr_id "i"))
         (expr_let "from"
          (expr_op1 unary_op_prim_to_str
           (expr_op2 binary_op_sub (expr_id "len")
            (expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int (1))))))
          (expr_set_attr pattr_value (expr_id "A") (expr_id "to")
           (expr_app (expr_id "%Get1") [expr_id "props"; expr_id "from"]))))
        (expr_app (expr_id "loop")
         [expr_op2 binary_op_add (expr_id "i")
          (expr_number (JsNumber.of_int (1)))])) expr_undefined))
     (expr_seq
      (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
      (expr_id "A")))))))
.
Definition ex_privgpoCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_get_obj_attr oattr_proto (expr_id "O")))
.
Definition ex_privhasOwnPropertyCall := 
expr_op2 binary_op_has_own_property
(expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_app (expr_id "%ToString")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
.
Definition ex_privin := 
expr_if (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "r")))
(expr_app (expr_id "%TypeError") [expr_string "not an object"])
(expr_app (expr_id "%HasProperty")
 [expr_id "r"; expr_app (expr_id "%ToString") [expr_id "l"]])
.
Definition ex_privinstanceof := 
expr_label "ret"
(expr_seq
 (expr_if
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq (expr_app (expr_id "%Typeof") [expr_id "r"])
    (expr_string "function")))
  (expr_app (expr_id "%TypeError")
   [expr_string "Non-function given to instanceof"]) expr_null)
 (expr_seq
  (expr_if
   (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "l")))
   (expr_break "ret" expr_false) expr_null)
  (expr_let "O"
   (expr_app (expr_id "%Get1") [expr_id "r"; expr_string "prototype"])
   (expr_if
    (expr_op1 unary_op_not (expr_op1 unary_op_is_object (expr_id "O")))
    (expr_app (expr_id "%TypeError")
     [expr_string "Prototype was not function or object"])
    (expr_recc "search"
     (expr_lambda ["v"]
      (expr_let "vp" (expr_get_obj_attr oattr_proto (expr_id "v"))
       (expr_if (expr_op2 binary_op_stx_eq (expr_id "vp") expr_null)
        expr_false
        (expr_if (expr_op2 binary_op_stx_eq (expr_id "O") (expr_id "vp"))
         expr_true (expr_app (expr_id "search") [expr_id "vp"])))))
     (expr_break "ret" (expr_app (expr_id "search") [expr_id "l"])))))))
.
Definition ex_privisExtensibleCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_get_obj_attr oattr_extensible (expr_id "O")))
.
Definition ex_privisFiniteCall := 
expr_app (expr_id "%IsFinite")
[expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]]
.
Definition ex_privisFrozenCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "names" (expr_own_field_names (expr_id "O"))
  (expr_let "len"
   (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
   (expr_recc "loop"
    (expr_lambda ["i"]
     (expr_label "ret"
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_let "name"
        (expr_get_attr pattr_value (expr_id "names")
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
              (expr_number (JsNumber.of_int (1)))]))))))
       (expr_break "ret"
        (expr_op1 unary_op_not
         (expr_get_obj_attr oattr_extensible (expr_id "O")))))))
    (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))))
.
Definition ex_privisNaNCall := 
expr_op2 binary_op_same_value
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_number JsNumber.nan)
.
Definition ex_privisPrototypeOfCall := 
expr_recc "searchChain"
(expr_lambda ["o"; "v"]
 (expr_let "vproto" (expr_get_obj_attr oattr_proto (expr_id "v"))
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "vproto") expr_null)
   expr_false
   (expr_if (expr_op2 binary_op_stx_eq (expr_id "o") (expr_id "vproto"))
    expr_true
    (expr_app (expr_id "searchChain") [expr_id "o"; expr_id "vproto"])))))
(expr_if
 (expr_op1 unary_op_not
  (expr_op1 unary_op_is_object
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))))
 expr_false
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_app (expr_id "searchChain")
   [expr_id "O"; expr_get_attr pattr_value (expr_id "args") (expr_string "0")])))
.
Definition ex_privisSealedCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "names" (expr_own_field_names (expr_id "O"))
  (expr_let "len"
   (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
   (expr_recc "loop"
    (expr_lambda ["i"]
     (expr_label "ret"
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_seq
        (expr_let "name"
         (expr_get_attr pattr_value (expr_id "names")
          (expr_op1 unary_op_prim_to_str (expr_id "i")))
         (expr_if (expr_get_attr pattr_config (expr_id "O") (expr_id "name"))
          (expr_break "ret" expr_false) expr_null))
        (expr_break "ret"
         (expr_app (expr_id "loop")
          [expr_op2 binary_op_add (expr_id "i")
           (expr_number (JsNumber.of_int (1)))])))
       (expr_break "ret"
        (expr_op1 unary_op_not
         (expr_get_obj_attr oattr_extensible (expr_id "O")))))))
    (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))))
.
Definition ex_privjoinCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "sep"
   (expr_if
    (expr_op2 binary_op_stx_eq
     (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
     expr_undefined) (expr_string ",")
    (expr_app (expr_id "%ToString")
     [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "len")
       (expr_number (JsNumber.of_int (0))))
      (expr_break "ret" (expr_string "")) expr_null)
     (expr_recc "loop"
      (expr_lambda ["k"; "R"]
       (expr_if (expr_op2 binary_op_ge (expr_id "k") (expr_id "len"))
        (expr_id "R")
        (expr_let "S"
         (expr_op2 binary_op_string_plus (expr_id "R") (expr_id "sep"))
         (expr_let "element"
          (expr_app (expr_id "%Get1")
           [expr_id "O"; expr_app (expr_id "%ToString") [expr_id "k"]])
          (expr_let "next"
           (expr_if
            (expr_if
             (expr_op2 binary_op_stx_eq (expr_id "element") expr_null)
             expr_true
             (expr_op2 binary_op_stx_eq (expr_id "element") expr_undefined))
            (expr_string "")
            (expr_app (expr_id "%ToString") [expr_id "element"]))
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "k")
             (expr_number (JsNumber.of_int (1)));
             expr_op2 binary_op_string_plus (expr_id "S") (expr_id "next")]))))))
      (expr_let "start"
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq
          (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "0"])
          expr_undefined) expr_true
         (expr_op2 binary_op_stx_eq
          (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "0"])
          expr_null)) (expr_string "")
        (expr_app (expr_id "%ToString")
         [expr_app (expr_id "%Get1") [expr_id "O"; expr_string "0"]]))
       (expr_break "ret"
        (expr_app (expr_id "loop")
         [expr_number (JsNumber.of_int (1)); expr_id "start"])))))))))
.
Definition ex_privkeysCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_let "names" (expr_own_field_names (expr_id "O"))
  (expr_let "len"
   (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
   (expr_let "A"
    (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
    (expr_recc "loop"
     (expr_lambda ["i"; "enumCount"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
        (expr_let "name"
         (expr_get_attr pattr_value (expr_id "names") (expr_id "indx"))
         (expr_if (expr_get_attr pattr_enum (expr_id "O") (expr_id "name"))
          (expr_seq
           (expr_let "pd"
            (expr_object
             (objattrs_intro (expr_string "Object") expr_true expr_null
              expr_undefined) []
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
             (expr_number (JsNumber.of_int (1)));
             expr_op2 binary_op_add (expr_id "enumCount")
             (expr_number (JsNumber.of_int (1)))]))
          (expr_app (expr_id "loop")
           [expr_op2 binary_op_add (expr_id "i")
            (expr_number (JsNumber.of_int (1)));
            expr_id "enumCount"]))))
       (expr_set_attr pattr_value (expr_id "A") (expr_string "length")
        (expr_id "enumCount"))))
     (expr_seq
      (expr_app (expr_id "loop")
       [expr_number (JsNumber.of_int (0)); expr_number (JsNumber.of_int (0))])
      (expr_id "A")))))))
.
Definition ex_privlen := 
expr_recc "inner_len"
(expr_lambda ["iter"]
 (expr_if
  (expr_op2 binary_op_has_own_property (expr_id "list")
   (expr_op1 unary_op_prim_to_str (expr_id "iter")))
  (expr_op2 binary_op_add (expr_number (JsNumber.of_int (1)))
   (expr_app (expr_id "inner_len")
    [expr_op2 binary_op_add (expr_number (JsNumber.of_int (1)))
     (expr_id "iter")])) (expr_id "iter")))
(expr_app (expr_id "inner_len") [expr_number (JsNumber.of_int (0))])
.
Definition ex_privlocaleCompareCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "That"
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_op2 binary_op_locale_compare (expr_id "S") (expr_id "That"))))
.
Definition ex_privlogCall := 
expr_recc "loop"
(expr_lambda ["i"]
 (expr_if
  (expr_app (expr_id "%HasProperty")
   [expr_id "args"; expr_op1 unary_op_prim_to_str (expr_id "i")])
  (expr_seq
   (expr_op1 unary_op_pretty
    (expr_get_attr pattr_value (expr_id "args")
     (expr_op1 unary_op_prim_to_str (expr_id "i"))))
   (expr_app (expr_id "loop")
    [expr_op2 binary_op_add (expr_id "i") (expr_number (JsNumber.of_int (1)))]))
  expr_undefined))
(expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
.
Definition ex_privmapCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op1 unary_op_not
       (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
      (expr_app (expr_id "%TypeError")
       [expr_string "Callback not a function in map"]) expr_null)
     (expr_let "T"
      (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
      (expr_let "A"
       (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
       (expr_recc "loop"
        (expr_lambda ["k"]
         (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
          (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
           (expr_if
            (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
            (expr_let "kValue"
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
             (expr_let "argsObj"
              (expr_object
               (objattrs_intro (expr_string "Object") expr_true expr_null
                expr_undefined) [] [])
              (expr_seq
               (expr_set_attr pattr_value (expr_id "argsObj")
                (expr_string "0") (expr_id "kValue"))
               (expr_seq
                (expr_set_attr pattr_value (expr_id "argsObj")
                 (expr_string "1") (expr_id "k"))
                (expr_seq
                 (expr_set_attr pattr_value (expr_id "argsObj")
                  (expr_string "2") (expr_id "O"))
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "length") (expr_number (JsNumber.of_int (3))))
                  (expr_seq
                   (expr_let "mappedValue"
                    (expr_app (expr_id "callbackfn")
                     [expr_id "T"; expr_id "argsObj"])
                    (expr_app (expr_id "%defineOwnProperty")
                     [expr_id "A";
                      expr_id "Pk";
                      expr_object
                      (objattrs_intro (expr_string "Object") expr_true
                       expr_null expr_undefined) []
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
                     (expr_number (JsNumber.of_int (1)))]))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)))])))
          (expr_set_attr pattr_value (expr_id "A") (expr_string "length")
           (expr_id "k"))))
        (expr_seq
         (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
         (expr_break "ret" (expr_id "A")))))))))))
.
Definition ex_privmathAbsCall := 
expr_let "n"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op1 unary_op_not
    (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")))
   (expr_break "ret" (expr_id "n")) expr_null)
  (expr_seq
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "n")
     (expr_number JsNumber.neg_infinity))
    (expr_break "ret" (expr_number JsNumber.infinity)) expr_null)
   (expr_break "ret" (expr_op1 unary_op_abs (expr_id "n"))))))
.
Definition ex_privmathCeilCall := 
expr_let "x"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_if
    (expr_if
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))) expr_true
      (expr_op2 binary_op_stx_eq (expr_id "x")
       (expr_number (JsNumber.of_int (0))))) expr_true
     (expr_op2 binary_op_stx_eq (expr_id "x")
      (expr_number JsNumber.neg_infinity))) expr_true
    (expr_op2 binary_op_stx_eq (expr_id "x") (expr_number JsNumber.infinity)))
   (expr_break "ret" (expr_id "x")) expr_null)
  (expr_break "ret" (expr_op1 unary_op_ceil (expr_id "x")))))
.
Definition ex_privmathFloorCall := 
expr_let "x"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_if
    (expr_if
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x"))) expr_true
      (expr_op2 binary_op_stx_eq (expr_id "x")
       (expr_number (JsNumber.of_int (0))))) expr_true
     (expr_op2 binary_op_stx_eq (expr_id "x")
      (expr_number JsNumber.neg_infinity))) expr_true
    (expr_op2 binary_op_stx_eq (expr_id "x") (expr_number JsNumber.infinity)))
   (expr_break "ret" (expr_id "x")) expr_null)
  (expr_break "ret" (expr_op1 unary_op_floor (expr_id "x")))))
.
Definition ex_privmathLogCall := 
expr_let "n"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op1 unary_op_not
    (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")))
   (expr_break "ret" (expr_id "n")) expr_null)
  (expr_seq
   (expr_if
    (expr_op2 binary_op_lt (expr_id "n") (expr_number (JsNumber.of_int (0))))
    (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "n")
      (expr_number (JsNumber.of_int (0))))
     (expr_break "ret" (expr_number JsNumber.neg_infinity)) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_number (JsNumber.of_int (1))))
      (expr_break "ret" (expr_number (JsNumber.of_int (0)))) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "n")
        (expr_number JsNumber.infinity)) (expr_break "ret" (expr_id "n"))
       expr_null) (expr_break "ret" (expr_op1 unary_op_log (expr_id "n")))))))))
.
Definition ex_privmathMaxCall := 
expr_app (expr_id "%minMaxCall")
[expr_id "this";
 expr_id "args";
 expr_id "%max";
 expr_number JsNumber.neg_infinity]
.
Definition ex_privmathMinCall := 
expr_app (expr_id "%minMaxCall")
[expr_id "this";
 expr_id "args";
 expr_id "%min";
 expr_number JsNumber.infinity]
.
Definition ex_privmathPowCall := 
expr_let "x"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_let "y"
 (expr_app (expr_id "%ToNumber")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq (expr_id "y") (expr_id "y")))
    (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "y")
      (expr_number (JsNumber.of_int (0))))
     (expr_break "ret" (expr_number (JsNumber.of_int (1)))) expr_null)
    (expr_seq
     (expr_if
      (expr_if
       (expr_op1 unary_op_not
        (expr_op2 binary_op_stx_eq (expr_id "x") (expr_id "x")))
       (expr_op1 unary_op_not
        (expr_op2 binary_op_stx_eq (expr_id "y")
         (expr_number (JsNumber.of_int (0))))) expr_false)
      (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
     (expr_let "absX" (expr_op1 unary_op_abs (expr_id "x"))
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_gt (expr_id "absX")
          (expr_number (JsNumber.of_int (1))))
         (expr_op2 binary_op_stx_eq (expr_id "y")
          (expr_number JsNumber.infinity)) expr_false)
        (expr_break "ret" (expr_number JsNumber.infinity)) expr_null)
       (expr_seq
        (expr_if
         (expr_if
          (expr_op2 binary_op_gt (expr_id "absX")
           (expr_number (JsNumber.of_int (1))))
          (expr_op2 binary_op_stx_eq (expr_id "y")
           (expr_number JsNumber.neg_infinity)) expr_false)
         (expr_break "ret" (expr_number (JsNumber.of_int (0)))) expr_null)
        (expr_seq
         (expr_if
          (expr_if
           (expr_op2 binary_op_stx_eq (expr_id "absX")
            (expr_number (JsNumber.of_int (1))))
           (expr_if
            (expr_op2 binary_op_stx_eq (expr_id "y")
             (expr_number JsNumber.infinity)) expr_true
            (expr_op2 binary_op_stx_eq (expr_id "y")
             (expr_number JsNumber.neg_infinity))) expr_false)
          (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
         (expr_seq
          (expr_if
           (expr_if
            (expr_op2 binary_op_lt (expr_id "absX")
             (expr_number (JsNumber.of_int (1))))
            (expr_op2 binary_op_stx_eq (expr_id "y")
             (expr_number JsNumber.infinity)) expr_false)
           (expr_break "ret" (expr_number (JsNumber.of_int (0)))) expr_null)
          (expr_seq
           (expr_if
            (expr_if
             (expr_op2 binary_op_lt (expr_id "absX")
              (expr_number (JsNumber.of_int (1))))
             (expr_op2 binary_op_stx_eq (expr_id "y")
              (expr_number JsNumber.neg_infinity)) expr_false)
            (expr_break "ret" (expr_number JsNumber.infinity)) expr_null)
           (expr_seq
            (expr_if
             (expr_if
              (expr_op2 binary_op_stx_eq (expr_id "x")
               (expr_number JsNumber.infinity))
              (expr_op2 binary_op_gt (expr_id "y")
               (expr_number (JsNumber.of_int (0)))) expr_false)
             (expr_break "ret" (expr_number JsNumber.infinity)) expr_null)
            (expr_seq
             (expr_if
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "x")
                (expr_number JsNumber.infinity))
               (expr_op2 binary_op_lt (expr_id "y")
                (expr_number (JsNumber.of_int (0)))) expr_false)
              (expr_break "ret" (expr_number (JsNumber.of_int (0))))
              expr_null)
             (expr_let "isOdd"
              (expr_lambda ["n"]
               (expr_let "divided"
                (expr_op2 binary_op_div (expr_id "n")
                 (expr_number (JsNumber.of_int (2))))
                (expr_if
                 (expr_op2 binary_op_stx_eq
                  (expr_op1 unary_op_floor (expr_id "n")) (expr_id "n"))
                 (expr_op1 unary_op_not
                  (expr_op2 binary_op_stx_eq
                   (expr_op1 unary_op_floor (expr_id "divided"))
                   (expr_id "divided"))) expr_false)))
              (expr_seq
               (expr_if
                (expr_if
                 (expr_op2 binary_op_stx_eq (expr_id "x")
                  (expr_number JsNumber.neg_infinity))
                 (expr_op2 binary_op_gt (expr_id "y")
                  (expr_number (JsNumber.of_int (0)))) expr_false)
                (expr_break "ret"
                 (expr_if (expr_app (expr_id "isOdd") [expr_id "y"])
                  (expr_number JsNumber.neg_infinity)
                  (expr_number JsNumber.infinity))) expr_null)
               (expr_seq
                (expr_if
                 (expr_if
                  (expr_op2 binary_op_stx_eq (expr_id "x")
                   (expr_number JsNumber.neg_infinity))
                  (expr_op2 binary_op_lt (expr_id "y")
                   (expr_number (JsNumber.of_int (0)))) expr_false)
                 (expr_break "ret" (expr_number (JsNumber.of_int (0))))
                 expr_null)
                (expr_seq
                 (expr_if
                  (expr_if
                   (expr_op2 binary_op_stx_eq (expr_id "x")
                    (expr_number (JsNumber.of_int (0))))
                   (expr_op2 binary_op_gt (expr_id "y")
                    (expr_number (JsNumber.of_int (0)))) expr_false)
                  (expr_break "ret" (expr_number (JsNumber.of_int (0))))
                  expr_null)
                 (expr_seq
                  (expr_if
                   (expr_if
                    (expr_op2 binary_op_stx_eq (expr_id "x")
                     (expr_number (JsNumber.of_int (0))))
                    (expr_op2 binary_op_lt (expr_id "y")
                     (expr_number (JsNumber.of_int (0)))) expr_false)
                   (expr_break "ret" (expr_number JsNumber.infinity))
                   expr_null)
                  (expr_seq
                   (expr_let "oddY"
                    (expr_app (expr_id "isOdd") [expr_id "y"])
                    (expr_if
                     (expr_if
                      (expr_if
                       (expr_op2 binary_op_stx_eq (expr_id "x")
                        (expr_number (JsNumber.of_int (0))))
                       (expr_op2 binary_op_lt (expr_id "y")
                        (expr_number (JsNumber.of_int (0)))) expr_false)
                      (expr_id "oddY") expr_false)
                     (expr_break "ret" (expr_number JsNumber.neg_infinity))
                     expr_null))
                   (expr_seq
                    (expr_if
                     (expr_if
                      (expr_op2 binary_op_stx_eq (expr_id "x")
                       (expr_number (JsNumber.of_int (0))))
                      (expr_op2 binary_op_lt (expr_id "y")
                       (expr_number (JsNumber.of_int (0)))) expr_false)
                     (expr_break "ret" (expr_number JsNumber.infinity))
                     expr_null)
                    (expr_seq
                     (expr_let "isFinite"
                      (expr_lambda ["n"]
                       (expr_if
                        (expr_op1 unary_op_not
                         (expr_op2 binary_op_stx_eq (expr_id "n")
                          (expr_number JsNumber.infinity)))
                        (expr_op1 unary_op_not
                         (expr_op2 binary_op_stx_eq (expr_id "n")
                          (expr_number JsNumber.neg_infinity))) expr_false))
                      (expr_let "finiteX"
                       (expr_app (expr_id "isFinite") [expr_id "x"])
                       (expr_let "finiteY"
                        (expr_app (expr_id "isFinite") [expr_id "y"])
                        (expr_if
                         (expr_if
                          (expr_if
                           (expr_if
                            (expr_op2 binary_op_lt (expr_id "x")
                             (expr_number (JsNumber.of_int (0))))
                            (expr_id "finiteX") expr_false)
                           (expr_id "finiteY") expr_false)
                          (expr_op1 unary_op_not
                           (expr_op2 binary_op_stx_eq
                            (expr_op1 unary_op_floor (expr_id "y"))
                            (expr_id "y"))) expr_false)
                         (expr_break "ret" (expr_number JsNumber.nan))
                         expr_null))))
                     (expr_break "ret"
                      (expr_op2 binary_op_pow (expr_id "x") (expr_id "y"))))))))))))))))))))))))
.
Definition ex_privmax := 
expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "b")
(expr_id "a")
.
Definition ex_privmin := 
expr_if (expr_op2 binary_op_le (expr_id "a") (expr_id "b")) (expr_id "a")
(expr_id "b")
.
Definition ex_privminMaxCall := 
expr_let "end"
(expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "end")
    (expr_number (JsNumber.of_int (0)))) (expr_break "ret" (expr_id "init"))
   expr_null)
  (expr_recc "loop"
   (expr_lambda ["best"; "i"]
    (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
     (expr_let "curr"
      (expr_app (expr_id "%ToNumber")
       [expr_get_attr pattr_value (expr_id "args")
        (expr_op1 unary_op_prim_to_str (expr_id "i"))])
      (expr_seq
       (expr_if
        (expr_op1 unary_op_not
         (expr_op2 binary_op_stx_eq (expr_id "curr") (expr_id "curr")))
        (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
       (expr_app (expr_id "loop")
        [expr_app (expr_id "op") [expr_id "best"; expr_id "curr"];
         expr_op2 binary_op_add (expr_id "i")
         (expr_number (JsNumber.of_int (1)))]))) (expr_id "best")))
   (expr_break "ret"
    (expr_app (expr_id "loop")
     [expr_id "init"; expr_number (JsNumber.of_int (0))])))))
.
Definition ex_privmkArgsObj := 
expr_let "argsObj"
(expr_object
 (objattrs_intro (expr_string "Arguments") expr_true (expr_id "%ObjectProto")
  expr_undefined) [] [])
(expr_seq
 (expr_if (expr_id "strict")
  (expr_seq
   (expr_app (expr_id "%AddAccessorField")
    [expr_id "argsObj";
     expr_string "callee";
     expr_id "%ThrowTypeError";
     expr_id "%ThrowTypeError";
     expr_false;
     expr_false])
   (expr_app (expr_id "%AddAccessorField")
    [expr_id "argsObj";
     expr_string "caller";
     expr_id "%ThrowTypeError";
     expr_id "%ThrowTypeError";
     expr_false;
     expr_false]))
  (expr_app (expr_id "%AddDataField")
   [expr_id "argsObj";
    expr_string "callee";
    expr_id "obj";
    expr_true;
    expr_false;
    expr_true]))
 (expr_recc "loop"
  (expr_lambda ["iter"]
   (expr_let "strx" (expr_op1 unary_op_prim_to_str (expr_id "iter"))
    (expr_if
     (expr_op2 binary_op_has_own_property (expr_id "args") (expr_id "strx"))
     (expr_seq
      (expr_set_attr pattr_value (expr_id "argsObj") (expr_id "strx")
       (expr_get_attr pattr_value (expr_id "args") (expr_id "strx")))
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "iter")
        (expr_number (JsNumber.of_int (1)))]))
     (expr_seq
      (expr_set_attr pattr_value (expr_id "argsObj") (expr_string "length")
       (expr_id "iter"))
      (expr_set_attr pattr_enum (expr_id "argsObj") (expr_string "length")
       expr_false)))))
  (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
   (expr_id "argsObj"))))
.
Definition ex_privnewDeclEnvRec := 
expr_object
(objattrs_intro (expr_string "DeclEnvRec") expr_true expr_null expr_undefined)
[("parent", expr_id "parent")] []
.
Definition ex_privnewObjEnvRec := 
expr_object
(objattrs_intro (expr_string "ObjEnvRec") expr_true expr_null expr_undefined)
[("parent", expr_id "parent");
 ("bindings", expr_id "obj");
 ("provideThis", expr_id "pt")] []
.
Definition ex_privnotEqEq := 
expr_op1 unary_op_not
(expr_app (expr_id "%EqEq") [expr_id "x1"; expr_id "x2"])
.
Definition ex_privnotStxEq := 
expr_op1 unary_op_not
(expr_app (expr_id "%StxEq") [expr_id "x1"; expr_id "x2"])
.
Definition ex_privnumTLSCall := 
expr_let "x"
(expr_if
 (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
  (expr_string "number")) (expr_id "this")
 (expr_get_internal "primval" (expr_id "this")))
(expr_let "obj"
 (expr_object
  (objattrs_intro (expr_string "Object") expr_true (expr_id "%StringProto")
   expr_undefined) [("primval", expr_op1 unary_op_prim_to_str (expr_id "x"))]
  [])
 (expr_app (expr_id "%toLocaleString")
  [expr_id "obj";
   expr_object
   (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
   [] []]))
.
Definition ex_privnumToStringAbstract := 
expr_recc "nts"
(expr_lambda ["n"; "r"]
 (expr_label "ret"
  (expr_seq
   (expr_if
    (expr_op1 unary_op_not
     (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")))
    (expr_break "ret" (expr_string "NaN")) expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "n")
      (expr_number (JsNumber.of_int (0))))
     (expr_break "ret" (expr_string "0")) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_lt (expr_id "n")
       (expr_number (JsNumber.of_int (0))))
      (expr_break "ret"
       (expr_op2 binary_op_string_plus (expr_string "-")
        (expr_app (expr_id "nts")
         [expr_op1 unary_op_neg (expr_id "n"); expr_id "r"]))) expr_null)
     (expr_seq
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "n")
        (expr_number JsNumber.infinity))
       (expr_break "ret" (expr_string "Infinity")) expr_null)
      (expr_seq
       (expr_if
        (expr_op2 binary_op_stx_eq (expr_id "r")
         (expr_number (JsNumber.of_int (10))))
        (expr_break "ret" (expr_op1 unary_op_prim_to_str (expr_id "n")))
        expr_null)
       (expr_break "ret"
        (expr_op2 binary_op_base (expr_id "n") (expr_id "r"))))))))))
(expr_app (expr_id "nts") [expr_id "n"; expr_id "r"])
.
Definition ex_privnumberPrimval := 
expr_if
(expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
 (expr_string "number")) (expr_id "this")
(expr_if
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "this"))
   (expr_string "object"))
  (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_class (expr_id "this"))
   (expr_string "Number")) expr_false)
 (expr_get_internal "primval" (expr_id "this"))
 (expr_app (expr_id "%TypeError") [expr_string "not a number"]))
.
Definition ex_privnumberToStringCall := 
expr_let "val" (expr_app (expr_id "%numberPrimval") [expr_id "this"])
(expr_let "rint"
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   expr_undefined) (expr_number (JsNumber.of_int (10)))
  (expr_app (expr_id "%ToInteger")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")]))
 (expr_if
  (expr_if
   (expr_op2 binary_op_lt (expr_id "rint")
    (expr_number (JsNumber.of_int (2)))) expr_true
   (expr_op2 binary_op_gt (expr_id "rint")
    (expr_number (JsNumber.of_int (36)))))
  (expr_app (expr_id "%RangeError")
   [expr_string "Number.toString received invalid radix"])
  (expr_app (expr_id "%numToStringAbstract") [expr_id "val"; expr_id "rint"])))
.
Definition ex_privobjectToStringCall := 
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
Definition ex_privobjectValueOfCall := 
expr_app (expr_id "%ToObject") [expr_id "this"]
.
Definition ex_privoneArgObj := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined) 
[]
[("0", property_data
       (data_intro (expr_id "arg") expr_false expr_false expr_false))]
.
Definition ex_privparse :=  expr_number (JsNumber.of_int (0)) .
Definition ex_privparseFloatCall :=  expr_string "parseFloat NYI" .
Definition ex_privparseIntCall := 
expr_let "numstr"
(expr_app (expr_id "%ToString")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_op1 unary_op_prim_to_num (expr_id "numstr"))
.
Definition ex_privpopCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "len")
    (expr_number (JsNumber.of_int (0))))
   (expr_seq
    (expr_app (expr_id "%Put1")
     [expr_id "O";
      expr_string "length";
      expr_number (JsNumber.of_int (0));
      expr_true]) expr_undefined)
   (expr_let "indx"
    (expr_app (expr_id "%ToString")
     [expr_op2 binary_op_sub (expr_id "len")
      (expr_number (JsNumber.of_int (1)))])
    (expr_let "element"
     (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "indx"])
     (expr_seq
      (expr_app (expr_id "%Delete") [expr_id "O"; expr_id "indx"; expr_false])
      (expr_seq
       (expr_app (expr_id "%Put1")
        [expr_id "O";
         expr_string "length";
         expr_app (expr_id "%ToNumber") [expr_id "indx"];
         expr_true]) (expr_id "element"))))))))
.
Definition ex_privpreventExtensionsCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
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
     [expr_app (expr_id "%Get1") [expr_id "arr"; expr_id "istr"]])
    (expr_app (expr_id "loop")
     [expr_op2 binary_op_add (expr_id "i")
      (expr_number (JsNumber.of_int (1)))])) expr_undefined)))
(expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
.
Definition ex_privprintCall := 
expr_op1 unary_op_print
(expr_app (expr_id "%ToString")
 [expr_get_attr pattr_value (expr_id "s") (expr_string "0")])
.
Definition ex_privpropEnumCall := 
expr_let "getOwnProperty"
(expr_lambda ["o"; "f"]
 (expr_if (expr_op2 binary_op_has_own_property (expr_id "o") (expr_id "f"))
  (expr_app (expr_id "%Get1") [expr_id "o"; expr_id "f"]) expr_undefined))
(expr_if
 (expr_op2 binary_op_stx_eq
  (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
  expr_undefined) expr_false
 (expr_let "P"
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
   (expr_let "desc"
    (expr_app (expr_id "getOwnProperty") [expr_id "O"; expr_id "P"])
    (expr_if (expr_op2 binary_op_stx_eq (expr_id "desc") expr_undefined)
     expr_false (expr_get_attr pattr_enum (expr_id "O") (expr_id "P")))))))
.
Definition ex_privpropertyNames := 
expr_let "aux"
(expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
 [] [])
(expr_recc "helper"
 (expr_lambda ["obj"]
  (expr_if (expr_op2 binary_op_stx_eq (expr_id "obj") expr_null)
   expr_undefined
   (expr_seq
    (expr_let "cur" (expr_own_field_names (expr_id "obj"))
     (expr_let "length"
      (expr_get_attr pattr_value (expr_id "cur") (expr_string "length"))
      (expr_recc "loop"
       (expr_lambda ["i"]
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "length"))
         (expr_let "istr" (expr_op1 unary_op_prim_to_str (expr_id "i"))
          (expr_seq
           (expr_if
            (expr_if
             (expr_get_attr pattr_enum (expr_id "obj")
              (expr_get_attr pattr_value (expr_id "cur") (expr_id "istr")))
             expr_true (expr_id "get-non-enumerable"))
            (expr_set_attr pattr_value (expr_id "aux")
             (expr_get_attr pattr_value (expr_id "cur") (expr_id "istr"))
             expr_true) expr_undefined)
           (expr_app (expr_id "loop")
            [expr_op2 binary_op_add (expr_id "i")
             (expr_number (JsNumber.of_int (1)))]))) expr_undefined))
       (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))]))))
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
Definition ex_privpushCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_recc "loop"
   (expr_lambda ["i"; "n"]
    (expr_if
     (expr_op2 binary_op_lt (expr_id "i")
      (expr_get_attr pattr_value (expr_id "args") (expr_string "length")))
     (expr_seq
      (expr_let "ii" (expr_op1 unary_op_prim_to_str (expr_id "i"))
       (expr_app (expr_id "%SetField")
        [expr_id "O";
         expr_app (expr_id "%ToString") [expr_id "n"];
         expr_get_attr pattr_value (expr_id "args") (expr_id "ii")]))
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int (1)));
        expr_op2 binary_op_add (expr_id "n")
        (expr_number (JsNumber.of_int (1)))])) (expr_id "n")))
   (expr_app (expr_id "loop")
    [expr_number (JsNumber.of_int (0)); expr_id "len"]))))
.
Definition ex_privrandomCall :=  expr_number (JsNumber.of_int (4)) .
Definition ex_privreduceCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_let "has_initial"
    (expr_op2 binary_op_ge
     (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
     (expr_number (JsNumber.of_int (2))))
    (expr_label "ret"
     (expr_seq
      (expr_if
       (expr_op1 unary_op_not
        (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
       (expr_app (expr_id "%TypeError")
        [expr_string "Callback not a function in reduce"]) expr_null)
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "len")
          (expr_number (JsNumber.of_int (0))))
         (expr_op1 unary_op_not (expr_id "has_initial")) expr_false)
        (expr_app (expr_id "%TypeError")
         [expr_string "Reducing an empty list with not enough arguments."])
        expr_null)
       (expr_let "origK"
        (expr_if (expr_id "has_initial")
         (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1))))
         (expr_recc "accumLoop"
          (expr_lambda ["k"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_let "kPresent"
              (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
              (expr_if (expr_id "kPresent") (expr_id "k")
               (expr_app (expr_id "accumLoop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)))]))))
            (expr_app (expr_id "%TypeError") [expr_string "In Array reduce"])))
          (expr_app (expr_id "accumLoop") [expr_number (JsNumber.of_int (0))])))
        (expr_let "accumulator"
         (expr_if (expr_id "has_initial")
          (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
          (expr_app (expr_id "%Get1")
           [expr_id "O"; expr_app (expr_id "%ToString") [expr_id "origK"]]))
         (expr_recc "outerLoop"
          (expr_lambda ["k"; "accumulator"]
           (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_let "kPresent"
              (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
              (expr_if (expr_id "kPresent")
               (expr_let "kValue"
                (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
                (expr_let "argsObj"
                 (expr_object
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_undefined) [] [])
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "0") (expr_id "accumulator"))
                  (expr_seq
                   (expr_set_attr pattr_value (expr_id "argsObj")
                    (expr_string "1") (expr_id "kValue"))
                   (expr_seq
                    (expr_set_attr pattr_value (expr_id "argsObj")
                     (expr_string "2") (expr_id "k"))
                    (expr_seq
                     (expr_set_attr pattr_value (expr_id "argsObj")
                      (expr_string "3") (expr_id "O"))
                     (expr_seq
                      (expr_set_attr pattr_value (expr_id "argsObj")
                       (expr_string "length")
                       (expr_number (JsNumber.of_int (4))))
                      (expr_let "next"
                       (expr_app (expr_id "callbackfn")
                        [expr_undefined; expr_id "argsObj"])
                       (expr_app (expr_id "outerLoop")
                        [expr_op2 binary_op_add (expr_id "k")
                         (expr_number (JsNumber.of_int (1)));
                         expr_id "next"])))))))))
               (expr_app (expr_id "outerLoop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)));
                 expr_id "accumulator"])))) (expr_id "accumulator")))
          (expr_break "ret"
           (expr_app (expr_id "outerLoop")
            [expr_op2 binary_op_add (expr_id "origK")
             (expr_number (JsNumber.of_int (1)));
             expr_id "accumulator"]))))))))))))
.
Definition ex_privreduceRightCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_let "has_initial"
    (expr_op2 binary_op_ge
     (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
     (expr_number (JsNumber.of_int (2))))
    (expr_label "ret"
     (expr_seq
      (expr_if
       (expr_op1 unary_op_not
        (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
       (expr_app (expr_id "%TypeError")
        [expr_string "Callback not function in reduceRight"]) expr_null)
      (expr_seq
       (expr_if
        (expr_if
         (expr_op2 binary_op_stx_eq (expr_id "len")
          (expr_number (JsNumber.of_int (0))))
         (expr_op1 unary_op_not (expr_id "has_initial")) expr_false)
        (expr_app (expr_id "%TypeError")
         [expr_string "Zero-length array in reduceRight"]) expr_null)
       (expr_let "origK"
        (expr_if (expr_id "has_initial") (expr_id "len")
         (expr_recc "accumLoop"
          (expr_lambda ["k"]
           (expr_if
            (expr_op2 binary_op_ge (expr_id "k")
             (expr_number (JsNumber.of_int (0))))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_let "kPresent"
              (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
              (expr_if (expr_id "kPresent") (expr_id "k")
               (expr_app (expr_id "accumLoop")
                [expr_op2 binary_op_sub (expr_id "k")
                 (expr_number (JsNumber.of_int (1)))]))))
            (expr_app (expr_id "%TypeError") [expr_string "reduceRight"])))
          (expr_app (expr_id "accumLoop")
           [expr_op2 binary_op_sub (expr_id "len")
            (expr_number (JsNumber.of_int (1)))])))
        (expr_let "accumulator"
         (expr_if (expr_id "has_initial")
          (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
          (expr_app (expr_id "%Get1")
           [expr_id "O"; expr_app (expr_id "%ToString") [expr_id "origK"]]))
         (expr_recc "outerLoop"
          (expr_lambda ["k"; "accumulator"]
           (expr_if
            (expr_op2 binary_op_ge (expr_id "k")
             (expr_number (JsNumber.of_int (0))))
            (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
             (expr_let "kPresent"
              (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
              (expr_if (expr_id "kPresent")
               (expr_let "kValue"
                (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
                (expr_let "argsObj"
                 (expr_object
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_undefined) [] [])
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "0") (expr_id "accumulator"))
                  (expr_seq
                   (expr_set_attr pattr_value (expr_id "argsObj")
                    (expr_string "1") (expr_id "kValue"))
                   (expr_seq
                    (expr_set_attr pattr_value (expr_id "argsObj")
                     (expr_string "2") (expr_id "k"))
                    (expr_seq
                     (expr_set_attr pattr_value (expr_id "argsObj")
                      (expr_string "3") (expr_id "O"))
                     (expr_seq
                      (expr_set_attr pattr_value (expr_id "argsObj")
                       (expr_string "length")
                       (expr_number (JsNumber.of_int (4))))
                      (expr_let "next"
                       (expr_app (expr_id "callbackfn")
                        [expr_undefined; expr_id "argsObj"])
                       (expr_app (expr_id "outerLoop")
                        [expr_op2 binary_op_sub (expr_id "k")
                         (expr_number (JsNumber.of_int (1)));
                         expr_id "next"])))))))))
               (expr_app (expr_id "outerLoop")
                [expr_op2 binary_op_sub (expr_id "k")
                 (expr_number (JsNumber.of_int (1)));
                 expr_id "accumulator"])))) (expr_id "accumulator")))
          (expr_break "ret"
           (expr_app (expr_id "outerLoop")
            [expr_op2 binary_op_sub (expr_id "origK")
             (expr_number (JsNumber.of_int (1)));
             expr_id "accumulator"]))))))))))))
.
Definition ex_privreplaceCall := 
expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
(expr_let "search"
 (expr_app (expr_id "%ToString")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 (expr_let "replace"
  (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
  (expr_if
   (expr_op1 unary_op_not
    (expr_app (expr_id "%IsCallable") [expr_id "replace"]))
   (expr_throw (expr_string "String.replace() only supports functions"))
   (expr_recc "loop"
    (expr_lambda ["str"]
     (expr_let "start"
      (expr_app (expr_id "%stringIndexOf")
       [expr_id "str"; expr_app (expr_id "%oneArgObj") [expr_id "search"]])
      (expr_if
       (expr_op2 binary_op_stx_eq (expr_id "start")
        (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
       (expr_id "str")
       (expr_let "replaced"
        (expr_app (expr_id "%ToString")
         [expr_app (expr_id "replace")
          [expr_undefined;
           expr_app (expr_id "%oneArgObj") [expr_id "replace"]]])
        (expr_let "before"
         (expr_app (expr_id "%substring")
          [expr_id "str";
           expr_app (expr_id "%twoArgObj")
           [expr_number (JsNumber.of_int (0)); expr_id "start"]])
         (expr_let "afterix"
          (expr_op2 binary_op_add (expr_id "start")
           (expr_op1 unary_op_strlen (expr_id "search")))
          (expr_let "after"
           (expr_app (expr_id "%substring")
            [expr_id "str";
             expr_app (expr_id "%oneArgObj") [expr_id "afterix"]])
           (expr_op2 binary_op_string_plus (expr_id "before")
            (expr_op2 binary_op_string_plus (expr_id "replaced")
             (expr_app (expr_id "loop") [expr_id "after"]))))))))))
    (expr_app (expr_id "loop") [expr_id "S"])))))
.
Definition ex_privresolveThis := 
expr_if (expr_id "strict") (expr_id "obj")
(expr_if
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "obj") expr_null) expr_true
  (expr_op2 binary_op_stx_eq (expr_id "obj") expr_undefined))
 (expr_id "%global")
 (expr_if
  (expr_op2 binary_op_stx_eq (expr_op1 unary_op_typeof (expr_id "obj"))
   (expr_string "object")) (expr_id "obj")
  (expr_app (expr_id "%ToObject") [expr_id "obj"])))
.
Definition ex_privreverseCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "middle"
   (expr_op1 unary_op_floor
    (expr_op2 binary_op_div (expr_id "len")
     (expr_number (JsNumber.of_int (2)))))
   (expr_recc "loop"
    (expr_lambda ["lower"]
     (expr_if
      (expr_op1 unary_op_not
       (expr_op2 binary_op_stx_eq (expr_id "lower") (expr_id "middle")))
      (expr_label "ret"
       (expr_let "upper"
        (expr_op2 binary_op_sub
         (expr_op2 binary_op_sub (expr_id "len") (expr_id "lower"))
         (expr_number (JsNumber.of_int (1))))
        (expr_let "upperP" (expr_app (expr_id "%ToString") [expr_id "upper"])
         (expr_let "lowerP"
          (expr_app (expr_id "%ToString") [expr_id "lower"])
          (expr_let "lowerValue"
           (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "lowerP"])
           (expr_let "upperValue"
            (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "upperP"])
            (expr_let "lowerExists"
             (expr_app (expr_id "%HasProperty")
              [expr_id "O"; expr_id "lowerP"])
             (expr_let "upperExists"
              (expr_app (expr_id "%HasProperty")
               [expr_id "O"; expr_id "upperP"])
              (expr_seq
               (expr_if
                (expr_if (expr_id "lowerExists") (expr_id "upperExists")
                 expr_false)
                (expr_seq
                 (expr_app (expr_id "%Put1")
                  [expr_id "O";
                   expr_id "lowerP";
                   expr_id "upperValue";
                   expr_true])
                 (expr_seq
                  (expr_app (expr_id "%Put1")
                   [expr_id "O";
                    expr_id "upperP";
                    expr_id "lowerValue";
                    expr_true])
                  (expr_break "ret"
                   (expr_app (expr_id "loop")
                    [expr_op2 binary_op_add (expr_id "lower")
                     (expr_number (JsNumber.of_int (1)))])))) expr_null)
               (expr_seq
                (expr_if (expr_id "upperExists")
                 (expr_seq
                  (expr_app (expr_id "%Put1")
                   [expr_id "O";
                    expr_id "lowerP";
                    expr_id "upperValue";
                    expr_true])
                  (expr_seq
                   (expr_app (expr_id "%Delete")
                    [expr_id "O"; expr_id "upperP"; expr_false])
                   (expr_break "ret"
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "lower")
                      (expr_number (JsNumber.of_int (1)))])))) expr_null)
                (expr_seq
                 (expr_if (expr_id "lowerExists")
                  (expr_seq
                   (expr_app (expr_id "%Delete")
                    [expr_id "O"; expr_id "lowerP"; expr_false])
                   (expr_seq
                    (expr_app (expr_id "%Put1")
                     [expr_id "O";
                      expr_id "upperP";
                      expr_id "lowerValue";
                      expr_true])
                    (expr_break "ret"
                     (expr_app (expr_id "loop")
                      [expr_op2 binary_op_add (expr_id "lower")
                       (expr_number (JsNumber.of_int (1)))])))) expr_null)
                 (expr_break "ret"
                  (expr_app (expr_id "loop")
                   [expr_op2 binary_op_add (expr_id "lower")
                    (expr_number (JsNumber.of_int (1)))])))))))))))))
      expr_undefined))
    (expr_seq (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])
     (expr_id "O"))))))
.
Definition ex_privroundCall :=  expr_string "round NYI" .
Definition ex_privrunConstruct := 
expr_app (expr_get_internal "construct" (expr_id "constr"))
[expr_id "constr"; expr_id "args"]
.
Definition ex_privsealCall := 
expr_let "O" (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_seq (expr_app (expr_id "%ObjectTypeCheck") [expr_id "O"])
 (expr_seq
  (expr_let "names" (expr_own_field_names (expr_id "O"))
   (expr_let "len"
    (expr_get_attr pattr_value (expr_id "names") (expr_string "length"))
    (expr_recc "loop"
     (expr_lambda ["i"]
      (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
       (expr_seq
        (expr_let "name"
         (expr_get_attr pattr_value (expr_id "names")
          (expr_op1 unary_op_prim_to_str (expr_id "i")))
         (expr_set_attr pattr_config (expr_id "O") (expr_id "name")
          expr_false))
        (expr_app (expr_id "loop")
         [expr_op2 binary_op_add (expr_id "i")
          (expr_number (JsNumber.of_int (1)))])) expr_null))
     (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))]))))
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
        (expr_op1 unary_op_not
         (expr_op2 binary_op_stx_eq (expr_id "uint")
          (expr_number (JsNumber.of_int (4294967295))))) expr_false)))
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
             (expr_op1 unary_op_not
              (expr_op2 binary_op_stx_eq (expr_id "newLen")
               (expr_id "toCompare")))
             (expr_throw
              (expr_app (expr_id "%JSError")
               [expr_object
                (objattrs_intro (expr_string "Object") expr_true
                 (expr_id "%RangeErrorProto") expr_undefined) [] []]))
             (expr_if
              (expr_op2 binary_op_lt (expr_id "newLen")
               (expr_app (expr_id "%Get1")
                [expr_id "obj"; expr_string "length"]))
              (expr_app (expr_id "%ArrayLengthChange")
               [expr_id "obj"; expr_id "newLen"]) expr_undefined))))
          expr_undefined))
        (expr_seq (expr_app (expr_id "lenCheck") [])
         (expr_seq
          (expr_app (expr_id "%Put1")
           [expr_id "obj";
            expr_id "fld";
            expr_if
            (expr_op2 binary_op_stx_eq (expr_id "fld") (expr_string "length"))
            (expr_app (expr_id "%ToUint32") [expr_id "val"]) (expr_id "val");
            expr_true])
          (expr_if (expr_app (expr_id "isArrayIndex") [])
           (expr_let "uint" (expr_app (expr_id "%ToUint32") [expr_id "fld"])
            (expr_let "len"
             (expr_app (expr_id "%Get1")
              [expr_id "obj"; expr_string "length"])
             (expr_if
              (expr_op2 binary_op_lt (expr_id "len")
               (expr_op2 binary_op_add (expr_id "uint")
                (expr_number (JsNumber.of_int (1)))))
              (expr_app (expr_id "%Put1")
               [expr_id "obj";
                expr_string "length";
                expr_op2 binary_op_add (expr_id "uint")
                (expr_number (JsNumber.of_int (1)));
                expr_true]) expr_undefined))) expr_undefined)))))
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_obj_attr oattr_class (expr_id "obj")) (expr_string "Array"))
       (expr_app (expr_id "setArrayField") [])
       (expr_app (expr_id "%Put1")
        [expr_id "obj"; expr_id "fld"; expr_id "val"; expr_true]))))))))
.
Definition ex_privshiftCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_if
   (expr_op2 binary_op_stx_eq (expr_id "len")
    (expr_number (JsNumber.of_int (0))))
   (expr_seq
    (expr_app (expr_id "%Put1")
     [expr_id "O";
      expr_string "length";
      expr_number (JsNumber.of_int (0));
      expr_true]) expr_undefined)
   (expr_let "first"
    (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "0"])
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
             (expr_number (JsNumber.of_int (1)))])
           (expr_let "fromPresent"
            (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "from"])
            (expr_if (expr_id "fromPresent")
             (expr_seq
              (expr_let "fromVal"
               (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "from"])
               (expr_app (expr_id "%Put1")
                [expr_id "O"; expr_id "to"; expr_id "fromVal"; expr_true]))
              (expr_break "ret"
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)))])))
             (expr_seq
              (expr_app (expr_id "%Delete")
               [expr_id "O"; expr_id "to"; expr_false])
              (expr_break "ret"
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)))]))))))))))
      (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (1))]))
     (expr_let "newLen"
      (expr_op2 binary_op_sub (expr_id "len")
       (expr_number (JsNumber.of_int (1))))
      (expr_seq
       (expr_app (expr_id "%Delete")
        [expr_id "O";
         expr_app (expr_id "%ToString") [expr_id "newLen"];
         expr_false])
       (expr_seq
        (expr_app (expr_id "%Put1")
         [expr_id "O"; expr_string "length"; expr_id "newLen"; expr_true])
        (expr_id "first")))))))))
.
Definition ex_privsinCall := 
expr_let "n"
(expr_app (expr_id "%ToNumber")
 [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
(expr_label "ret"
 (expr_seq
  (expr_if
   (expr_op1 unary_op_not
    (expr_op2 binary_op_stx_eq (expr_id "n") (expr_id "n")))
   (expr_break "ret" (expr_id "n")) expr_null)
  (expr_seq
   (expr_if
    (expr_op2 binary_op_stx_eq (expr_id "n")
     (expr_number (JsNumber.of_int (0)))) (expr_break "ret" (expr_id "n"))
    expr_null)
   (expr_seq
    (expr_if
     (expr_op2 binary_op_stx_eq (expr_id "n") (expr_number JsNumber.infinity))
     (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
    (expr_seq
     (expr_if
      (expr_op2 binary_op_stx_eq (expr_id "n")
       (expr_number JsNumber.neg_infinity))
      (expr_break "ret" (expr_number JsNumber.nan)) expr_null)
     (expr_break "ret" (expr_op1 unary_op_sin (expr_id "n"))))))))
.
Definition ex_privsliceCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "A"
 (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
 (expr_let "lenVal"
  (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
  (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
   (expr_let "relativeStart"
    (expr_app (expr_id "%ToInteger")
     [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
    (expr_let "initk"
     (expr_if
      (expr_op2 binary_op_lt (expr_id "relativeStart")
       (expr_number (JsNumber.of_int (0))))
      (expr_let "added"
       (expr_op2 binary_op_add (expr_id "len") (expr_id "relativeStart"))
       (expr_if
        (expr_op2 binary_op_gt (expr_id "added")
         (expr_number (JsNumber.of_int (0)))) (expr_id "added")
        (expr_number (JsNumber.of_int (0)))))
      (expr_if
       (expr_op2 binary_op_lt (expr_id "relativeStart") (expr_id "len"))
       (expr_id "relativeStart") (expr_id "len")))
     (expr_let "relativeEnd"
      (expr_if
       (expr_op2 binary_op_stx_eq
        (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
        expr_undefined) (expr_id "len")
       (expr_app (expr_id "%ToInteger")
        [expr_get_attr pattr_value (expr_id "args") (expr_string "1")]))
      (expr_let "final"
       (expr_if
        (expr_op2 binary_op_lt (expr_id "relativeEnd")
         (expr_number (JsNumber.of_int (0))))
        (expr_let "added"
         (expr_op2 binary_op_add (expr_id "len") (expr_id "relativeEnd"))
         (expr_if
          (expr_op2 binary_op_gt (expr_id "added")
           (expr_number (JsNumber.of_int (0)))) (expr_id "added")
          (expr_number (JsNumber.of_int (0)))))
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
             (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
             (expr_if (expr_id "kPresent")
              (expr_seq
               (expr_let "kValue"
                (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
                (expr_app (expr_id "%defineOwnProperty")
                 [expr_id "A";
                  expr_app (expr_id "%ToString") [expr_id "n"];
                  expr_object
                  (objattrs_intro (expr_string "Object") expr_true expr_null
                   expr_undefined) []
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
                  (expr_number (JsNumber.of_int (1)));
                  expr_op2 binary_op_add (expr_id "k")
                  (expr_number (JsNumber.of_int (1)));
                  expr_op2 binary_op_add (expr_id "finalLen")
                  (expr_number (JsNumber.of_int (1)))])))
              (expr_break "ret"
               (expr_app (expr_id "loop")
                [expr_op2 binary_op_add (expr_id "n")
                 (expr_number (JsNumber.of_int (1)));
                 expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)));
                 expr_op2 binary_op_add (expr_id "finalLen")
                 (expr_number (JsNumber.of_int (1)))]))))))))
        (expr_seq
         (expr_set_attr pattr_value (expr_id "A") (expr_string "length")
          (expr_app (expr_id "loop")
           [expr_number (JsNumber.of_int (0));
            expr_id "initk";
            expr_number (JsNumber.of_int (0))])) (expr_id "A"))))))))))
.
Definition ex_privslice_internal := 
expr_let "retObj"
(expr_object
 (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
 [] [])
(expr_seq
 (expr_recc "inner_slice"
  (expr_lambda ["iter"; "ix"]
   (expr_if
    (expr_op2 binary_op_has_own_property (expr_id "list")
     (expr_op1 unary_op_prim_to_str (expr_id "iter")))
    (expr_seq
     (expr_set_attr pattr_value (expr_id "retObj")
      (expr_op1 unary_op_prim_to_str (expr_id "ix"))
      (expr_get_attr pattr_value (expr_id "list")
       (expr_op1 unary_op_prim_to_str (expr_id "iter"))))
     (expr_if (expr_op2 binary_op_gt (expr_id "iter") (expr_id "max"))
      expr_undefined
      (expr_app (expr_id "inner_slice")
       [expr_op2 binary_op_add (expr_id "iter")
        (expr_number (JsNumber.of_int (1)));
        expr_op2 binary_op_add (expr_id "ix")
        (expr_number (JsNumber.of_int (1)))])))
    (expr_set_attr pattr_value (expr_id "retObj") (expr_string "length")
     (expr_id "ix"))))
  (expr_app (expr_id "inner_slice")
   [expr_id "min"; expr_number (JsNumber.of_int (0))])) (expr_id "retObj"))
.
Definition ex_privsomeCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenValue"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenValue"])
  (expr_let "callbackfn"
   (expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
   (expr_label "ret"
    (expr_seq
     (expr_if
      (expr_op1 unary_op_not
       (expr_app (expr_id "%IsCallable") [expr_id "callbackfn"]))
      (expr_app (expr_id "%TypeError")
       [expr_string "Callback not function in some"]) expr_null)
     (expr_let "T"
      (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
      (expr_recc "loop"
       (expr_lambda ["k"]
        (expr_if (expr_op2 binary_op_lt (expr_id "k") (expr_id "len"))
         (expr_let "Pk" (expr_app (expr_id "%ToString") [expr_id "k"])
          (expr_let "kPresent"
           (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "Pk"])
           (expr_if (expr_id "kPresent")
            (expr_let "kValue"
             (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "Pk"])
             (expr_let "argsObj"
              (expr_object
               (objattrs_intro (expr_string "Object") expr_true expr_null
                expr_undefined) [] [])
              (expr_seq
               (expr_set_attr pattr_value (expr_id "argsObj")
                (expr_string "0") (expr_id "kValue"))
               (expr_seq
                (expr_set_attr pattr_value (expr_id "argsObj")
                 (expr_string "1") (expr_id "k"))
                (expr_seq
                 (expr_set_attr pattr_value (expr_id "argsObj")
                  (expr_string "2") (expr_id "O"))
                 (expr_seq
                  (expr_set_attr pattr_value (expr_id "argsObj")
                   (expr_string "length") (expr_number (JsNumber.of_int (3))))
                  (expr_let "testResult"
                   (expr_app (expr_id "callbackfn")
                    [expr_id "T"; expr_id "argsObj"])
                   (expr_if
                    (expr_op2 binary_op_stx_eq
                     (expr_app (expr_id "%ToBoolean") [expr_id "testResult"])
                     expr_true) expr_true
                    (expr_app (expr_id "loop")
                     [expr_op2 binary_op_add (expr_id "k")
                      (expr_number (JsNumber.of_int (1)))])))))))))
            (expr_app (expr_id "loop")
             [expr_op2 binary_op_add (expr_id "k")
              (expr_number (JsNumber.of_int (1)))])))) expr_false))
       (expr_break "ret"
        (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))])))))))))
.
Definition ex_privsortCall := 
expr_let "obj" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "sortCompare"
 (expr_lambda ["j"; "k"]
  (expr_let "jString" (expr_app (expr_id "%ToString") [expr_id "j"])
   (expr_let "kString" (expr_app (expr_id "%ToString") [expr_id "k"])
    (expr_let "hasj"
     (expr_app (expr_id "%HasProperty") [expr_id "obj"; expr_id "jString"])
     (expr_let "hask"
      (expr_app (expr_id "%HasProperty") [expr_id "obj"; expr_id "kString"])
      (expr_label "ret"
       (expr_seq
        (expr_if
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "hasj") expr_false)
          (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false) expr_false)
         (expr_break "ret" (expr_number (JsNumber.of_int (0)))) expr_null)
        (expr_seq
         (expr_if (expr_op2 binary_op_stx_eq (expr_id "hasj") expr_false)
          (expr_break "ret" (expr_number (JsNumber.of_int (1)))) expr_null)
         (expr_seq
          (expr_if (expr_op2 binary_op_stx_eq (expr_id "hask") expr_false)
           (expr_break "ret"
            (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
           expr_null)
          (expr_let "x"
           (expr_app (expr_id "%Get1") [expr_id "obj"; expr_id "jString"])
           (expr_let "y"
            (expr_app (expr_id "%Get1") [expr_id "obj"; expr_id "kString"])
            (expr_seq
             (expr_if
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
               (expr_op2 binary_op_stx_eq (expr_id "y") expr_undefined)
               expr_false)
              (expr_break "ret" (expr_number (JsNumber.of_int (0))))
              expr_null)
             (expr_seq
              (expr_if
               (expr_op2 binary_op_stx_eq (expr_id "x") expr_undefined)
               (expr_break "ret" (expr_number (JsNumber.of_int (1))))
               expr_null)
              (expr_seq
               (expr_if
                (expr_op2 binary_op_stx_eq (expr_id "y") expr_undefined)
                (expr_break "ret"
                 (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1)))))
                expr_null)
               (expr_seq
                (expr_if
                 (expr_op1 unary_op_not
                  (expr_op2 binary_op_stx_eq
                   (expr_get_attr pattr_value (expr_id "args")
                    (expr_string "0")) expr_undefined))
                 (expr_seq
                  (expr_if
                   (expr_op1 unary_op_not
                    (expr_app (expr_id "%IsCallable")
                     [expr_get_attr pattr_value (expr_id "args")
                      (expr_string "0")]))
                   (expr_throw
                    (expr_app (expr_id "%JSError")
                     [expr_object
                      (objattrs_intro (expr_string "Object") expr_true
                       (expr_id "%TypeErrorProto") expr_undefined) [] 
                      []])) expr_null)
                  (expr_break "ret"
                   (expr_app
                    (expr_get_attr pattr_value (expr_id "args")
                     (expr_string "0"))
                    [expr_undefined;
                     expr_object
                     (objattrs_intro (expr_string "Object") expr_true
                      expr_null expr_undefined) []
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
                     (expr_op1 unary_op_neg
                      (expr_number (JsNumber.of_int (1))))) expr_null)
                   (expr_seq
                    (expr_if
                     (expr_op2 binary_op_string_lt (expr_id "yString")
                      (expr_id "xString"))
                     (expr_break "ret" (expr_number (JsNumber.of_int (1))))
                     expr_null)
                    (expr_break "ret" (expr_number (JsNumber.of_int (0)))))))))))))))))))))))
 (expr_let "insert"
  (expr_lambda ["elt"; "before"]
   (expr_recc "insertAndShift"
    (expr_lambda ["prior"; "i"]
     (expr_let "indx" (expr_op1 unary_op_prim_to_str (expr_id "i"))
      (expr_let "next"
       (expr_app (expr_id "%Get1") [expr_id "obj"; expr_id "indx"])
       (expr_seq
        (expr_app (expr_id "%Put1")
         [expr_id "obj"; expr_id "indx"; expr_id "prior"; expr_true])
        (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "before"))
         (expr_app (expr_id "insertAndShift")
          [expr_id "next";
           expr_op2 binary_op_add (expr_id "i")
           (expr_number (JsNumber.of_int (1)))]) expr_undefined)))))
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
           (expr_number (JsNumber.of_int (1))))
          (expr_let "old"
           (expr_app (expr_id "%Get1") [expr_id "obj"; expr_id "indx"])
           (expr_seq
            (expr_app (expr_id "%Put1")
             [expr_id "obj"; expr_id "indx"; expr_id "elt"; expr_true])
            (expr_app (expr_id "insertAndShift")
             [expr_id "old";
              expr_op2 binary_op_add (expr_id "currIndex")
              (expr_number (JsNumber.of_int (1)))])))
          (expr_app (expr_id "loop")
           [expr_op2 binary_op_add (expr_id "currIndex")
            (expr_number (JsNumber.of_int (1)))]))))))
     (expr_app (expr_id "loop") [expr_number (JsNumber.of_int (0))]))))
  (expr_let "len"
   (expr_app (expr_id "%Get1") [expr_id "obj"; expr_string "length"])
   (expr_recc "isort"
    (expr_lambda ["i"]
     (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "len"))
      (expr_seq
       (expr_app (expr_id "insert")
        [expr_app (expr_id "%Get1")
         [expr_id "obj"; expr_op1 unary_op_prim_to_str (expr_id "i")];
         expr_id "i"])
       (expr_app (expr_id "isort")
        [expr_op2 binary_op_add (expr_id "i")
         (expr_number (JsNumber.of_int (1)))])) (expr_id "obj")))
    (expr_app (expr_id "isort") [expr_number (JsNumber.of_int (1))])))))
.
Definition ex_privspliceCall := 
expr_let "start"
(expr_get_attr pattr_value (expr_id "args") (expr_string "0"))
(expr_let "deleteCount"
 (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
 (expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
  (expr_let "emptyobj"
   (expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
    [] [])
   (expr_let "A"
    (expr_app (expr_id "%MakeArray") [expr_number (JsNumber.of_int (0))])
    (expr_let "lenVal"
     (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
     (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
      (expr_let "relativeStart"
       (expr_app (expr_id "%ToInteger") [expr_id "start"])
       (expr_let "actualStart"
        (expr_if
         (expr_op2 binary_op_lt (expr_id "relativeStart")
          (expr_number (JsNumber.of_int (0))))
         (expr_app (expr_id "%max")
          [expr_op2 binary_op_add (expr_id "len") (expr_id "relativeStart");
           expr_number (JsNumber.of_int (0))])
         (expr_app (expr_id "%min") [expr_id "relativeStart"; expr_id "len"]))
        (expr_let "actualDeleteCount"
         (expr_app (expr_id "%min")
          [expr_app (expr_id "%max")
           [expr_app (expr_id "%ToInteger") [expr_id "deleteCount"];
            expr_number (JsNumber.of_int (0))];
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
               (expr_app (expr_id "%HasProperty")
                [expr_id "O"; expr_id "from"])
               (expr_seq
                (expr_let "fromValue"
                 (expr_app (expr_id "%Get1") [expr_id "O"; expr_id "from"])
                 (expr_app (expr_id "%defineOwnProperty")
                  [expr_id "A";
                   expr_app (expr_id "%ToString") [expr_id "k"];
                   expr_object
                   (objattrs_intro (expr_string "Object") expr_true expr_null
                    expr_undefined) []
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
                 (expr_set_attr pattr_value (expr_id "A")
                  (expr_string "length")
                  (expr_op2 binary_op_add
                   (expr_get_attr pattr_value (expr_id "A")
                    (expr_string "length"))
                   (expr_number (JsNumber.of_int (1)))))
                 (expr_app (expr_id "writeToALoop")
                  [expr_op2 binary_op_add (expr_id "k")
                   (expr_number (JsNumber.of_int (1)))])))
               (expr_app (expr_id "writeToALoop")
                [expr_op2 binary_op_add (expr_id "k")
                 (expr_number (JsNumber.of_int (1)))]))) expr_undefined))
           (expr_app (expr_id "writeToALoop")
            [expr_number (JsNumber.of_int (0))]))
          (expr_let "itemCount"
           (expr_op2 binary_op_sub
            (expr_get_attr pattr_value (expr_id "args")
             (expr_string "length")) (expr_number (JsNumber.of_int (2))))
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
                       (expr_app (expr_id "%HasProperty")
                        [expr_id "O"; expr_id "from"])
                       (expr_seq
                        (expr_app (expr_id "%Put1")
                         [expr_id "O";
                          expr_id "to";
                          expr_app (expr_id "%Get1")
                          [expr_id "O"; expr_id "from"];
                          expr_true])
                        (expr_app (expr_id "writeToOLoop")
                         [expr_op2 binary_op_add (expr_id "k")
                          (expr_number (JsNumber.of_int (1)))]))
                       (expr_seq
                        (expr_app (expr_id "%Delete")
                         [expr_id "O"; expr_id "to"; expr_false])
                        (expr_app (expr_id "writeToOLoop")
                         [expr_op2 binary_op_add (expr_id "k")
                          (expr_number (JsNumber.of_int (1)))])))))
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
                      (expr_number (JsNumber.of_int (1))))
                     (expr_seq
                      (expr_app (expr_id "%Delete")
                       [expr_id "O";
                        expr_app (expr_id "%ToString") [expr_id "next"];
                        expr_false])
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
                       (expr_number (JsNumber.of_int (1))))])
                    (expr_let "to"
                     (expr_app (expr_id "%ToString")
                      [expr_op2 binary_op_add (expr_id "k")
                       (expr_op2 binary_op_sub (expr_id "itemCount")
                        (expr_number (JsNumber.of_int (1))))])
                     (expr_if
                      (expr_app (expr_id "%HasProperty")
                       [expr_id "O"; expr_id "from"])
                      (expr_seq
                       (expr_app (expr_id "%Put1")
                        [expr_id "O";
                         expr_id "to";
                         expr_app (expr_id "%Get1")
                         [expr_id "O"; expr_id "from"];
                         expr_true])
                       (expr_app (expr_id "writeToOLoop")
                        [expr_op2 binary_op_sub (expr_id "k")
                         (expr_number (JsNumber.of_int (1)))]))
                      (expr_seq
                       (expr_app (expr_id "%Delete")
                        [expr_id "O"; expr_id "to"; expr_false])
                       (expr_app (expr_id "writeToOLoop")
                        [expr_op2 binary_op_sub (expr_id "k")
                         (expr_number (JsNumber.of_int (1)))])))))
                   expr_undefined))
                 (expr_app (expr_id "writeToOLoop")
                  [expr_op2 binary_op_sub (expr_id "len")
                   (expr_id "actualDeleteCount")])) expr_undefined))
              (expr_app (expr_id "step2") []))
             (expr_seq
              (expr_let "outerEnd"
               (expr_get_attr pattr_value (expr_id "args")
                (expr_string "length"))
               (expr_recc "outerloop"
                (expr_lambda ["k"; "argsIndex"]
                 (expr_if
                  (expr_op2 binary_op_lt (expr_id "argsIndex")
                   (expr_id "outerEnd"))
                  (expr_seq
                   (expr_app (expr_id "%Put1")
                    [expr_id "O";
                     expr_app (expr_id "%ToString") [expr_id "k"];
                     expr_get_attr pattr_value (expr_id "args")
                     (expr_op1 unary_op_prim_to_str (expr_id "argsIndex"));
                     expr_true])
                   (expr_app (expr_id "outerloop")
                    [expr_op2 binary_op_add (expr_id "k")
                     (expr_number (JsNumber.of_int (1)));
                     expr_op2 binary_op_add (expr_id "argsIndex")
                     (expr_number (JsNumber.of_int (1)))])) expr_undefined))
                (expr_app (expr_id "outerloop")
                 [expr_id "actualStart"; expr_number (JsNumber.of_int (2))])))
              (expr_seq
               (expr_app (expr_id "%Put1")
                [expr_string "length";
                 expr_op2 binary_op_add
                 (expr_op2 binary_op_sub (expr_id "len")
                  (expr_id "actualDeleteCount")) (expr_id "itemCount");
                 expr_true]) (expr_id "A"))))))))))))))))
.
Definition ex_privsplitCall :=  expr_string "String.prototype.split NYI" .
Definition ex_privsqrtCall :=  expr_string "sqrt NYI" .
Definition ex_privstringConcatCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "end"
  (expr_get_attr pattr_value (expr_id "args") (expr_string "length"))
  (expr_recc "loop"
   (expr_lambda ["i"; "soFar"]
    (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "end"))
     (expr_let "next"
      (expr_app (expr_id "%ToString")
       [expr_get_attr pattr_value (expr_id "args")
        (expr_op1 unary_op_prim_to_str (expr_id "i"))])
      (expr_app (expr_id "loop")
       [expr_op2 binary_op_add (expr_id "i")
        (expr_number (JsNumber.of_int (1)));
        expr_op2 binary_op_string_plus (expr_id "soFar") (expr_id "next")]))
     (expr_id "soFar")))
   (expr_app (expr_id "loop")
    [expr_number (JsNumber.of_int (0)); expr_id "S"]))))
.
Definition ex_privstringIndexOfCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "searchStr"
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_let "pos"
   (expr_app (expr_id "%ToInteger")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
   (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
    (expr_let "start"
     (expr_app (expr_id "%min")
      [expr_app (expr_id "%max")
       [expr_id "pos"; expr_number (JsNumber.of_int (0))];
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
            (expr_op1 unary_op_not
             (expr_op2 binary_op_stx_eq
              (expr_op2 binary_op_char_at (expr_id "S")
               (expr_op2 binary_op_add (expr_id "k") (expr_id "j")))
              (expr_op2 binary_op_char_at (expr_id "searchStr") (expr_id "j"))))
            expr_false
            (expr_app (expr_id "check_j")
             [expr_op2 binary_op_add (expr_id "j")
              (expr_number (JsNumber.of_int (1)))]))))
         (expr_if
          (expr_op1 unary_op_not
           (expr_op2 binary_op_le
            (expr_op2 binary_op_add (expr_id "k") (expr_id "searchLen"))
            (expr_id "len"))) expr_false
          (expr_if
           (expr_op1 unary_op_not
            (expr_app (expr_id "check_j") [expr_number (JsNumber.of_int (0))]))
           expr_false expr_true))))
       (expr_recc "find_k"
        (expr_lambda ["curr"]
         (expr_if
          (expr_op2 binary_op_gt
           (expr_op2 binary_op_add (expr_id "curr") (expr_id "searchLen"))
           (expr_id "len"))
          (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1))))
          (expr_if (expr_app (expr_id "check_k") [expr_id "curr"])
           (expr_id "curr")
           (expr_app (expr_id "find_k")
            [expr_op2 binary_op_add (expr_id "curr")
             (expr_number (JsNumber.of_int (1)))]))))
        (expr_app (expr_id "find_k") [expr_id "start"])))))))))
.
Definition ex_privstringLastIndexOfCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "searchStr"
  (expr_app (expr_id "%ToString")
   [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
  (expr_let "numPos"
   (expr_app (expr_id "%ToNumber")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "1")])
   (expr_let "pos"
    (expr_if
     (expr_op1 unary_op_not
      (expr_op2 binary_op_stx_eq (expr_id "numPos") (expr_id "numPos")))
     (expr_number JsNumber.infinity)
     (expr_app (expr_id "%ToInteger") [expr_id "numPos"]))
    (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
     (expr_let "start"
      (expr_app (expr_id "%min")
       [expr_app (expr_id "%max")
        [expr_id "pos"; expr_number (JsNumber.of_int (0))];
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
             (expr_op1 unary_op_not
              (expr_op2 binary_op_stx_eq
               (expr_op2 binary_op_char_at (expr_id "S")
                (expr_op2 binary_op_add (expr_id "k") (expr_id "j")))
               (expr_op2 binary_op_char_at (expr_id "searchStr")
                (expr_id "j")))) expr_false
             (expr_app (expr_id "check_j")
              [expr_op2 binary_op_add (expr_id "j")
               (expr_number (JsNumber.of_int (1)))]))))
          (expr_if
           (expr_op1 unary_op_not
            (expr_op2 binary_op_le
             (expr_op2 binary_op_add (expr_id "k") (expr_id "searchLen"))
             (expr_id "len"))) expr_false
           (expr_if
            (expr_op1 unary_op_not
             (expr_app (expr_id "check_j")
              [expr_number (JsNumber.of_int (0))])) expr_false expr_true))))
        (expr_recc "find_k"
         (expr_lambda ["curr"]
          (expr_if
           (expr_op2 binary_op_lt (expr_id "curr")
            (expr_number (JsNumber.of_int (0))))
           (expr_op1 unary_op_neg (expr_number (JsNumber.of_int (1))))
           (expr_if (expr_app (expr_id "check_k") [expr_id "curr"])
            (expr_id "curr")
            (expr_app (expr_id "find_k")
             [expr_op2 binary_op_sub (expr_id "curr")
              (expr_number (JsNumber.of_int (1)))]))))
         (expr_app (expr_id "find_k") [expr_id "start"]))))))))))
.
Definition ex_privstringSliceCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
  (expr_let "intStart"
   (expr_app (expr_id "%ToInteger")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "end"
    (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
    (expr_let "intEnd"
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "end") expr_undefined)
      (expr_id "len") (expr_app (expr_id "%ToInteger") [expr_id "end"]))
     (expr_let "from"
      (expr_if
       (expr_op2 binary_op_lt (expr_id "intStart")
        (expr_number (JsNumber.of_int (0))))
       (expr_app (expr_id "%max")
        [expr_op2 binary_op_add (expr_id "len") (expr_id "intStart");
         expr_number (JsNumber.of_int (0))])
       (expr_app (expr_id "%min") [expr_id "intStart"; expr_id "len"]))
      (expr_let "to"
       (expr_if
        (expr_op2 binary_op_lt (expr_id "intEnd")
         (expr_number (JsNumber.of_int (0))))
        (expr_app (expr_id "%max")
         [expr_op2 binary_op_add (expr_id "len") (expr_id "intEnd");
          expr_number (JsNumber.of_int (0))])
        (expr_app (expr_id "%min") [expr_id "intEnd"; expr_id "len"]))
       (expr_let "span"
        (expr_app (expr_id "%max")
         [expr_op2 binary_op_sub (expr_id "to") (expr_id "from");
          expr_number (JsNumber.of_int (0))])
        (expr_recc "build"
         (expr_lambda ["i"; "result"]
          (expr_if (expr_op2 binary_op_lt (expr_id "i") (expr_id "span"))
           (expr_let "next"
            (expr_op2 binary_op_string_plus (expr_id "result")
             (expr_op2 binary_op_char_at (expr_id "S")
              (expr_op2 binary_op_add (expr_id "from") (expr_id "i"))))
            (expr_app (expr_id "build")
             [expr_op2 binary_op_add (expr_id "i")
              (expr_number (JsNumber.of_int (1)));
              expr_id "next"])) (expr_id "result")))
         (expr_app (expr_id "build")
          [expr_number (JsNumber.of_int (0)); expr_string ""]))))))))))
.
Definition ex_privstringToStringCall := 
expr_let "t" (expr_op1 unary_op_typeof (expr_id "this"))
(expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "string"))
 (expr_id "this")
 (expr_if (expr_op2 binary_op_stx_eq (expr_id "t") (expr_string "object"))
  (expr_if
   (expr_op2 binary_op_stx_eq
    (expr_get_obj_attr oattr_class (expr_id "this")) (expr_string "String"))
   (expr_get_internal "primval" (expr_id "this"))
   (expr_app (expr_id "%TypeError")
    [expr_string "String.prototype.toString got a non-string object"]))
  (expr_app (expr_id "%TypeError")
   [expr_string "String.prototype.toString got a non-string value"])))
.
Definition ex_privsubstringCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_let "len" (expr_op1 unary_op_strlen (expr_id "S"))
  (expr_let "intStart"
   (expr_app (expr_id "%ToInteger")
    [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
   (expr_let "intEnd"
    (expr_let "end"
     (expr_get_attr pattr_value (expr_id "args") (expr_string "1"))
     (expr_if (expr_op2 binary_op_stx_eq (expr_id "end") expr_undefined)
      (expr_id "len") (expr_app (expr_id "%ToInteger") [expr_id "end"])))
    (expr_let "finalStart"
     (expr_app (expr_id "%min")
      [expr_app (expr_id "%max")
       [expr_id "intStart"; expr_number (JsNumber.of_int (0))];
       expr_id "len"])
     (expr_let "finalEnd"
      (expr_app (expr_id "%min")
       [expr_app (expr_id "%max")
        [expr_id "intEnd"; expr_number (JsNumber.of_int (0))];
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
             (expr_number (JsNumber.of_int (1)));
             expr_op2 binary_op_string_plus (expr_id "soFar")
             (expr_op2 binary_op_char_at (expr_id "S") (expr_id "i"))])
           (expr_id "soFar")))
         (expr_app (expr_id "loop") [expr_id "from"; expr_string ""]))))))))))
.
Definition ex_privtanCall :=  expr_string "tan NYI" .
Definition ex_privtestCall := 
expr_op1 unary_op_print
(expr_string
 "You used the es5.env testCall.  Are you sure you didn't forget to include the regexp.js library, or regexp.env?")
.
Definition ex_privtoExponentialCall :=  expr_string "toExponential NYI" .
Definition ex_privtoFixedCall := 
expr_let "x" (expr_app (expr_id "%numberPrimval") [expr_id "this"])
(expr_let "f"
 (expr_app (expr_id "%ToInteger")
  [expr_get_attr pattr_value (expr_id "args") (expr_string "0")])
 (expr_seq
  (expr_if
   (expr_if
    (expr_op2 binary_op_lt (expr_id "f") (expr_number (JsNumber.of_int (0))))
    expr_true
    (expr_op2 binary_op_gt (expr_id "f") (expr_number (JsNumber.of_int (20)))))
   (expr_app (expr_id "%RangeError")
    [expr_string "invalid fractionDigits in Number.toFixed"]) expr_undefined)
  (expr_if
   (expr_op2 binary_op_same_value (expr_id "x") (expr_number JsNumber.nan))
   (expr_string "NaN")
   (expr_if
    (expr_op2 binary_op_ge (expr_id "x") (expr_number (JsNumber.of_int (0))))
    (expr_app (expr_id "%ToString") [expr_id "x"])
    (expr_op2 binary_op_to_fixed (expr_id "x") (expr_id "f"))))))
.
Definition ex_privtoLocaleStringCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "toString"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "toString"])
 (expr_if
  (expr_op2 binary_op_stx_eq
   (expr_get_obj_attr oattr_code (expr_id "toString")) expr_null)
  (expr_app (expr_id "%TypeError") [expr_string "toLocaleString"])
  (expr_app (expr_id "toString")
   [expr_id "O";
    expr_object
    (objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined)
    [] []])))
.
Definition ex_privtoLowerCaseCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_op1 unary_op_to_lower (expr_id "S")))
.
Definition ex_privtoPrecisionCall :=  expr_string "toPrecision NYI" .
Definition ex_privtoUpperCaseCall := 
expr_seq (expr_app (expr_id "%CheckObjectCoercible") [expr_id "this"])
(expr_let "S" (expr_app (expr_id "%ToString") [expr_id "this"])
 (expr_op1 unary_op_to_upper (expr_id "S")))
.
Definition ex_privtwoArgObj := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined) 
[]
[("0", property_data
       (data_intro (expr_id "arg1") expr_false expr_false expr_false));
 ("1", property_data
       (data_intro (expr_id "arg2") expr_false expr_false expr_false))]
.
Definition ex_privunescapeCall :=  expr_string "unescape NYI" .
Definition ex_privunshiftCall := 
expr_let "O" (expr_app (expr_id "%ToObject") [expr_id "this"])
(expr_let "lenVal"
 (expr_app (expr_id "%Get1") [expr_id "O"; expr_string "length"])
 (expr_let "len" (expr_app (expr_id "%ToUint32") [expr_id "lenVal"])
  (expr_let "argCount" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
   (expr_seq
    (expr_recc "Oloop"
     (expr_lambda ["k"]
      (expr_if
       (expr_op2 binary_op_gt (expr_id "k")
        (expr_number (JsNumber.of_int (0))))
       (expr_let "from"
        (expr_app (expr_id "%ToString")
         [expr_op2 binary_op_sub (expr_id "k")
          (expr_number (JsNumber.of_int (1)))])
        (expr_let "to"
         (expr_app (expr_id "%ToString")
          [expr_op2 binary_op_add (expr_id "k")
           (expr_op2 binary_op_sub (expr_id "argCount")
            (expr_number (JsNumber.of_int (1))))])
         (expr_if
          (expr_app (expr_id "%HasProperty") [expr_id "O"; expr_id "from"])
          (expr_seq
           (expr_app (expr_id "%Put1")
            [expr_id "O";
             expr_id "to";
             expr_app (expr_id "%Get1") [expr_id "O"; expr_id "from"];
             expr_true])
           (expr_app (expr_id "Oloop")
            [expr_op2 binary_op_sub (expr_id "k")
             (expr_number (JsNumber.of_int (1)))]))
          (expr_seq
           (expr_app (expr_id "%Delete")
            [expr_id "O"; expr_id "to"; expr_false])
           (expr_app (expr_id "Oloop")
            [expr_op2 binary_op_sub (expr_id "k")
             (expr_number (JsNumber.of_int (1)))]))))) expr_undefined))
     (expr_app (expr_id "Oloop") [expr_id "len"]))
    (expr_seq
     (expr_let "end" (expr_app (expr_id "%ComputeLength") [expr_id "args"])
      (expr_recc "argsLoop"
       (expr_lambda ["argsIndex"; "j"]
        (expr_if
         (expr_op2 binary_op_lt (expr_id "argsIndex") (expr_id "end"))
         (expr_seq
          (expr_app (expr_id "%Put1")
           [expr_id "O";
            expr_app (expr_id "%ToString") [expr_id "j"];
            expr_get_attr pattr_value (expr_id "args")
            (expr_op1 unary_op_prim_to_str (expr_id "argsIndex"));
            expr_true])
          (expr_app (expr_id "argsLoop")
           [expr_op2 binary_op_add (expr_id "argsIndex")
            (expr_number (JsNumber.of_int (1)));
            expr_op2 binary_op_add (expr_id "j")
            (expr_number (JsNumber.of_int (1)))])) expr_undefined))
       (expr_app (expr_id "argsLoop")
        [expr_number (JsNumber.of_int (0)); expr_number (JsNumber.of_int (0))])))
     (expr_let "finalLen"
      (expr_op2 binary_op_add (expr_id "len") (expr_id "argCount"))
      (expr_seq
       (expr_app (expr_id "%Put1")
        [expr_id "O"; expr_string "length"; expr_id "finalLen"; expr_true])
       (expr_id "finalLen"))))))))
.
Definition ex_privvalueOfCall := 
expr_let "hasWrongProto"
(expr_op1 unary_op_not
 (expr_op2 binary_op_stx_eq (expr_get_obj_attr oattr_proto (expr_id "this"))
  (expr_id "proto")))
(expr_let "hasWrongTypeof"
 (expr_op1 unary_op_not
  (expr_op2 binary_op_stx_eq (expr_app (expr_id "%Typeof") [expr_id "this"])
   (expr_id "typestr")))
 (expr_let "isntProto"
  (expr_op1 unary_op_not
   (expr_op2 binary_op_stx_eq (expr_id "this") (expr_id "proto")))
  (expr_if
   (expr_if
    (expr_if (expr_id "hasWrongProto") (expr_id "hasWrongTypeof") expr_false)
    (expr_id "isntProto") expr_false)
   (expr_app (expr_id "%TypeError") [expr_string "valueOf"])
   (expr_if (expr_id "hasWrongTypeof")
    (expr_get_internal "primval" (expr_id "this")) (expr_id "this")))))
.
Definition ex_privzeroArgObj := 
expr_object
(objattrs_intro (expr_string "Object") expr_true expr_null expr_undefined) 
[] []
.
Definition objCode :=  value_undefined .
Definition name_objCode : id :=  "objCode" .
Definition proto :=  value_null .
Definition name_proto : id :=  "proto" .
Definition privAddAccessorField := 
value_closure
(closure_intro [] None ["obj"; "name"; "g"; "s"; "e"; "c"]
 ex_privAddAccessorField)
.
Definition name_privAddAccessorField : id :=  "%AddAccessorField" .
Definition privAddDataField := 
value_closure
(closure_intro [] None ["obj"; "name"; "v"; "w"; "e"; "c"]
 ex_privAddDataField)
.
Definition name_privAddDataField : id :=  "%AddDataField" .
Definition privAppExpr := 
value_closure (closure_intro [] None ["fun"; "this"; "args"] ex_privAppExpr)
.
Definition name_privAppExpr : id :=  "%AppExpr" .
Definition privTypeof := 
value_closure (closure_intro [] None ["val"] ex_privTypeof)
.
Definition name_privTypeof : id :=  "%Typeof" .
Definition privIsCallable := 
value_closure
(closure_intro [("%Typeof", privTypeof)] None ["o"] ex_privIsCallable)
.
Definition name_privIsCallable : id :=  "%IsCallable" .
Definition privJSError := 
value_closure (closure_intro [] None ["err"] ex_privJSError)
.
Definition name_privJSError : id :=  "%JSError" .
Definition privMakeNativeError := 
value_closure (closure_intro [] None ["proto"; "msg"] ex_privMakeNativeError)
.
Definition name_privMakeNativeError : id :=  "%MakeNativeError" .
Definition privNativeError := 
value_closure
(closure_intro
 [("%JSError", privJSError); ("%MakeNativeError", privMakeNativeError)] 
 None ["proto"; "msg"] ex_privNativeError)
.
Definition name_privNativeError : id :=  "%NativeError" .
Definition privTypeErrorProto :=  value_object 4 .
Definition name_privTypeErrorProto : id :=  "%TypeErrorProto" .
Definition privTypeError := 
value_closure
(closure_intro
 [("%NativeError", privNativeError); ("%TypeErrorProto", privTypeErrorProto)]
 None ["msg"] ex_privTypeError)
.
Definition name_privTypeError : id :=  "%TypeError" .
Definition privAppExprCheck := 
value_closure
(closure_intro
 [("%AppExpr", privAppExpr);
  ("%IsCallable", privIsCallable);
  ("%TypeError", privTypeError)] None ["fun"; "this"; "args"]
 ex_privAppExprCheck)
.
Definition name_privAppExprCheck : id :=  "%AppExprCheck" .
Definition privGetOwnProperty := 
value_closure
(closure_intro [] None ["obj"; "id"; "f_data"; "f_acc"; "f_undef"]
 ex_privGetOwnProperty)
.
Definition name_privGetOwnProperty : id :=  "%GetOwnProperty" .
Definition privGetProperty := 
value_closure
(closure_intro [("%GetOwnProperty", privGetOwnProperty)]
 (Some "%GetProperty") ["obj"; "id"; "f_data"; "f_acc"; "f_undef"]
 ex_privGetProperty)
.
Definition name_privGetProperty : id :=  "%GetProperty" .
Definition privzeroArgObj := 
value_closure (closure_intro [] None [] ex_privzeroArgObj)
.
Definition name_privzeroArgObj : id :=  "%zeroArgObj" .
Definition privGet := 
value_closure
(closure_intro
 [("%AppExpr", privAppExpr);
  ("%GetProperty", privGetProperty);
  ("%zeroArgObj", privzeroArgObj)] None ["obj"; "this"; "fld"] ex_privGet)
.
Definition name_privGet : id :=  "%Get" .
Definition privGet1 := 
value_closure
(closure_intro [("%Get", privGet)] None ["obj"; "fld"] ex_privGet1)
.
Definition name_privGet1 : id :=  "%Get1" .
Definition privBooleanProto :=  value_object 9 .
Definition name_privBooleanProto : id :=  "%BooleanProto" .
Definition privMakeBoolean := 
value_closure
(closure_intro [("%BooleanProto", privBooleanProto)] None ["v"]
 ex_privMakeBoolean)
.
Definition name_privMakeBoolean : id :=  "%MakeBoolean" .
Definition privNumberProto :=  value_object 10 .
Definition name_privNumberProto : id :=  "%NumberProto" .
Definition privMakeNumber := 
value_closure
(closure_intro [("%NumberProto", privNumberProto)] None ["v"]
 ex_privMakeNumber)
.
Definition name_privMakeNumber : id :=  "%MakeNumber" .
Definition privStringIndices := 
value_closure (closure_intro [] None ["obj"; "s"] ex_privStringIndices)
.
Definition name_privStringIndices : id :=  "%StringIndices" .
Definition privStringProto :=  value_object 11 .
Definition name_privStringProto : id :=  "%StringProto" .
Definition privMakeString := 
value_closure
(closure_intro
 [("%StringIndices", privStringIndices); ("%StringProto", privStringProto)]
 None ["v"] ex_privMakeString)
.
Definition name_privMakeString : id :=  "%MakeString" .
Definition privToObject := 
value_closure
(closure_intro
 [("%MakeBoolean", privMakeBoolean);
  ("%MakeNumber", privMakeNumber);
  ("%MakeString", privMakeString);
  ("%TypeError", privTypeError)] None ["o"] ex_privToObject)
.
Definition name_privToObject : id :=  "%ToObject" .
Definition privGetPrim := 
value_closure
(closure_intro [("%Get", privGet); ("%ToObject", privToObject)] None
 ["obj"; "fld"] ex_privGetPrim)
.
Definition name_privGetPrim : id :=  "%GetPrim" .
Definition privGetField := 
value_closure
(closure_intro [("%Get1", privGet1); ("%GetPrim", privGetPrim)] None
 ["v"; "fld"] ex_privGetField)
.
Definition name_privGetField : id :=  "%GetField" .
Definition privAppMethodOp := 
value_closure
(closure_intro
 [("%AppExprCheck", privAppExprCheck); ("%GetField", privGetField)] None
 ["fargs"] ex_privAppMethodOp)
.
Definition name_privAppMethodOp : id :=  "%AppMethodOp" .
Definition privComputeLength := 
value_closure (closure_intro [] None ["args"] ex_privComputeLength)
.
Definition name_privComputeLength : id :=  "%ComputeLength" .
Definition privArrayProto :=  value_object 52 .
Definition name_privArrayProto : id :=  "%ArrayProto" .
Definition privMakeArray := 
value_closure
(closure_intro [("%ArrayProto", privArrayProto)] None ["len"]
 ex_privMakeArray)
.
Definition name_privMakeArray : id :=  "%MakeArray" .
Definition privRangeErrorProto :=  value_object 8 .
Definition name_privRangeErrorProto : id :=  "%RangeErrorProto" .
Definition privToPrimitiveHint := 
value_closure
(closure_intro
 [("%AppExpr", privAppExpr);
  ("%Get1", privGet1);
  ("%IsCallable", privIsCallable);
  ("%TypeError", privTypeError);
  ("%zeroArgObj", privzeroArgObj)] None ["val"; "hint"]
 ex_privToPrimitiveHint)
.
Definition name_privToPrimitiveHint : id :=  "%ToPrimitiveHint" .
Definition privToNumber := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["x"]
 ex_privToNumber)
.
Definition name_privToNumber : id :=  "%ToNumber" .
Definition privToUint := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["n"; "limit"]
 ex_privToUint)
.
Definition name_privToUint : id :=  "%ToUint" .
Definition privToUint32 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"] ex_privToUint32)
.
Definition name_privToUint32 : id :=  "%ToUint32" .
Definition privToBoolean := 
value_closure (closure_intro [] None ["x"] ex_privToBoolean)
.
Definition name_privToBoolean : id :=  "%ToBoolean" .
Definition privToString := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 ex_privToString)
.
Definition name_privToString : id :=  "%ToString" .
Definition privDelete := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"; "fld"; "strict"]
 ex_privDelete)
.
Definition name_privDelete : id :=  "%Delete" .
Definition copy_when_defined := 
value_closure
(closure_intro [] None ["obj1"; "obj2"; "s"] ex_copy_when_defined)
.
Definition name_copy_when_defined : id :=  "copy-when-defined" .
Definition copy_access_desc := 
value_closure
(closure_intro
 [("%Delete", privDelete); ("copy-when-defined", copy_when_defined)] 
 None ["obj1"; "obj2"] ex_copy_access_desc)
.
Definition name_copy_access_desc : id :=  "copy-access-desc" .
Definition copy_data_desc := 
value_closure
(closure_intro
 [("%Delete", privDelete); ("copy-when-defined", copy_when_defined)] 
 None ["obj1"; "obj2"] ex_copy_data_desc)
.
Definition name_copy_data_desc : id :=  "copy-data-desc" .
Definition isAccessorDescriptor := 
value_closure (closure_intro [] None ["attr-obj"] ex_isAccessorDescriptor)
.
Definition name_isAccessorDescriptor : id :=  "isAccessorDescriptor" .
Definition isDataDescriptor := 
value_closure (closure_intro [] None ["attr-obj"] ex_isDataDescriptor)
.
Definition name_isDataDescriptor : id :=  "isDataDescriptor" .
Definition privdefineOwnProperty := 
value_closure
(closure_intro
 [("%ToBoolean", privToBoolean);
  ("%ToString", privToString);
  ("%TypeError", privTypeError);
  ("copy-access-desc", copy_access_desc);
  ("copy-data-desc", copy_data_desc);
  ("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["obj"; "field"; "attr-obj"]
 ex_privdefineOwnProperty)
.
Definition name_privdefineOwnProperty : id :=  "%defineOwnProperty" .
Definition privArrayConstructor := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%JSError", privJSError);
  ("%MakeArray", privMakeArray);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["this"; "args"]
 ex_privArrayConstructor)
.
Definition name_privArrayConstructor : id :=  "%ArrayConstructor" .
Definition privArrayCall := 
value_closure
(closure_intro [("%ArrayConstructor", privArrayConstructor)] None
 ["obj"; "this"; "args"] ex_privArrayCall)
.
Definition name_privArrayCall : id :=  "%ArrayCall" .
Definition privArrayGlobalFuncObj :=  value_object 101 .
Definition name_privArrayGlobalFuncObj : id :=  "%ArrayGlobalFuncObj" .
Definition privArrayIdx := 
value_closure (closure_intro [] None ["arr"; "idx"] ex_privArrayIdx)
.
Definition name_privArrayIdx : id :=  "%ArrayIdx" .
Definition privArrayLengthChange := 
value_closure
(closure_intro
 [("%Delete", privDelete); ("%Get1", privGet1); ("%ToUint32", privToUint32)]
 None ["arr"; "newlen"] ex_privArrayLengthChange)
.
Definition name_privArrayLengthChange : id :=  "%ArrayLengthChange" .
Definition privrunConstruct := 
value_closure (closure_intro [] None ["constr"; "args"] ex_privrunConstruct)
.
Definition name_privrunConstruct : id :=  "%runConstruct" .
Definition privPrimNew := 
value_closure
(closure_intro
 [("%TypeError", privTypeError); ("%runConstruct", privrunConstruct)] 
 None ["constr"; "args"] ex_privPrimNew)
.
Definition name_privPrimNew : id :=  "%PrimNew" .
Definition privconcat :=  value_object 95 .
Definition name_privconcat : id :=  "%concat" .
Definition privBindConstructor := 
value_closure
(closure_intro [("%PrimNew", privPrimNew); ("%concat", privconcat)] None
 ["constr"; "args"] ex_privBindConstructor)
.
Definition name_privBindConstructor : id :=  "%BindConstructor" .
Definition privBindObjCall := 
value_closure
(closure_intro [("%AppExprCheck", privAppExprCheck); ("%concat", privconcat)]
 None ["obj"; "this"; "args"] ex_privBindObjCall)
.
Definition name_privBindObjCall : id :=  "%BindObjCall" .
Definition privToInt32 := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["n"] ex_privToInt32)
.
Definition name_privToInt32 : id :=  "%ToInt32" .
Definition privBitwiseInfix := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["l"; "r"; "op"]
 ex_privBitwiseInfix)
.
Definition name_privBitwiseInfix : id :=  "%BitwiseInfix" .
Definition privBitwiseAnd := 
value_closure
(closure_intro [("%BitwiseInfix", privBitwiseInfix)] None ["l"; "r"]
 ex_privBitwiseAnd)
.
Definition name_privBitwiseAnd : id :=  "%BitwiseAnd" .
Definition privBitwiseNot := 
value_closure
(closure_intro [("%ToInt32", privToInt32)] None ["expr"] ex_privBitwiseNot)
.
Definition name_privBitwiseNot : id :=  "%BitwiseNot" .
Definition privBitwiseOr := 
value_closure
(closure_intro [("%BitwiseInfix", privBitwiseInfix)] None ["l"; "r"]
 ex_privBitwiseOr)
.
Definition name_privBitwiseOr : id :=  "%BitwiseOr" .
Definition privBitwiseXor := 
value_closure
(closure_intro [("%BitwiseInfix", privBitwiseInfix)] None ["l"; "r"]
 ex_privBitwiseXor)
.
Definition name_privBitwiseXor : id :=  "%BitwiseXor" .
Definition privBooleanCall := 
value_closure
(closure_intro [("%ToBoolean", privToBoolean)] None ["obj"; "this"; "args"]
 ex_privBooleanCall)
.
Definition name_privBooleanCall : id :=  "%BooleanCall" .
Definition privBooleanConstructor := 
value_closure
(closure_intro
 [("%MakeBoolean", privMakeBoolean); ("%ToBoolean", privToBoolean)] None
 ["constr"; "args"] ex_privBooleanConstructor)
.
Definition name_privBooleanConstructor : id :=  "%BooleanConstructor" .
Definition privBooleanGlobalFuncObj :=  value_object 31 .
Definition name_privBooleanGlobalFuncObj : id :=  "%BooleanGlobalFuncObj" .
Definition privCheckObjectCoercible := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 ex_privCheckObjectCoercible)
.
Definition name_privCheckObjectCoercible : id :=  "%CheckObjectCoercible" .
Definition privNumberCompareOp := 
value_closure (closure_intro [] None ["l"; "r"] ex_privNumberCompareOp)
.
Definition name_privNumberCompareOp : id :=  "%NumberCompareOp" .
Definition privPrimitiveCompareOp := 
value_closure
(closure_intro [("%NumberCompareOp", privNumberCompareOp)] None ["l"; "r"]
 ex_privPrimitiveCompareOp)
.
Definition name_privPrimitiveCompareOp : id :=  "%PrimitiveCompareOp" .
Definition privToPrimitive := 
value_closure
(closure_intro [("%ToPrimitiveHint", privToPrimitiveHint)] None ["val"]
 ex_privToPrimitive)
.
Definition name_privToPrimitive : id :=  "%ToPrimitive" .
Definition privCompareOp := 
value_closure
(closure_intro
 [("%PrimitiveCompareOp", privPrimitiveCompareOp);
  ("%ToPrimitive", privToPrimitive)] None ["l"; "r"; "swap"; "neg"]
 ex_privCompareOp)
.
Definition name_privCompareOp : id :=  "%CompareOp" .
Definition privDateProto :=  value_object 167 .
Definition name_privDateProto : id :=  "%DateProto" .
Definition privMakeDate := 
value_closure
(closure_intro [("%DateProto", privDateProto)] None ["v"] ex_privMakeDate)
.
Definition name_privMakeDate : id :=  "%MakeDate" .
Definition privdateToString :=  value_object 168 .
Definition name_privdateToString : id :=  "%dateToString" .
Definition privgetCurrentUTC := 
value_closure (closure_intro [] None [] ex_privgetCurrentUTC)
.
Definition name_privgetCurrentUTC : id :=  "%getCurrentUTC" .
Definition privDateCall := 
value_closure
(closure_intro
 [("%MakeDate", privMakeDate);
  ("%dateToString", privdateToString);
  ("%getCurrentUTC", privgetCurrentUTC)] None ["obj"; "this"; "args"]
 ex_privDateCall)
.
Definition name_privDateCall : id :=  "%DateCall" .
Definition privmsPerDay :=  value_number (JsNumber.of_int (86400000)) .
Definition name_privmsPerDay : id :=  "%msPerDay" .
Definition privMakeDateDayTime := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["day"; "time"]
 ex_privMakeDateDayTime)
.
Definition name_privMakeDateDayTime : id :=  "%MakeDateDayTime" .
Definition privDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"] ex_privDay)
.
Definition name_privDay : id :=  "%Day" .
Definition privDayFromYear := 
value_closure (closure_intro [] None ["y"] ex_privDayFromYear)
.
Definition name_privDayFromYear : id :=  "%DayFromYear" .
Definition privTimeFromYear := 
value_closure
(closure_intro
 [("%DayFromYear", privDayFromYear); ("%msPerDay", privmsPerDay)] None 
 ["y"] ex_privTimeFromYear)
.
Definition name_privTimeFromYear : id :=  "%TimeFromYear" .
Definition privYearFromTime := 
value_closure
(closure_intro [("%TimeFromYear", privTimeFromYear)] None ["t"]
 ex_privYearFromTime)
.
Definition name_privYearFromTime : id :=  "%YearFromTime" .
Definition privDayWithinYear := 
value_closure
(closure_intro
 [("%Day", privDay);
  ("%DayFromYear", privDayFromYear);
  ("%YearFromTime", privYearFromTime)] None ["t"] ex_privDayWithinYear)
.
Definition name_privDayWithinYear : id :=  "%DayWithinYear" .
Definition privDaysInYear := 
value_closure (closure_intro [] None ["y"] ex_privDaysInYear)
.
Definition name_privDaysInYear : id :=  "%DaysInYear" .
Definition privInLeapYear := 
value_closure
(closure_intro
 [("%DaysInYear", privDaysInYear); ("%YearFromTime", privYearFromTime)] 
 None ["t"] ex_privInLeapYear)
.
Definition name_privInLeapYear : id :=  "%InLeapYear" .
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
Definition name_privMonthFromTime : id :=  "%MonthFromTime" .
Definition privDateFromTime := 
value_closure
(closure_intro
 [("%DayWithinYear", privDayWithinYear);
  ("%InLeapYear", privInLeapYear);
  ("%MonthFromTime", privMonthFromTime);
  ("%TypeError", privTypeError)] None ["t"] ex_privDateFromTime)
.
Definition name_privDateFromTime : id :=  "%DateFromTime" .
Definition privDaysInMonth := 
value_closure (closure_intro [] None ["m"; "leap"] ex_privDaysInMonth)
.
Definition name_privDaysInMonth : id :=  "%DaysInMonth" .
Definition privIsFinite := 
value_closure (closure_intro [] None ["n"] ex_privIsFinite)
.
Definition name_privIsFinite : id :=  "%IsFinite" .
Definition privToInteger := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["i"] ex_privToInteger)
.
Definition name_privToInteger : id :=  "%ToInteger" .
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
Definition name_privMakeDay : id :=  "%MakeDay" .
Definition privmsPerHour :=  value_number (JsNumber.of_int (3600000)) .
Definition name_privmsPerHour : id :=  "%msPerHour" .
Definition privmsPerMin :=  value_number (JsNumber.of_int (60000)) .
Definition name_privmsPerMin : id :=  "%msPerMin" .
Definition privmsPerSecond :=  value_number (JsNumber.of_int (1000)) .
Definition name_privmsPerSecond : id :=  "%msPerSecond" .
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
Definition name_privMakeTime : id :=  "%MakeTime" .
Definition privTimeClip := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToInteger", privToInteger)]
 None ["t"] ex_privTimeClip)
.
Definition name_privTimeClip : id :=  "%TimeClip" .
Definition privUTC := 
value_closure (closure_intro [] None ["t"] ex_privUTC)
.
Definition name_privUTC : id :=  "%UTC" .
Definition privparse := 
value_closure (closure_intro [] None ["v"] ex_privparse)
.
Definition name_privparse : id :=  "%parse" .
Definition privDateConstructor := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%DateProto", privDateProto);
  ("%MakeDate", privMakeDate);
  ("%MakeDateDayTime", privMakeDateDayTime);
  ("%MakeDay", privMakeDay);
  ("%MakeTime", privMakeTime);
  ("%TimeClip", privTimeClip);
  ("%ToInteger", privToInteger);
  ("%ToNumber", privToNumber);
  ("%ToPrimitive", privToPrimitive);
  ("%UTC", privUTC);
  ("%getCurrentUTC", privgetCurrentUTC);
  ("%parse", privparse)] None ["constr"; "args"] ex_privDateConstructor)
.
Definition name_privDateConstructor : id :=  "%DateConstructor" .
Definition privDateGlobalFuncObj :=  value_object 171 .
Definition name_privDateGlobalFuncObj : id :=  "%DateGlobalFuncObj" .
Definition privDeclEnvAddBinding := 
value_closure
(closure_intro [("%AddDataField", privAddDataField)] None
 ["context"; "name"; "val"; "mutable"; "deletable"] ex_privDeclEnvAddBinding)
.
Definition name_privDeclEnvAddBinding : id :=  "%DeclEnvAddBinding" .
Definition privglobal :=  value_object 2 .
Definition name_privglobal : id :=  "%global" .
Definition privresolveThis := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%global", privglobal)] 
 None ["strict"; "obj"] ex_privresolveThis)
.
Definition name_privresolveThis : id :=  "%resolveThis" .
Definition privDefaultCall := 
value_closure
(closure_intro [("%resolveThis", privresolveThis)] None
 ["obj"; "this"; "args"] ex_privDefaultCall)
.
Definition name_privDefaultCall : id :=  "%DefaultCall" .
Definition privObjectProto :=  value_object 1 .
Definition name_privObjectProto : id :=  "%ObjectProto" .
Definition privDefaultConstruct := 
value_closure
(closure_intro
 [("%AppExpr", privAppExpr);
  ("%Get1", privGet1);
  ("%ObjectProto", privObjectProto)] None ["constr"; "args"]
 ex_privDefaultConstruct)
.
Definition name_privDefaultConstruct : id :=  "%DefaultConstruct" .
Definition privDeleteOp := 
value_closure
(closure_intro [("%Delete", privDelete); ("%ToObject", privToObject)] 
 None ["obj"; "fld"; "strict"] ex_privDeleteOp)
.
Definition name_privDeleteOp : id :=  "%DeleteOp" .
Definition privHasProperty := 
value_closure
(closure_intro [] (Some "%HasProperty") ["obj"; "id"] ex_privHasProperty)
.
Definition name_privHasProperty : id :=  "%HasProperty" .
Definition privEnvGetId := 
value_closure
(closure_intro [("%HasProperty", privHasProperty)] (Some "%EnvGetId")
 ["context"; "id"; "f"] ex_privEnvGetId)
.
Definition name_privEnvGetId : id :=  "%EnvGetId" .
Definition privReferenceErrorProto :=  value_object 5 .
Definition name_privReferenceErrorProto : id :=  "%ReferenceErrorProto" .
Definition privReferenceError := 
value_closure
(closure_intro
 [("%NativeError", privNativeError);
  ("%ReferenceErrorProto", privReferenceErrorProto)] None ["msg"]
 ex_privReferenceError)
.
Definition name_privReferenceError : id :=  "%ReferenceError" .
Definition privEnvGetBindingValue := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%ReferenceError", privReferenceError)] None ["context"; "id"; "strict"]
 ex_privEnvGetBindingValue)
.
Definition name_privEnvGetBindingValue : id :=  "%EnvGetBindingValue" .
Definition privUnboundId := 
value_closure
(closure_intro [("%ReferenceError", privReferenceError)] None ["id"]
 ex_privUnboundId)
.
Definition name_privUnboundId : id :=  "%UnboundId" .
Definition privEnvGetValue := 
value_closure
(closure_intro
 [("%EnvGetBindingValue", privEnvGetBindingValue);
  ("%UnboundId", privUnboundId)] None ["context"; "id"; "strict"]
 ex_privEnvGetValue)
.
Definition name_privEnvGetValue : id :=  "%EnvGetValue" .
Definition privEnvImplicitThis := 
value_closure (closure_intro [] None ["context"] ex_privEnvImplicitThis)
.
Definition name_privEnvImplicitThis : id :=  "%EnvImplicitThis" .
Definition privmakeGlobalEnv :=  value_object 0 .
Definition name_privmakeGlobalEnv : id :=  "%makeGlobalEnv" .
Definition privconfigurableEval := 
value_closure
(closure_intro [("%makeGlobalEnv", privmakeGlobalEnv)] None
 ["this"; "context"; "vcontext"; "useStrict"; "args"] ex_privconfigurableEval)
.
Definition name_privconfigurableEval : id :=  "%configurableEval" .
Definition priveval :=  value_object 310 .
Definition name_priveval : id :=  "%eval" .
Definition privEnvAppExpr := 
value_closure
(closure_intro
 [("%AppExpr", privAppExpr);
  ("%EnvGetId", privEnvGetId);
  ("%EnvGetValue", privEnvGetValue);
  ("%EnvImplicitThis", privEnvImplicitThis);
  ("%IsCallable", privIsCallable);
  ("%TypeError", privTypeError);
  ("%configurableEval", privconfigurableEval);
  ("%eval", priveval)] None
 ["pcontext"; "vcontext"; "id"; "this"; "args_thunk"; "strict"]
 ex_privEnvAppExpr)
.
Definition name_privEnvAppExpr : id :=  "%EnvAppExpr" .
Definition privoneArgObj := 
value_closure (closure_intro [] None ["arg"] ex_privoneArgObj)
.
Definition name_privoneArgObj : id :=  "%oneArgObj" .
Definition privPut := 
value_closure
(closure_intro
 [("%AddDataField", privAddDataField);
  ("%AppExpr", privAppExpr);
  ("%GetOwnProperty", privGetOwnProperty);
  ("%GetProperty", privGetProperty);
  ("%TypeError", privTypeError);
  ("%oneArgObj", privoneArgObj)] None ["obj"; "this"; "fld"; "val"; "strict"]
 ex_privPut)
.
Definition name_privPut : id :=  "%Put" .
Definition privPut1 := 
value_closure
(closure_intro [("%Put", privPut)] None ["obj"; "fld"; "val"; "strict"]
 ex_privPut1)
.
Definition name_privPut1 : id :=  "%Put1" .
Definition privEnvSetMutableBinding := 
value_closure
(closure_intro [("%Put1", privPut1); ("%TypeError", privTypeError)] None
 ["context"; "id"; "val"; "strict"] ex_privEnvSetMutableBinding)
.
Definition name_privEnvSetMutableBinding : id :=  "%EnvSetMutableBinding" .
Definition privEnvPutValue := 
value_closure
(closure_intro
 [("%EnvSetMutableBinding", privEnvSetMutableBinding);
  ("%UnboundId", privUnboundId);
  ("%global", privglobal)] None ["context"; "id"; "val"; "strict"]
 ex_privEnvPutValue)
.
Definition name_privEnvPutValue : id :=  "%EnvPutValue" .
Definition privEnvAssign := 
value_closure
(closure_intro
 [("%EnvGetId", privEnvGetId); ("%EnvPutValue", privEnvPutValue)] None
 ["context"; "id"; "val_thunk"; "strict"] ex_privEnvAssign)
.
Definition name_privEnvAssign : id :=  "%EnvAssign" .
Definition privEnvCreateImmutableBinding := 
value_closure
(closure_intro [("%DeclEnvAddBinding", privDeclEnvAddBinding)] None
 ["context"; "id"] ex_privEnvCreateImmutableBinding)
.
Definition name_privEnvCreateImmutableBinding : id :=  "%EnvCreateImmutableBinding" .
Definition privEnvCreateMutableBinding := 
value_closure
(closure_intro
 [("%AddDataField", privAddDataField);
  ("%DeclEnvAddBinding", privDeclEnvAddBinding)] None
 ["context"; "id"; "configurable"] ex_privEnvCreateMutableBinding)
.
Definition name_privEnvCreateMutableBinding : id :=  "%EnvCreateMutableBinding" .
Definition privEnvCreateSetMutableBinding := 
value_closure
(closure_intro
 [("%EnvCreateMutableBinding", privEnvCreateMutableBinding);
  ("%EnvSetMutableBinding", privEnvSetMutableBinding)] None
 ["context"; "id"; "val"; "configurable"; "strict"]
 ex_privEnvCreateSetMutableBinding)
.
Definition name_privEnvCreateSetMutableBinding : id :=  "%EnvCreateSetMutableBinding" .
Definition privEnvHasBinding := 
value_closure
(closure_intro [("%HasProperty", privHasProperty)] None ["context"; "id"]
 ex_privEnvHasBinding)
.
Definition name_privEnvHasBinding : id :=  "%EnvHasBinding" .
Definition privEnvDefineArg := 
value_closure
(closure_intro
 [("%EnvCreateMutableBinding", privEnvCreateMutableBinding);
  ("%EnvHasBinding", privEnvHasBinding);
  ("%EnvSetMutableBinding", privEnvSetMutableBinding)] None
 ["context"; "id"; "val"; "strict"] ex_privEnvDefineArg)
.
Definition name_privEnvDefineArg : id :=  "%EnvDefineArg" .
Definition privEnvInitializeImmutableBinding := 
value_closure
(closure_intro [] None ["context"; "id"; "val"]
 ex_privEnvInitializeImmutableBinding)
.
Definition name_privEnvInitializeImmutableBinding : id :=  "%EnvInitializeImmutableBinding" .
Definition privThrowTypeError :=  value_object 14 .
Definition name_privThrowTypeError : id :=  "%ThrowTypeError" .
Definition privmkArgsObj := 
value_closure
(closure_intro
 [("%AddAccessorField", privAddAccessorField);
  ("%AddDataField", privAddDataField);
  ("%ObjectProto", privObjectProto);
  ("%ThrowTypeError", privThrowTypeError)] None
 ["context"; "ids"; "args"; "obj"; "strict"] ex_privmkArgsObj)
.
Definition name_privmkArgsObj : id :=  "%mkArgsObj" .
Definition privEnvDefineArgsObjOk := 
value_closure
(closure_intro
 [("%EnvCreateImmutableBinding", privEnvCreateImmutableBinding);
  ("%EnvCreateSetMutableBinding", privEnvCreateSetMutableBinding);
  ("%EnvInitializeImmutableBinding", privEnvInitializeImmutableBinding);
  ("%mkArgsObj", privmkArgsObj)] None
 ["context"; "ids"; "args"; "obj"; "strict"] ex_privEnvDefineArgsObjOk)
.
Definition name_privEnvDefineArgsObjOk : id :=  "%EnvDefineArgsObjOk" .
Definition privEnvDefineArgsObj := 
value_closure
(closure_intro
 [("%EnvDefineArgsObjOk", privEnvDefineArgsObjOk);
  ("%EnvHasBinding", privEnvHasBinding)] None
 ["context"; "ids"; "args"; "obj"; "strict"] ex_privEnvDefineArgsObj)
.
Definition name_privEnvDefineArgsObj : id :=  "%EnvDefineArgsObj" .
Definition privglobalContext :=  value_object 307 .
Definition name_privglobalContext : id :=  "%globalContext" .
Definition privEnvDefineFunc := 
value_closure
(closure_intro
 [("%AddDataField", privAddDataField);
  ("%EnvCreateMutableBinding", privEnvCreateMutableBinding);
  ("%EnvHasBinding", privEnvHasBinding);
  ("%EnvSetMutableBinding", privEnvSetMutableBinding);
  ("%TypeError", privTypeError);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None
 ["context"; "id"; "fo"; "configurableBindings"; "strict"]
 ex_privEnvDefineFunc)
.
Definition name_privEnvDefineFunc : id :=  "%EnvDefineFunc" .
Definition privEnvDefineVar := 
value_closure
(closure_intro
 [("%EnvCreateSetMutableBinding", privEnvCreateSetMutableBinding);
  ("%EnvHasBinding", privEnvHasBinding)] None
 ["context"; "id"; "configurableBindings"; "strict"] ex_privEnvDefineVar)
.
Definition name_privEnvDefineVar : id :=  "%EnvDefineVar" .
Definition privSyntaxErrorProto :=  value_object 6 .
Definition name_privSyntaxErrorProto : id :=  "%SyntaxErrorProto" .
Definition privSyntaxError := 
value_closure
(closure_intro
 [("%NativeError", privNativeError);
  ("%SyntaxErrorProto", privSyntaxErrorProto)] None ["msg"]
 ex_privSyntaxError)
.
Definition name_privSyntaxError : id :=  "%SyntaxError" .
Definition privEnvDelete := 
value_closure
(closure_intro
 [("%Delete", privDelete);
  ("%EnvGetId", privEnvGetId);
  ("%SyntaxError", privSyntaxError)] (Some "%EnvDelete")
 ["context"; "id"; "strict"] ex_privEnvDelete)
.
Definition name_privEnvDelete : id :=  "%EnvDelete" .
Definition privEnvGet := 
value_closure
(closure_intro
 [("%EnvGetId", privEnvGetId); ("%EnvGetValue", privEnvGetValue)] None
 ["context"; "id"; "strict"] ex_privEnvGet)
.
Definition name_privEnvGet : id :=  "%EnvGet" .
Definition privEnvModify := 
value_closure
(closure_intro
 [("%EnvGetId", privEnvGetId);
  ("%EnvGetValue", privEnvGetValue);
  ("%EnvPutValue", privEnvPutValue)] None
 ["context"; "id"; "op"; "val_thunk"; "strict"] ex_privEnvModify)
.
Definition name_privEnvModify : id :=  "%EnvModify" .
Definition privEnvPrepostOp := 
value_closure
(closure_intro
 [("%EnvGetId", privEnvGetId);
  ("%EnvGetValue", privEnvGetValue);
  ("%EnvPutValue", privEnvPutValue);
  ("%ToNumber", privToNumber)] None
 ["context"; "id"; "op"; "is_pre"; "strict"] ex_privEnvPrepostOp)
.
Definition name_privEnvPrepostOp : id :=  "%EnvPrepostOp" .
Definition privEnvTypeof := 
value_closure
(closure_intro
 [("%EnvGetBindingValue", privEnvGetBindingValue);
  ("%EnvGetId", privEnvGetId);
  ("%Typeof", privTypeof)] (Some "%EnvTypeof") ["context"; "id"; "strict"]
 ex_privEnvTypeof)
.
Definition name_privEnvTypeof : id :=  "%EnvTypeof" .
Definition privEqEq := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] (Some "%EqEq")
 ["x1"; "x2"] ex_privEqEq)
.
Definition name_privEqEq : id :=  "%EqEq" .
Definition privErrorProto :=  value_object 3 .
Definition name_privErrorProto : id :=  "proto" .
Definition privErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privErrorProto)] None ["this"; "args"] ex_privErrorConstructor)
.
Definition name_privErrorConstructor : id :=  "%ErrorConstructor" .
Definition privErrorGlobalFuncObj :=  value_object 44 .
Definition name_privErrorGlobalFuncObj : id :=  "%ErrorGlobalFuncObj" .
Definition privEvalErrorProto :=  value_object 7 .
Definition name_privEvalErrorProto : id :=  "proto" .
Definition privEvalErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privEvalErrorProto)] None ["this"; "args"]
 ex_privEvalErrorConstructor)
.
Definition name_privEvalErrorConstructor : id :=  "%EvalErrorConstructor" .
Definition privEvalErrorGlobalFuncObj :=  value_object 46 .
Definition name_privEvalErrorGlobalFuncObj : id :=  "%EvalErrorGlobalFuncObj" .
Definition privevalCall := 
value_closure
(closure_intro
 [("%configurableEval", privconfigurableEval);
  ("%global", privglobal);
  ("%globalContext", privglobalContext)] None ["obj"; "this"; "args"]
 ex_privevalCall)
.
Definition name_privevalCall : id :=  "%evalCall" .
Definition privFunctionConstructor := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%ToString", privToString);
  ("%evalCall", privevalCall)] None ["this"; "args"]
 ex_privFunctionConstructor)
.
Definition name_privFunctionConstructor : id :=  "%FunctionConstructor" .
Definition privFunctionGlobalFuncObj :=  value_object 311 .
Definition name_privFunctionGlobalFuncObj : id :=  "%FunctionGlobalFuncObj" .
Definition privFunctionProto :=  value_object 12 .
Definition name_privFunctionProto : id :=  "%FunctionProto" .
Definition privFunctionProtoCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privFunctionProtoCall)
.
Definition name_privFunctionProtoCall : id :=  "%FunctionProtoCall" .
Definition privGeOp := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"] ex_privGeOp)
.
Definition name_privGeOp : id :=  "%GeOp" .
Definition privGetOp := 
value_closure
(closure_intro [("%GetField", privGetField)] None ["v"; "fld"; "strict"]
 ex_privGetOp)
.
Definition name_privGetOp : id :=  "%GetOp" .
Definition privGtOp := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"] ex_privGtOp)
.
Definition name_privGtOp : id :=  "%GtOp" .
Definition privIsJSError := 
value_closure (closure_intro [] None ["thing"] ex_privIsJSError)
.
Definition name_privIsJSError : id :=  "%IsJSError" .
Definition privLeOp := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"] ex_privLeOp)
.
Definition name_privLeOp : id :=  "%LeOp" .
Definition privLeftShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"] ex_privLeftShift)
.
Definition name_privLeftShift : id :=  "%LeftShift" .
Definition privLocalTime := 
value_closure (closure_intro [] None ["t"] ex_privLocalTime)
.
Definition name_privLocalTime : id :=  "%LocalTime" .
Definition privLtOp := 
value_closure
(closure_intro [("%CompareOp", privCompareOp)] None ["l"; "r"] ex_privLtOp)
.
Definition name_privLtOp : id :=  "%LtOp" .
Definition privmax := 
value_closure (closure_intro [] None ["a"; "b"] ex_privmax)
.
Definition name_privmax : id :=  "%max" .
Definition privMakeBind := 
value_closure
(closure_intro
 [("%BindConstructor", privBindConstructor);
  ("%BindObjCall", privBindObjCall);
  ("%FunctionProto", privFunctionProto);
  ("%ThrowTypeError", privThrowTypeError);
  ("%max", privmax)] None ["obj"; "this"; "args"] ex_privMakeBind)
.
Definition name_privMakeBind : id :=  "%MakeBind" .
Definition privMakeFunctionObject := 
value_closure
(closure_intro
 [("%AddAccessorField", privAddAccessorField);
  ("%AddDataField", privAddDataField);
  ("%DefaultCall", privDefaultCall);
  ("%DefaultConstruct", privDefaultConstruct);
  ("%FunctionProto", privFunctionProto);
  ("%ObjectProto", privObjectProto);
  ("%ThrowTypeError", privThrowTypeError)] None
 ["body"; "len"; "codetxt"; "strict"] ex_privMakeFunctionObject)
.
Definition name_privMakeFunctionObject : id :=  "%MakeFunctionObject" .
Definition privMakeNativeErrorProto := 
value_closure
(closure_intro [("%ErrorProto", privErrorProto)] None ["name"]
 ex_privMakeNativeErrorProto)
.
Definition name_privMakeNativeErrorProto : id :=  "%MakeNativeErrorProto" .
Definition privMakeObject := 
value_closure
(closure_intro [("%ObjectProto", privObjectProto)] None [] ex_privMakeObject)
.
Definition name_privMakeObject : id :=  "%MakeObject" .
Definition privMath :=  value_object 255 .
Definition name_privMath : id :=  "%Math" .
Definition privNativeErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError); ("%ToString", privToString)]
 None ["proto"] ex_privNativeErrorConstructor)
.
Definition name_privNativeErrorConstructor : id :=  "%NativeErrorConstructor" .
Definition privNumberCall := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength); ("%ToNumber", privToNumber)] 
 None ["obj"; "this"; "args"] ex_privNumberCall)
.
Definition name_privNumberCall : id :=  "%NumberCall" .
Definition privNumberConstructor := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%MakeNumber", privMakeNumber);
  ("%ToNumber", privToNumber)] None ["constr"; "args"]
 ex_privNumberConstructor)
.
Definition name_privNumberConstructor : id :=  "%NumberConstructor" .
Definition privNumberGlobalFuncObj :=  value_object 24 .
Definition name_privNumberGlobalFuncObj : id :=  "%NumberGlobalFuncObj" .
Definition privObjectCall := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%MakeObject", privMakeObject);
  ("%ToObject", privToObject)] None ["obj"; "this"; "args"] ex_privObjectCall)
.
Definition name_privObjectCall : id :=  "%ObjectCall" .
Definition privObjectConstructor := 
value_closure
(closure_intro [("%ObjectCall", privObjectCall)] None ["constr"; "args"]
 ex_privObjectConstructor)
.
Definition name_privObjectConstructor : id :=  "%ObjectConstructor" .
Definition privObjectGlobalFuncObj :=  value_object 33 .
Definition name_privObjectGlobalFuncObj : id :=  "%ObjectGlobalFuncObj" .
Definition privObjectTypeCheck := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["o"]
 ex_privObjectTypeCheck)
.
Definition name_privObjectTypeCheck : id :=  "%ObjectTypeCheck" .
Definition privPutPrim := 
value_closure
(closure_intro [("%Put", privPut); ("%ToObject", privToObject)] None
 ["v"; "fld"; "val"; "strict"] ex_privPutPrim)
.
Definition name_privPutPrim : id :=  "%PutPrim" .
Definition privSetField := 
value_closure
(closure_intro [("%Put1", privPut1); ("%PutPrim", privPutPrim)] None
 ["v"; "fld"; "val"; "strict"] ex_privSetField)
.
Definition name_privSetField : id :=  "%SetField" .
Definition privPrepostOp := 
value_closure
(closure_intro
 [("%GetField", privGetField);
  ("%SetField", privSetField);
  ("%ToNumber", privToNumber)] None ["obj"; "fld"; "op"; "is_pre"]
 ex_privPrepostOp)
.
Definition name_privPrepostOp : id :=  "%PrepostOp" .
Definition privPrimAdd := 
value_closure
(closure_intro [("%ToPrimitive", privToPrimitive)] None ["l"; "r"]
 ex_privPrimAdd)
.
Definition name_privPrimAdd : id :=  "%PrimAdd" .
Definition privPrimComma := 
value_closure (closure_intro [] None ["l"; "r"] ex_privPrimComma)
.
Definition name_privPrimComma : id :=  "%PrimComma" .
Definition privPrimMultOp := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["l"; "r"; "op"]
 ex_privPrimMultOp)
.
Definition name_privPrimMultOp : id :=  "%PrimMultOp" .
Definition privPrimDiv := 
value_closure
(closure_intro [("%PrimMultOp", privPrimMultOp)] None ["l"; "r"]
 ex_privPrimDiv)
.
Definition name_privPrimDiv : id :=  "%PrimDiv" .
Definition privPrimMod := 
value_closure
(closure_intro [("%PrimMultOp", privPrimMultOp)] None ["l"; "r"]
 ex_privPrimMod)
.
Definition name_privPrimMod : id :=  "%PrimMod" .
Definition privPrimMult := 
value_closure
(closure_intro [("%PrimMultOp", privPrimMultOp)] None ["l"; "r"]
 ex_privPrimMult)
.
Definition name_privPrimMult : id :=  "%PrimMult" .
Definition privPrimSub := 
value_closure
(closure_intro [("%PrimMultOp", privPrimMultOp)] None ["l"; "r"]
 ex_privPrimSub)
.
Definition name_privPrimSub : id :=  "%PrimSub" .
Definition privPropertyAccess := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["cont"; "o"; "fld"; "strict"]
 ex_privPropertyAccess)
.
Definition name_privPropertyAccess : id :=  "%PropertyAccess" .
Definition privRangeError := 
value_closure
(closure_intro
 [("%NativeError", privNativeError);
  ("%RangeErrorProto", privRangeErrorProto)] None ["msg"] ex_privRangeError)
.
Definition name_privRangeError : id :=  "%RangeError" .
Definition privRangeErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privRangeErrorProto)] None ["this"; "args"]
 ex_privRangeErrorConstructor)
.
Definition name_privRangeErrorConstructor : id :=  "%RangeErrorConstructor" .
Definition privRangeErrorGlobalFuncObj :=  value_object 47 .
Definition name_privRangeErrorGlobalFuncObj : id :=  "%RangeErrorGlobalFuncObj" .
Definition privReferenceErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privReferenceErrorProto)] None ["this"; "args"]
 ex_privReferenceErrorConstructor)
.
Definition name_privReferenceErrorConstructor : id :=  "%ReferenceErrorConstructor" .
Definition privReferenceErrorGlobalFuncObj :=  value_object 48 .
Definition name_privReferenceErrorGlobalFuncObj : id :=  "%ReferenceErrorGlobalFuncObj" .
Definition privRegExpProto :=  value_object 247 .
Definition name_privRegExpProto : id :=  "%RegExpProto" .
Definition privRegExpConstructor := 
value_closure
(closure_intro [("%RegExpProto", privRegExpProto)] None
 ["obj"; "this"; "args"] ex_privRegExpConstructor)
.
Definition name_privRegExpConstructor : id :=  "%RegExpConstructor" .
Definition privRegExpCode := 
value_closure
(closure_intro [("%RegExpConstructor", privRegExpConstructor)] None
 ["obj"; "this"; "args"] ex_privRegExpCode)
.
Definition name_privRegExpCode : id :=  "%RegExpCode" .
Definition privRegExpGlobalFuncObj :=  value_object 248 .
Definition name_privRegExpGlobalFuncObj : id :=  "%RegExpGlobalFuncObj" .
Definition privRunSelfConstructorCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privRunSelfConstructorCall)
.
Definition name_privRunSelfConstructorCall : id :=  "%RunSelfConstructorCall" .
Definition privSetOp := 
value_closure
(closure_intro [("%SetField", privSetField)] None ["cval"] ex_privSetOp)
.
Definition name_privSetOp : id :=  "%SetOp" .
Definition privSignedRightShift := 
value_closure
(closure_intro [("%ToInt32", privToInt32); ("%ToUint32", privToUint32)] 
 None ["l"; "r"] ex_privSignedRightShift)
.
Definition name_privSignedRightShift : id :=  "%SignedRightShift" .
Definition privStringCall := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength); ("%ToString", privToString)] 
 None ["obj"; "this"; "args"] ex_privStringCall)
.
Definition name_privStringCall : id :=  "%StringCall" .
Definition privStringConstructor := 
value_closure
(closure_intro
 [("%MakeString", privMakeString); ("%StringCall", privStringCall)] None
 ["constr"; "args"] ex_privStringConstructor)
.
Definition name_privStringConstructor : id :=  "%StringConstructor" .
Definition privStringGlobalFuncObj :=  value_object 27 .
Definition name_privStringGlobalFuncObj : id :=  "%StringGlobalFuncObj" .
Definition privStxEq := 
value_closure (closure_intro [] None ["x1"; "x2"] ex_privStxEq)
.
Definition name_privStxEq : id :=  "%StxEq" .
Definition privSyntaxErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privSyntaxErrorProto)] None ["this"; "args"]
 ex_privSyntaxErrorConstructor)
.
Definition name_privSyntaxErrorConstructor : id :=  "%SyntaxErrorConstructor" .
Definition privSyntaxErrorGlobalFuncObj :=  value_object 45 .
Definition name_privSyntaxErrorGlobalFuncObj : id :=  "%SyntaxErrorGlobalFuncObj" .
Definition privThrowTypeErrorFun := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privThrowTypeErrorFun)
.
Definition name_privThrowTypeErrorFun : id :=  "%ThrowTypeErrorFun" .
Definition privTimeWithinDay := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["t"] ex_privTimeWithinDay)
.
Definition name_privTimeWithinDay : id :=  "%TimeWithinDay" .
Definition privToPropertyDescriptor := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToBoolean", privToBoolean);
  ("%TypeError", privTypeError);
  ("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["propobj"]
 ex_privToPropertyDescriptor)
.
Definition name_privToPropertyDescriptor : id :=  "%ToPropertyDescriptor" .
Definition privToUint16 := 
value_closure
(closure_intro [("%ToUint", privToUint)] None ["n"] ex_privToUint16)
.
Definition name_privToUint16 : id :=  "%ToUint16" .
Definition privTypeErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privTypeErrorProto)] None ["this"; "args"]
 ex_privTypeErrorConstructor)
.
Definition name_privTypeErrorConstructor : id :=  "%TypeErrorConstructor" .
Definition privTypeErrorGlobalFuncObj :=  value_object 49 .
Definition name_privTypeErrorGlobalFuncObj : id :=  "%TypeErrorGlobalFuncObj" .
Definition privURIErrorProto :=  value_object 50 .
Definition name_privURIErrorProto : id :=  "proto" .
Definition privURIErrorConstructor := 
value_closure
(closure_intro
 [("%MakeNativeError", privMakeNativeError);
  ("%ToString", privToString);
  ("proto", privURIErrorProto)] None ["this"; "args"]
 ex_privURIErrorConstructor)
.
Definition name_privURIErrorConstructor : id :=  "%URIErrorConstructor" .
Definition privURIErrorGlobalFuncObj :=  value_object 51 .
Definition name_privURIErrorGlobalFuncObj : id :=  "%URIErrorGlobalFuncObj" .
Definition privUnaryNeg := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"] ex_privUnaryNeg)
.
Definition name_privUnaryNeg : id :=  "%UnaryNeg" .
Definition privUnaryNot := 
value_closure
(closure_intro [("%ToBoolean", privToBoolean)] None ["expr"] ex_privUnaryNot)
.
Definition name_privUnaryNot : id :=  "%UnaryNot" .
Definition privUnaryPlus := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["expr"] ex_privUnaryPlus)
.
Definition name_privUnaryPlus : id :=  "%UnaryPlus" .
Definition privUnsignedRightShift := 
value_closure
(closure_intro [("%ToUint32", privToUint32)] None ["l"; "r"]
 ex_privUnsignedRightShift)
.
Definition name_privUnsignedRightShift : id :=  "%UnsignedRightShift" .
Definition privVoid := 
value_closure (closure_intro [] None ["val"] ex_privVoid)
.
Definition name_privVoid : id :=  "%Void" .
Definition privacos :=  value_object 264 .
Definition name_privacos : id :=  "%acos" .
Definition privacosCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privacosCall)
.
Definition name_privacosCall : id :=  "%acosCall" .
Definition privapply :=  value_object 18 .
Definition name_privapply : id :=  "%apply" .
Definition privapplyCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["this"; "args"] ex_privapplyCall)
.
Definition name_privapplyCall : id :=  "%applyCall" .
Definition privarrayIndexOf :=  value_object 121 .
Definition name_privarrayIndexOf : id :=  "%arrayIndexOf" .
Definition privarrayIndexOfCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%max", privmax)] None ["obj"; "this"; "args"] ex_privarrayIndexOfCall)
.
Definition name_privarrayIndexOfCall : id :=  "%arrayIndexOfCall" .
Definition privarrayLastIndexOf :=  value_object 124 .
Definition name_privarrayLastIndexOf : id :=  "%arrayLastIndexOf" .
Definition privmin := 
value_closure (closure_intro [] None ["a"; "b"] ex_privmin)
.
Definition name_privmin : id :=  "%min" .
Definition privarrayLastIndexOfCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%min", privmin)] None ["obj"; "this"; "args"] ex_privarrayLastIndexOfCall)
.
Definition name_privarrayLastIndexOfCall : id :=  "%arrayLastIndexOfCall" .
Definition privarrayTLSCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%JSError", privJSError);
  ("%ToObject", privToObject);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%TypeErrorProto", privTypeErrorProto)] None ["obj"; "this"; "args"]
 ex_privarrayTLSCall)
.
Definition name_privarrayTLSCall : id :=  "%arrayTLSCall" .
Definition privarrayToLocaleString :=  value_object 93 .
Definition name_privarrayToLocaleString : id :=  "%arrayToLocaleString" .
Definition privarrayToString :=  value_object 90 .
Definition name_privarrayToString : id :=  "%arrayToString" .
Definition privobjectToStringCall := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["obj"; "this"; "args"]
 ex_privobjectToStringCall)
.
Definition name_privobjectToStringCall : id :=  "%objectToStringCall" .
Definition privarrayToStringCall := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%objectToStringCall", privobjectToStringCall)] None
 ["obj"; "this"; "args"] ex_privarrayToStringCall)
.
Definition name_privarrayToStringCall : id :=  "%arrayToStringCall" .
Definition privasin :=  value_object 266 .
Definition name_privasin : id :=  "%asin" .
Definition privasinCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privasinCall)
.
Definition name_privasinCall : id :=  "%asinCall" .
Definition privassert := 
value_closure (closure_intro [] None ["b"; "s"] ex_privassert)
.
Definition name_privassert : id :=  "%assert" .
Definition privatan :=  value_object 268 .
Definition name_privatan : id :=  "%atan" .
Definition privatan2 :=  value_object 270 .
Definition name_privatan2 : id :=  "%atan2" .
Definition privatan2Call := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privatan2Call)
.
Definition name_privatan2Call : id :=  "%atan2Call" .
Definition privatanCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privatanCall)
.
Definition name_privatanCall : id :=  "%atanCall" .
Definition privbind :=  value_object 150 .
Definition name_privbind : id :=  "%bind" .
Definition privslice :=  value_object 147 .
Definition name_privslice : id :=  "%slice" .
Definition privbindCall := 
value_closure
(closure_intro
 [("%IsCallable", privIsCallable);
  ("%MakeBind", privMakeBind);
  ("%TypeError", privTypeError);
  ("%oneArgObj", privoneArgObj);
  ("%slice", privslice)] None ["obj"; "this"; "args"] ex_privbindCall)
.
Definition name_privbindCall : id :=  "%bindCall" .
Definition privbooleanToString :=  value_object 28 .
Definition name_privbooleanToString : id :=  "%booleanToString" .
Definition privbooleanToStringCall := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privbooleanToStringCall)
.
Definition name_privbooleanToStringCall : id :=  "%booleanToStringCall" .
Definition privbooleanValueOf :=  value_object 296 .
Definition name_privbooleanValueOf : id :=  "%booleanValueOf" .
Definition privcall :=  value_object 17 .
Definition name_privcall : id :=  "%call" .
Definition privlen := 
value_closure (closure_intro [] None ["list"] ex_privlen)
.
Definition name_privlen : id :=  "%len" .
Definition privslice_internal := 
value_closure
(closure_intro [] None ["list"; "min"; "max"] ex_privslice_internal)
.
Definition name_privslice_internal : id :=  "%slice_internal" .
Definition privcallCall := 
value_closure
(closure_intro [("%len", privlen); ("%slice_internal", privslice_internal)]
 None ["this"; "args"] ex_privcallCall)
.
Definition name_privcallCall : id :=  "%callCall" .
Definition privcharAt :=  value_object 103 .
Definition name_privcharAt : id :=  "%charAt" .
Definition privcharAtCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["obj"; "this"; "args"] ex_privcharAtCall)
.
Definition name_privcharAtCall : id :=  "%charAtCall" .
Definition privcharCodeAt :=  value_object 106 .
Definition name_privcharCodeAt : id :=  "%charCodeAt" .
Definition privcharCodeAtCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privcharCodeAtCall)
.
Definition name_privcharCodeAtCall : id :=  "%charCodeAtCall" .
Definition privconcatCall := 
value_closure
(closure_intro
 [("%ArrayConstructor", privArrayConstructor);
  ("%Get1", privGet1);
  ("%Put1", privPut1);
  ("%ToObject", privToObject)] None ["obj"; "this"; "args"] ex_privconcatCall)
.
Definition name_privconcatCall : id :=  "%concatCall" .
Definition privconsole :=  value_object 309 .
Definition name_privconsole : id :=  "%console" .
Definition privcos :=  value_object 272 .
Definition name_privcos : id :=  "%cos" .
Definition privcosCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privcosCall)
.
Definition name_privcosCall : id :=  "%cosCall" .
Definition privcreate :=  value_object 58 .
Definition name_privcreate : id :=  "%create" .
Definition privdefineProperties :=  value_object 56 .
Definition name_privdefineProperties : id :=  "%defineProperties" .
Definition privcreateCall := 
value_closure
(closure_intro
 [("%ToObject", privToObject);
  ("%TypeError", privTypeError);
  ("%defineProperties", privdefineProperties)] None ["obj"; "this"; "args"]
 ex_privcreateCall)
.
Definition name_privcreateCall : id :=  "%createCall" .
Definition privdateGetTimezoneOffset :=  value_object 172 .
Definition name_privdateGetTimezoneOffset : id :=  "%dateGetTimezoneOffset" .
Definition privdateGetTimezoneOffsetCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"]
 ex_privdateGetTimezoneOffsetCall)
.
Definition name_privdateGetTimezoneOffsetCall : id :=  "%dateGetTimezoneOffsetCall" .
Definition privdateToStringCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privdateToStringCall)
.
Definition name_privdateToStringCall : id :=  "%dateToStringCall" .
Definition privdateValueOf :=  value_object 170 .
Definition name_privdateValueOf : id :=  "%dateValueOf" .
Definition privdateValueOfCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privdateValueOfCall)
.
Definition name_privdateValueOfCall : id :=  "%dateValueOfCall" .
Definition privdategetDate :=  value_object 176 .
Definition name_privdategetDate : id :=  "%dategetDate" .
Definition privdategetDateCall := 
value_closure
(closure_intro
 [("%DateFromTime", privDateFromTime); ("%LocalTime", privLocalTime)] 
 None ["obj"; "this"; "args"] ex_privdategetDateCall)
.
Definition name_privdategetDateCall : id :=  "%dategetDateCall" .
Definition privdategetDay :=  value_object 174 .
Definition name_privdategetDay : id :=  "%dategetDay" .
Definition privdategetDayCall := 
value_closure
(closure_intro [("%msPerDay", privmsPerDay)] None ["obj"; "this"; "args"]
 ex_privdategetDayCall)
.
Definition name_privdategetDayCall : id :=  "%dategetDayCall" .
Definition privdecodeURI :=  value_object 250 .
Definition name_privdecodeURI : id :=  "%decodeURI" .
Definition privdecodeURICall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privdecodeURICall)
.
Definition name_privdecodeURICall : id :=  "%decodeURICall" .
Definition privdecodeURIComponent :=  value_object 251 .
Definition name_privdecodeURIComponent : id :=  "%decodeURIComponent" .
Definition privdecodeURIComponentCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privdecodeURIComponentCall)
.
Definition name_privdecodeURIComponentCall : id :=  "%decodeURIComponentCall" .
Definition privdefine15Property := 
value_closure
(closure_intro
 [("%Typeof", privTypeof); ("%defineOwnProperty", privdefineOwnProperty)]
 None ["obj"; "field"; "prop"] ex_privdefine15Property)
.
Definition name_privdefine15Property : id :=  "%define15Property" .
Definition privdefineNYIProperty := 
value_closure
(closure_intro
 [("%FunctionProto", privFunctionProto);
  ("%TypeError", privTypeError);
  ("%define15Property", privdefine15Property)] None ["base"; "name"]
 ex_privdefineNYIProperty)
.
Definition name_privdefineNYIProperty : id :=  "%defineNYIProperty" .
Definition privdefineProperty :=  value_object 16 .
Definition name_privdefineProperty : id :=  "%defineProperty" .
Definition privdefinePropertiesCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToObject", privToObject);
  ("%defineProperty", privdefineProperty)] None ["obj"; "this"; "args"]
 ex_privdefinePropertiesCall)
.
Definition name_privdefinePropertiesCall : id :=  "%definePropertiesCall" .
Definition privdefinePropertyCall := 
value_closure
(closure_intro
 [("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToPropertyDescriptor", privToPropertyDescriptor);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privdefinePropertyCall)
.
Definition name_privdefinePropertyCall : id :=  "%definePropertyCall" .
Definition privencodeURI :=  value_object 252 .
Definition name_privencodeURI : id :=  "%encodeURI" .
Definition privencodeURICall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privencodeURICall)
.
Definition name_privencodeURICall : id :=  "%encodeURICall" .
Definition privencodeURIComponent :=  value_object 253 .
Definition name_privencodeURIComponent : id :=  "%encodeURIComponent" .
Definition privencodeURIComponentCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privencodeURIComponentCall)
.
Definition name_privencodeURIComponentCall : id :=  "%encodeURIComponentCall" .
Definition privescape :=  value_object 314 .
Definition name_privescape : id :=  "%escape" .
Definition privescapeCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privescapeCall)
.
Definition name_privescapeCall : id :=  "%escapeCall" .
Definition privets :=  value_object 22 .
Definition name_privets : id :=  "%ets" .
Definition privetsCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ToString", privToString);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"] ex_privetsCall)
.
Definition name_privetsCall : id :=  "%etsCall" .
Definition privevery :=  value_object 138 .
Definition name_privevery : id :=  "%every" .
Definition priveveryCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_priveveryCall)
.
Definition name_priveveryCall : id :=  "%everyCall" .
Definition privexp :=  value_object 254 .
Definition name_privexp : id :=  "%exp" .
Definition privexpCall := 
value_closure (closure_intro [] None [] ex_privexpCall)
.
Definition name_privexpCall : id :=  "%expCall" .
Definition privfilter :=  value_object 133 .
Definition name_privfilter : id :=  "%filter" .
Definition privfilterCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%MakeArray", privMakeArray);
  ("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privfilterCall)
.
Definition name_privfilterCall : id :=  "%filterCall" .
Definition privforeach :=  value_object 127 .
Definition name_privforeach : id :=  "%foreach" .
Definition privforeachCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privforeachCall)
.
Definition name_privforeachCall : id :=  "%foreachCall" .
Definition privfreeze :=  value_object 62 .
Definition name_privfreeze : id :=  "%freeze" .
Definition privfreezeCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privfreezeCall)
.
Definition name_privfreezeCall : id :=  "%freezeCall" .
Definition privfromCharCode :=  value_object 74 .
Definition name_privfromCharCode : id :=  "%fromCharCode" .
Definition privfromccCall := 
value_closure
(closure_intro [("%ToUint16", privToUint16)] None ["obj"; "this"; "args"]
 ex_privfromccCall)
.
Definition name_privfromccCall : id :=  "%fromccCall" .
Definition privfunctionToString :=  value_object 13 .
Definition name_privfunctionToString : id :=  "%functionToString" .
Definition privfunctionToStringCall := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privfunctionToStringCall)
.
Definition name_privfunctionToStringCall : id :=  "%functionToStringCall" .
Definition privgetMonth :=  value_object 166 .
Definition name_privgetMonth : id :=  "%getMonth" .
Definition privgetMonthCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privgetMonthCall)
.
Definition name_privgetMonthCall : id :=  "%getMonthCall" .
Definition privgetYear :=  value_object 165 .
Definition name_privgetYear : id :=  "%getYear" .
Definition privgetYearCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privgetYearCall)
.
Definition name_privgetYearCall : id :=  "%getYearCall" .
Definition privgopd :=  value_object 36 .
Definition name_privgopd : id :=  "%gopd" .
Definition privgopdCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ObjectProto", privObjectProto);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%ToString", privToString);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privgopdCall)
.
Definition name_privgopdCall : id :=  "%gopdCall" .
Definition privgopn :=  value_object 53 .
Definition name_privgopn : id :=  "%gopn" .
Definition privgopnCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%MakeArray", privMakeArray);
  ("%ObjectTypeCheck", privObjectTypeCheck)] None ["obj"; "this"; "args"]
 ex_privgopnCall)
.
Definition name_privgopnCall : id :=  "%gopnCall" .
Definition privgpo :=  value_object 34 .
Definition name_privgpo : id :=  "%gpo" .
Definition privgpoCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privgpoCall)
.
Definition name_privgpoCall : id :=  "%gpoCall" .
Definition privhasOwnProperty :=  value_object 42 .
Definition name_privhasOwnProperty : id :=  "%hasOwnProperty" .
Definition privhasOwnPropertyCall := 
value_closure
(closure_intro [("%ToObject", privToObject); ("%ToString", privToString)]
 None ["obj"; "this"; "args"] ex_privhasOwnPropertyCall)
.
Definition name_privhasOwnPropertyCall : id :=  "%hasOwnPropertyCall" .
Definition privin := 
value_closure
(closure_intro
 [("%HasProperty", privHasProperty);
  ("%ToString", privToString);
  ("%TypeError", privTypeError)] None ["l"; "r"] ex_privin)
.
Definition name_privin : id :=  "%in" .
Definition privinstanceof := 
value_closure
(closure_intro
 [("%Get1", privGet1); ("%TypeError", privTypeError); ("%Typeof", privTypeof)]
 None ["l"; "r"] ex_privinstanceof)
.
Definition name_privinstanceof : id :=  "%instanceof" .
Definition privisExtensible :=  value_object 70 .
Definition name_privisExtensible : id :=  "%isExtensible" .
Definition privisExtensibleCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privisExtensibleCall)
.
Definition name_privisExtensibleCall : id :=  "%isExtensibleCall" .
Definition privisFinite :=  value_object 312 .
Definition name_privisFinite : id :=  "%isFinite" .
Definition privisFiniteCall := 
value_closure
(closure_intro [("%IsFinite", privIsFinite); ("%ToNumber", privToNumber)]
 None ["obj"; "this"; "args"] ex_privisFiniteCall)
.
Definition name_privisFiniteCall : id :=  "%isFiniteCall" .
Definition privisFrozen :=  value_object 66 .
Definition name_privisFrozen : id :=  "%isFrozen" .
Definition privisFrozenCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privisFrozenCall)
.
Definition name_privisFrozenCall : id :=  "%isFrozenCall" .
Definition privisNaN :=  value_object 21 .
Definition name_privisNaN : id :=  "%isNaN" .
Definition privisNaNCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privisNaNCall)
.
Definition name_privisNaNCall : id :=  "%isNaNCall" .
Definition privisPrototypeOf :=  value_object 43 .
Definition name_privisPrototypeOf : id :=  "%isPrototypeOf" .
Definition privisPrototypeOfCall := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["obj"; "this"; "args"]
 ex_privisPrototypeOfCall)
.
Definition name_privisPrototypeOfCall : id :=  "%isPrototypeOfCall" .
Definition privisSealed :=  value_object 68 .
Definition name_privisSealed : id :=  "%isSealed" .
Definition privisSealedCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privisSealedCall)
.
Definition name_privisSealedCall : id :=  "%isSealedCall" .
Definition privjoin :=  value_object 76 .
Definition name_privjoin : id :=  "%join" .
Definition privjoinCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"] ex_privjoinCall)
.
Definition name_privjoinCall : id :=  "%joinCall" .
Definition privkeys :=  value_object 72 .
Definition name_privkeys : id :=  "%keys" .
Definition privkeysCall := 
value_closure
(closure_intro
 [("%MakeArray", privMakeArray);
  ("%ObjectTypeCheck", privObjectTypeCheck);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privkeysCall)
.
Definition name_privkeysCall : id :=  "%keysCall" .
Definition privlocaleCompare :=  value_object 159 .
Definition name_privlocaleCompare : id :=  "%localeCompare" .
Definition privlocaleCompareCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privlocaleCompareCall)
.
Definition name_privlocaleCompareCall : id :=  "%localeCompareCall" .
Definition privlog :=  value_object 308 .
Definition name_privlog : id :=  "%log" .
Definition privlogCall := 
value_closure
(closure_intro [("%HasProperty", privHasProperty)] None
 ["obj"; "this"; "args"] ex_privlogCall)
.
Definition name_privlogCall : id :=  "%logCall" .
Definition privmap :=  value_object 130 .
Definition name_privmap : id :=  "%map" .
Definition privmapCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%MakeArray", privMakeArray);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privmapCall)
.
Definition name_privmapCall : id :=  "%mapCall" .
Definition privmathAbs :=  value_object 262 .
Definition name_privmathAbs : id :=  "%mathAbs" .
Definition privmathAbsCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privmathAbsCall)
.
Definition name_privmathAbsCall : id :=  "%mathAbsCall" .
Definition privmathCeil :=  value_object 286 .
Definition name_privmathCeil : id :=  "%mathCeil" .
Definition privmathCeilCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privmathCeilCall)
.
Definition name_privmathCeilCall : id :=  "%mathCeilCall" .
Definition privmathFloor :=  value_object 288 .
Definition name_privmathFloor : id :=  "%mathFloor" .
Definition privmathFloorCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privmathFloorCall)
.
Definition name_privmathFloorCall : id :=  "%mathFloorCall" .
Definition privmathLog :=  value_object 284 .
Definition name_privmathLog : id :=  "%mathLog" .
Definition privmathLogCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privmathLogCall)
.
Definition name_privmathLogCall : id :=  "%mathLogCall" .
Definition privmathMax :=  value_object 259 .
Definition name_privmathMax : id :=  "%mathMax" .
Definition privminMaxCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None
 ["this"; "args"; "op"; "init"] ex_privminMaxCall)
.
Definition name_privminMaxCall : id :=  "%minMaxCall" .
Definition privmathMaxCall := 
value_closure
(closure_intro [("%max", privmax); ("%minMaxCall", privminMaxCall)] None
 ["obj"; "this"; "args"] ex_privmathMaxCall)
.
Definition name_privmathMaxCall : id :=  "%mathMaxCall" .
Definition privmathMin :=  value_object 256 .
Definition name_privmathMin : id :=  "%mathMin" .
Definition privmathMinCall := 
value_closure
(closure_intro [("%min", privmin); ("%minMaxCall", privminMaxCall)] None
 ["obj"; "this"; "args"] ex_privmathMinCall)
.
Definition name_privmathMinCall : id :=  "%mathMinCall" .
Definition privmathPow :=  value_object 290 .
Definition name_privmathPow : id :=  "%mathPow" .
Definition privmathPowCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privmathPowCall)
.
Definition name_privmathPowCall : id :=  "%mathPowCall" .
Definition privnewDeclEnvRec := 
value_closure (closure_intro [] None ["parent"] ex_privnewDeclEnvRec)
.
Definition name_privnewDeclEnvRec : id :=  "%newDeclEnvRec" .
Definition privnewObjEnvRec := 
value_closure
(closure_intro [] None ["parent"; "obj"; "pt"] ex_privnewObjEnvRec)
.
Definition name_privnewObjEnvRec : id :=  "%newObjEnvRec" .
Definition privnotEqEq := 
value_closure
(closure_intro [("%EqEq", privEqEq)] None ["x1"; "x2"] ex_privnotEqEq)
.
Definition name_privnotEqEq : id :=  "%notEqEq" .
Definition privnotStxEq := 
value_closure
(closure_intro [("%StxEq", privStxEq)] None ["x1"; "x2"] ex_privnotStxEq)
.
Definition name_privnotStxEq : id :=  "%notStxEq" .
Definition privnumTLS :=  value_object 301 .
Definition name_privnumTLS : id :=  "%numTLS" .
Definition privtoLocaleString :=  value_object 40 .
Definition name_privtoLocaleString : id :=  "%toLocaleString" .
Definition privnumTLSCall := 
value_closure
(closure_intro
 [("%StringProto", privStringProto); ("%toLocaleString", privtoLocaleString)]
 None ["obj"; "this"; "args"] ex_privnumTLSCall)
.
Definition name_privnumTLSCall : id :=  "%numTLSCall" .
Definition privnumToStringAbstract := 
value_closure (closure_intro [] None ["n"; "r"] ex_privnumToStringAbstract)
.
Definition name_privnumToStringAbstract : id :=  "%numToStringAbstract" .
Definition privnumberPrimval := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["this"]
 ex_privnumberPrimval)
.
Definition name_privnumberPrimval : id :=  "%numberPrimval" .
Definition privnumberToString :=  value_object 153 .
Definition name_privnumberToString : id :=  "%numberToString" .
Definition privnumberToStringCall := 
value_closure
(closure_intro
 [("%RangeError", privRangeError);
  ("%ToInteger", privToInteger);
  ("%numToStringAbstract", privnumToStringAbstract);
  ("%numberPrimval", privnumberPrimval)] None ["obj"; "this"; "args"]
 ex_privnumberToStringCall)
.
Definition name_privnumberToStringCall : id :=  "%numberToStringCall" .
Definition privnumberValueOf :=  value_object 294 .
Definition name_privnumberValueOf : id :=  "%numberValueOf" .
Definition privobjectToString :=  value_object 38 .
Definition name_privobjectToString : id :=  "%objectToString" .
Definition privobjectValueOf :=  value_object 41 .
Definition name_privobjectValueOf : id :=  "%objectValueOf" .
Definition privobjectValueOfCall := 
value_closure
(closure_intro [("%ToObject", privToObject)] None ["obj"; "this"; "args"]
 ex_privobjectValueOfCall)
.
Definition name_privobjectValueOfCall : id :=  "%objectValueOfCall" .
Definition privparseFloat :=  value_object 313 .
Definition name_privparseFloat : id :=  "%parseFloat" .
Definition privparseFloatCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privparseFloatCall)
.
Definition name_privparseFloatCall : id :=  "%parseFloatCall" .
Definition privparseInt :=  value_object 249 .
Definition name_privparseInt : id :=  "%parseInt" .
Definition privparseIntCall := 
value_closure
(closure_intro [("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privparseIntCall)
.
Definition name_privparseIntCall : id :=  "%parseIntCall" .
Definition privpop :=  value_object 78 .
Definition name_privpop : id :=  "%pop" .
Definition privpopCall := 
value_closure
(closure_intro
 [("%Delete", privDelete);
  ("%Get1", privGet1);
  ("%Put1", privPut1);
  ("%ToNumber", privToNumber);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"] ex_privpopCall)
.
Definition name_privpopCall : id :=  "%popCall" .
Definition privpreventExtensions :=  value_object 64 .
Definition name_privpreventExtensions : id :=  "%preventExtensions" .
Definition privpreventExtensionsCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privpreventExtensionsCall)
.
Definition name_privpreventExtensionsCall : id :=  "%preventExtensionsCall" .
Definition privprimEach := 
value_closure
(closure_intro [("%Get1", privGet1); ("%ToString", privToString)] None
 ["arr"; "fn"] ex_privprimEach)
.
Definition name_privprimEach : id :=  "%primEach" .
Definition privprint :=  value_object 15 .
Definition name_privprint : id :=  "%print" .
Definition privprintCall := 
value_closure
(closure_intro [("%ToString", privToString)] None ["obj"; "o"; "s"]
 ex_privprintCall)
.
Definition name_privprintCall : id :=  "%printCall" .
Definition privpropEnum :=  value_object 39 .
Definition name_privpropEnum : id :=  "%propEnum" .
Definition privpropEnumCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ToObject", privToObject);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privpropEnumCall)
.
Definition name_privpropEnumCall : id :=  "%propEnumCall" .
Definition privpropertyNames := 
value_closure
(closure_intro [] None ["obj"; "get-non-enumerable"] ex_privpropertyNames)
.
Definition name_privpropertyNames : id :=  "%propertyNames" .
Definition privprotoOfField := 
value_closure
(closure_intro [] (Some "%protoOfField") ["object"; "fld"]
 ex_privprotoOfField)
.
Definition name_privprotoOfField : id :=  "%protoOfField" .
Definition privpush :=  value_object 81 .
Definition name_privpush : id :=  "%push" .
Definition privpushCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%SetField", privSetField);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"] ex_privpushCall)
.
Definition name_privpushCall : id :=  "%pushCall" .
Definition privrandom :=  value_object 274 .
Definition name_privrandom : id :=  "%random" .
Definition privrandomCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privrandomCall)
.
Definition name_privrandomCall : id :=  "%randomCall" .
Definition privreduce :=  value_object 135 .
Definition name_privreduce : id :=  "%reduce" .
Definition privreduceCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privreduceCall)
.
Definition name_privreduceCall : id :=  "%reduceCall" .
Definition privreduceRight :=  value_object 144 .
Definition name_privreduceRight : id :=  "%reduceRight" .
Definition privreduceRightCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privreduceRightCall)
.
Definition name_privreduceRightCall : id :=  "%reduceRightCall" .
Definition privreplace :=  value_object 157 .
Definition name_privreplace : id :=  "%replace" .
Definition privstringIndexOf :=  value_object 156 .
Definition name_privstringIndexOf : id :=  "%stringIndexOf" .
Definition privsubstring :=  value_object 112 .
Definition name_privsubstring : id :=  "%substring" .
Definition privtwoArgObj := 
value_closure (closure_intro [] None ["arg1"; "arg2"] ex_privtwoArgObj)
.
Definition name_privtwoArgObj : id :=  "%twoArgObj" .
Definition privreplaceCall := 
value_closure
(closure_intro
 [("%IsCallable", privIsCallable);
  ("%ToString", privToString);
  ("%oneArgObj", privoneArgObj);
  ("%stringIndexOf", privstringIndexOf);
  ("%substring", privsubstring);
  ("%twoArgObj", privtwoArgObj)] None ["obj"; "this"; "args"]
 ex_privreplaceCall)
.
Definition name_privreplaceCall : id :=  "%replaceCall" .
Definition privreverse :=  value_object 84 .
Definition name_privreverse : id :=  "%reverse" .
Definition privreverseCall := 
value_closure
(closure_intro
 [("%Delete", privDelete);
  ("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%Put1", privPut1);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"]
 ex_privreverseCall)
.
Definition name_privreverseCall : id :=  "%reverseCall" .
Definition privround :=  value_object 276 .
Definition name_privround : id :=  "%round" .
Definition privroundCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privroundCall)
.
Definition name_privroundCall : id :=  "%roundCall" .
Definition privseal :=  value_object 60 .
Definition name_privseal : id :=  "%seal" .
Definition privsealCall := 
value_closure
(closure_intro [("%ObjectTypeCheck", privObjectTypeCheck)] None
 ["obj"; "this"; "args"] ex_privsealCall)
.
Definition name_privsealCall : id :=  "%sealCall" .
Definition privset_property := 
value_closure
(closure_intro
 [("%ArrayLengthChange", privArrayLengthChange);
  ("%Get1", privGet1);
  ("%JSError", privJSError);
  ("%Put1", privPut1);
  ("%RangeErrorProto", privRangeErrorProto);
  ("%ToNumber", privToNumber);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "fld"; "val"]
 ex_privset_property)
.
Definition name_privset_property : id :=  "%set-property" .
Definition privshift :=  value_object 87 .
Definition name_privshift : id :=  "%shift" .
Definition privshiftCall := 
value_closure
(closure_intro
 [("%Delete", privDelete);
  ("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%Put1", privPut1);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"] ex_privshiftCall)
.
Definition name_privshiftCall : id :=  "%shiftCall" .
Definition privsin :=  value_object 278 .
Definition name_privsin : id :=  "%sin" .
Definition privsinCall := 
value_closure
(closure_intro [("%ToNumber", privToNumber)] None ["obj"; "this"; "args"]
 ex_privsinCall)
.
Definition name_privsinCall : id :=  "%sinCall" .
Definition privsliceCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%MakeArray", privMakeArray);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty)] None ["obj"; "this"; "args"]
 ex_privsliceCall)
.
Definition name_privsliceCall : id :=  "%sliceCall" .
Definition privsome :=  value_object 141 .
Definition name_privsome : id :=  "%some" .
Definition privsomeCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%ToBoolean", privToBoolean);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"] ex_privsomeCall)
.
Definition name_privsomeCall : id :=  "%someCall" .
Definition privsort :=  value_object 98 .
Definition name_privsort : id :=  "%sort" .
Definition privsortCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%IsCallable", privIsCallable);
  ("%JSError", privJSError);
  ("%Put1", privPut1);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%TypeErrorProto", privTypeErrorProto)] None ["obj"; "this"; "args"]
 ex_privsortCall)
.
Definition name_privsortCall : id :=  "%sortCall" .
Definition privsplice :=  value_object 115 .
Definition name_privsplice : id :=  "%splice" .
Definition privspliceCall := 
value_closure
(closure_intro
 [("%Delete", privDelete);
  ("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%MakeArray", privMakeArray);
  ("%Put1", privPut1);
  ("%ToInteger", privToInteger);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32);
  ("%defineOwnProperty", privdefineOwnProperty);
  ("%max", privmax);
  ("%min", privmin)] None ["obj"; "this"; "args"] ex_privspliceCall)
.
Definition name_privspliceCall : id :=  "%spliceCall" .
Definition privsplit :=  value_object 163 .
Definition name_privsplit : id :=  "%split" .
Definition privsplitCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privsplitCall)
.
Definition name_privsplitCall : id :=  "%splitCall" .
Definition privsqrt :=  value_object 280 .
Definition name_privsqrt : id :=  "%sqrt" .
Definition privsqrtCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privsqrtCall)
.
Definition name_privsqrtCall : id :=  "%sqrtCall" .
Definition privstringConcat :=  value_object 109 .
Definition name_privstringConcat : id :=  "%stringConcat" .
Definition privstringConcatCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privstringConcatCall)
.
Definition name_privstringConcatCall : id :=  "%stringConcatCall" .
Definition privstringIndexOfCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["obj"; "this"; "args"] ex_privstringIndexOfCall)
.
Definition name_privstringIndexOfCall : id :=  "%stringIndexOfCall" .
Definition privstringLastIndexOf :=  value_object 158 .
Definition name_privstringLastIndexOf : id :=  "%stringLastIndexOf" .
Definition privstringLastIndexOfCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToNumber", privToNumber);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["obj"; "this"; "args"]
 ex_privstringLastIndexOfCall)
.
Definition name_privstringLastIndexOfCall : id :=  "%stringLastIndexOfCall" .
Definition privstringSlice :=  value_object 160 .
Definition name_privstringSlice : id :=  "%stringSlice" .
Definition privstringSliceCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["obj"; "this"; "args"] ex_privstringSliceCall)
.
Definition name_privstringSliceCall : id :=  "%stringSliceCall" .
Definition privstringToString :=  value_object 25 .
Definition name_privstringToString : id :=  "%stringToString" .
Definition privstringToStringCall := 
value_closure
(closure_intro [("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privstringToStringCall)
.
Definition name_privstringToStringCall : id :=  "%stringToStringCall" .
Definition privstringValueOf :=  value_object 292 .
Definition name_privstringValueOf : id :=  "%stringValueOf" .
Definition privsubstringCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%max", privmax);
  ("%min", privmin)] None ["obj"; "this"; "args"] ex_privsubstringCall)
.
Definition name_privsubstringCall : id :=  "%substringCall" .
Definition privtan :=  value_object 282 .
Definition name_privtan : id :=  "%tan" .
Definition privtanCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privtanCall)
.
Definition name_privtanCall : id :=  "%tanCall" .
Definition privtest :=  value_object 246 .
Definition name_privtest : id :=  "%test" .
Definition privtestCall := 
value_closure (closure_intro [] None ["obj"; "this"; "args"] ex_privtestCall)
.
Definition name_privtestCall : id :=  "%testCall" .
Definition privtoExponential :=  value_object 303 .
Definition name_privtoExponential : id :=  "%toExponential" .
Definition privtoExponentialCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privtoExponentialCall)
.
Definition name_privtoExponentialCall : id :=  "%toExponentialCall" .
Definition privtoFixed :=  value_object 298 .
Definition name_privtoFixed : id :=  "%toFixed" .
Definition privtoFixedCall := 
value_closure
(closure_intro
 [("%RangeError", privRangeError);
  ("%ToInteger", privToInteger);
  ("%ToString", privToString);
  ("%numberPrimval", privnumberPrimval)] None ["obj"; "this"; "args"]
 ex_privtoFixedCall)
.
Definition name_privtoFixedCall : id :=  "%toFixedCall" .
Definition privtoLocaleStringCall := 
value_closure
(closure_intro
 [("%Get1", privGet1);
  ("%ToObject", privToObject);
  ("%TypeError", privTypeError)] None ["obj"; "this"; "args"]
 ex_privtoLocaleStringCall)
.
Definition name_privtoLocaleStringCall : id :=  "%toLocaleStringCall" .
Definition privtoLowerCase :=  value_object 161 .
Definition name_privtoLowerCase : id :=  "%toLowerCase" .
Definition privtoLowerCaseCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privtoLowerCaseCall)
.
Definition name_privtoLowerCaseCall : id :=  "%toLowerCaseCall" .
Definition privtoPrecision :=  value_object 305 .
Definition name_privtoPrecision : id :=  "%toPrecision" .
Definition privtoPrecisionCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privtoPrecisionCall)
.
Definition name_privtoPrecisionCall : id :=  "%toPrecisionCall" .
Definition privtoUpperCase :=  value_object 162 .
Definition name_privtoUpperCase : id :=  "%toUpperCase" .
Definition privtoUpperCaseCall := 
value_closure
(closure_intro
 [("%CheckObjectCoercible", privCheckObjectCoercible);
  ("%ToString", privToString)] None ["obj"; "this"; "args"]
 ex_privtoUpperCaseCall)
.
Definition name_privtoUpperCaseCall : id :=  "%toUpperCaseCall" .
Definition privunescape :=  value_object 316 .
Definition name_privunescape : id :=  "%unescape" .
Definition privunescapeCall := 
value_closure
(closure_intro [] None ["obj"; "this"; "args"] ex_privunescapeCall)
.
Definition name_privunescapeCall : id :=  "%unescapeCall" .
Definition privunshift :=  value_object 118 .
Definition name_privunshift : id :=  "%unshift" .
Definition privunshiftCall := 
value_closure
(closure_intro
 [("%ComputeLength", privComputeLength);
  ("%Delete", privDelete);
  ("%Get1", privGet1);
  ("%HasProperty", privHasProperty);
  ("%Put1", privPut1);
  ("%ToObject", privToObject);
  ("%ToString", privToString);
  ("%ToUint32", privToUint32)] None ["obj"; "this"; "args"]
 ex_privunshiftCall)
.
Definition name_privunshiftCall : id :=  "%unshiftCall" .
Definition privvalueOfCall := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("%Typeof", privTypeof)] 
 None ["this"; "args"; "proto"; "typestr"] ex_privvalueOfCall)
.
Definition name_privvalueOfCall : id :=  "%valueOfCall" .
Definition isAccessorField := 
value_closure (closure_intro [] None ["obj"; "field"] ex_isAccessorField)
.
Definition name_isAccessorField : id :=  "isAccessorField" .
Definition isDataField := 
value_closure (closure_intro [] None ["obj"; "field"] ex_isDataField)
.
Definition name_isDataField : id :=  "isDataField" .
Definition isGenericDescriptor := 
value_closure
(closure_intro
 [("isAccessorDescriptor", isAccessorDescriptor);
  ("isDataDescriptor", isDataDescriptor)] None ["attr-obj"]
 ex_isGenericDescriptor)
.
Definition name_isGenericDescriptor : id :=  "isGenericDescriptor" .
Definition isGenericField := 
value_closure
(closure_intro
 [("isAccessorField", isAccessorField); ("isDataField", isDataField)] 
 None ["obj"; "field"] ex_isGenericField)
.
Definition name_isGenericField : id :=  "isGenericField" .
Definition name :=  value_string "parse" .
Definition name_name : id :=  "name" .
Definition objCode1 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name)] None
 ["obj"; "this"; "args"] ex_objCode1)
.
Definition name_objCode1 : id :=  "objCode" .
Definition name1 :=  value_string "UTC" .
Definition name_name1 : id :=  "name" .
Definition objCode2 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name1)] None
 ["obj"; "this"; "args"] ex_objCode2)
.
Definition name_objCode2 : id :=  "objCode" .
Definition name2 :=  value_string "getTime" .
Definition name_name2 : id :=  "name" .
Definition objCode3 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name2)] None
 ["obj"; "this"; "args"] ex_objCode3)
.
Definition name_objCode3 : id :=  "objCode" .
Definition name3 :=  value_string "getFullYear" .
Definition name_name3 : id :=  "name" .
Definition objCode4 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name3)] None
 ["obj"; "this"; "args"] ex_objCode4)
.
Definition name_objCode4 : id :=  "objCode" .
Definition name4 :=  value_string "getUTCFullYear" .
Definition name_name4 : id :=  "name" .
Definition objCode5 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name4)] None
 ["obj"; "this"; "args"] ex_objCode5)
.
Definition name_objCode5 : id :=  "objCode" .
Definition name5 :=  value_string "getUTCMonth" .
Definition name_name5 : id :=  "name" .
Definition objCode6 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name5)] None
 ["obj"; "this"; "args"] ex_objCode6)
.
Definition name_objCode6 : id :=  "objCode" .
Definition name6 :=  value_string "getUTCDate" .
Definition name_name6 : id :=  "name" .
Definition objCode7 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name6)] None
 ["obj"; "this"; "args"] ex_objCode7)
.
Definition name_objCode7 : id :=  "objCode" .
Definition name7 :=  value_string "getUTCDay" .
Definition name_name7 : id :=  "name" .
Definition objCode8 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name7)] None
 ["obj"; "this"; "args"] ex_objCode8)
.
Definition name_objCode8 : id :=  "objCode" .
Definition name8 :=  value_string "getHours" .
Definition name_name8 : id :=  "name" .
Definition objCode9 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name8)] None
 ["obj"; "this"; "args"] ex_objCode9)
.
Definition name_objCode9 : id :=  "objCode" .
Definition name9 :=  value_string "getUTCHours" .
Definition name_name9 : id :=  "name" .
Definition objCode10 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name9)] None
 ["obj"; "this"; "args"] ex_objCode10)
.
Definition name_objCode10 : id :=  "objCode" .
Definition name10 :=  value_string "getMinutes" .
Definition name_name10 : id :=  "name" .
Definition objCode11 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name10)] None
 ["obj"; "this"; "args"] ex_objCode11)
.
Definition name_objCode11 : id :=  "objCode" .
Definition name11 :=  value_string "getUTCMinutes" .
Definition name_name11 : id :=  "name" .
Definition objCode12 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name11)] None
 ["obj"; "this"; "args"] ex_objCode12)
.
Definition name_objCode12 : id :=  "objCode" .
Definition name12 :=  value_string "getSeconds" .
Definition name_name12 : id :=  "name" .
Definition objCode13 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name12)] None
 ["obj"; "this"; "args"] ex_objCode13)
.
Definition name_objCode13 : id :=  "objCode" .
Definition name13 :=  value_string "getUTCSeconds" .
Definition name_name13 : id :=  "name" .
Definition objCode14 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name13)] None
 ["obj"; "this"; "args"] ex_objCode14)
.
Definition name_objCode14 : id :=  "objCode" .
Definition name14 :=  value_string "getMilliseconds" .
Definition name_name14 : id :=  "name" .
Definition objCode15 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name14)] None
 ["obj"; "this"; "args"] ex_objCode15)
.
Definition name_objCode15 : id :=  "objCode" .
Definition name15 :=  value_string "getUTCMilliseconds" .
Definition name_name15 : id :=  "name" .
Definition objCode16 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name15)] None
 ["obj"; "this"; "args"] ex_objCode16)
.
Definition name_objCode16 : id :=  "objCode" .
Definition name16 :=  value_string "setTime" .
Definition name_name16 : id :=  "name" .
Definition objCode17 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name16)] None
 ["obj"; "this"; "args"] ex_objCode17)
.
Definition name_objCode17 : id :=  "objCode" .
Definition name17 :=  value_string "setMilliseconds" .
Definition name_name17 : id :=  "name" .
Definition objCode18 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name17)] None
 ["obj"; "this"; "args"] ex_objCode18)
.
Definition name_objCode18 : id :=  "objCode" .
Definition name18 :=  value_string "setUTCMilliseconds" .
Definition name_name18 : id :=  "name" .
Definition objCode19 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name18)] None
 ["obj"; "this"; "args"] ex_objCode19)
.
Definition name_objCode19 : id :=  "objCode" .
Definition name19 :=  value_string "setSeconds" .
Definition name_name19 : id :=  "name" .
Definition objCode20 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name19)] None
 ["obj"; "this"; "args"] ex_objCode20)
.
Definition name_objCode20 : id :=  "objCode" .
Definition name20 :=  value_string "setUTCSeconds" .
Definition name_name20 : id :=  "name" .
Definition objCode21 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name20)] None
 ["obj"; "this"; "args"] ex_objCode21)
.
Definition name_objCode21 : id :=  "objCode" .
Definition name21 :=  value_string "setMinutes" .
Definition name_name21 : id :=  "name" .
Definition objCode22 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name21)] None
 ["obj"; "this"; "args"] ex_objCode22)
.
Definition name_objCode22 : id :=  "objCode" .
Definition name22 :=  value_string "setUTCMinutes" .
Definition name_name22 : id :=  "name" .
Definition objCode23 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name22)] None
 ["obj"; "this"; "args"] ex_objCode23)
.
Definition name_objCode23 : id :=  "objCode" .
Definition name23 :=  value_string "setHours" .
Definition name_name23 : id :=  "name" .
Definition objCode24 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name23)] None
 ["obj"; "this"; "args"] ex_objCode24)
.
Definition name_objCode24 : id :=  "objCode" .
Definition name24 :=  value_string "setUTCHours" .
Definition name_name24 : id :=  "name" .
Definition objCode25 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name24)] None
 ["obj"; "this"; "args"] ex_objCode25)
.
Definition name_objCode25 : id :=  "objCode" .
Definition name25 :=  value_string "setDate" .
Definition name_name25 : id :=  "name" .
Definition objCode26 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name25)] None
 ["obj"; "this"; "args"] ex_objCode26)
.
Definition name_objCode26 : id :=  "objCode" .
Definition name26 :=  value_string "setUTCDate" .
Definition name_name26 : id :=  "name" .
Definition objCode27 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name26)] None
 ["obj"; "this"; "args"] ex_objCode27)
.
Definition name_objCode27 : id :=  "objCode" .
Definition name27 :=  value_string "setMonth" .
Definition name_name27 : id :=  "name" .
Definition objCode28 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name27)] None
 ["obj"; "this"; "args"] ex_objCode28)
.
Definition name_objCode28 : id :=  "objCode" .
Definition name28 :=  value_string "setUTCMonth" .
Definition name_name28 : id :=  "name" .
Definition objCode29 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name28)] None
 ["obj"; "this"; "args"] ex_objCode29)
.
Definition name_objCode29 : id :=  "objCode" .
Definition name29 :=  value_string "setFullYear" .
Definition name_name29 : id :=  "name" .
Definition objCode30 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name29)] None
 ["obj"; "this"; "args"] ex_objCode30)
.
Definition name_objCode30 : id :=  "objCode" .
Definition name30 :=  value_string "setUTCFullYear" .
Definition name_name30 : id :=  "name" .
Definition objCode31 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name30)] None
 ["obj"; "this"; "args"] ex_objCode31)
.
Definition name_objCode31 : id :=  "objCode" .
Definition name31 :=  value_string "toUTCString" .
Definition name_name31 : id :=  "name" .
Definition objCode32 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name31)] None
 ["obj"; "this"; "args"] ex_objCode32)
.
Definition name_objCode32 : id :=  "objCode" .
Definition name32 :=  value_string "toGMTString" .
Definition name_name32 : id :=  "name" .
Definition objCode33 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name32)] None
 ["obj"; "this"; "args"] ex_objCode33)
.
Definition name_objCode33 : id :=  "objCode" .
Definition name33 :=  value_string "setYear" .
Definition name_name33 : id :=  "name" .
Definition objCode34 := 
value_closure
(closure_intro [("%TypeError", privTypeError); ("name", name33)] None
 ["obj"; "this"; "args"] ex_objCode34)
.
Definition name_objCode34 : id :=  "objCode" .
Definition objCode35 := 
value_closure
(closure_intro
 [("%StringProto", privStringProto); ("%valueOfCall", privvalueOfCall)] 
 None ["obj"; "this"; "args"] ex_objCode35)
.
Definition name_objCode35 : id :=  "objCode" .
Definition objCode36 := 
value_closure
(closure_intro
 [("%NumberProto", privNumberProto); ("%valueOfCall", privvalueOfCall)] 
 None ["obj"; "this"; "args"] ex_objCode36)
.
Definition name_objCode36 : id :=  "objCode" .
Definition objCode37 := 
value_closure
(closure_intro
 [("%BooleanProto", privBooleanProto); ("%valueOfCall", privvalueOfCall)]
 None ["obj"; "this"; "args"] ex_objCode37)
.
Definition name_objCode37 : id :=  "objCode" .
Definition ctx_items := 
[(name_privAddAccessorField, privAddAccessorField);
 (name_privAddDataField, privAddDataField);
 (name_privAppExpr, privAppExpr);
 (name_privAppExprCheck, privAppExprCheck);
 (name_privAppMethodOp, privAppMethodOp);
 (name_privArrayCall, privArrayCall);
 (name_privArrayConstructor, privArrayConstructor);
 (name_privArrayGlobalFuncObj, privArrayGlobalFuncObj);
 (name_privArrayIdx, privArrayIdx);
 (name_privArrayLengthChange, privArrayLengthChange);
 (name_privArrayProto, privArrayProto);
 (name_privBindConstructor, privBindConstructor);
 (name_privBindObjCall, privBindObjCall);
 (name_privBitwiseAnd, privBitwiseAnd);
 (name_privBitwiseInfix, privBitwiseInfix);
 (name_privBitwiseNot, privBitwiseNot);
 (name_privBitwiseOr, privBitwiseOr);
 (name_privBitwiseXor, privBitwiseXor);
 (name_privBooleanCall, privBooleanCall);
 (name_privBooleanConstructor, privBooleanConstructor);
 (name_privBooleanGlobalFuncObj, privBooleanGlobalFuncObj);
 (name_privBooleanProto, privBooleanProto);
 (name_privCheckObjectCoercible, privCheckObjectCoercible);
 (name_privCompareOp, privCompareOp);
 (name_privComputeLength, privComputeLength);
 (name_privDateCall, privDateCall);
 (name_privDateConstructor, privDateConstructor);
 (name_privDateFromTime, privDateFromTime);
 (name_privDateGlobalFuncObj, privDateGlobalFuncObj);
 (name_privDateProto, privDateProto);
 (name_privDay, privDay);
 (name_privDayFromYear, privDayFromYear);
 (name_privDayWithinYear, privDayWithinYear);
 (name_privDaysInMonth, privDaysInMonth);
 (name_privDaysInYear, privDaysInYear);
 (name_privDeclEnvAddBinding, privDeclEnvAddBinding);
 (name_privDefaultCall, privDefaultCall);
 (name_privDefaultConstruct, privDefaultConstruct);
 (name_privDelete, privDelete);
 (name_privDeleteOp, privDeleteOp);
 (name_privEnvAppExpr, privEnvAppExpr);
 (name_privEnvAssign, privEnvAssign);
 (name_privEnvCreateImmutableBinding, privEnvCreateImmutableBinding);
 (name_privEnvCreateMutableBinding, privEnvCreateMutableBinding);
 (name_privEnvCreateSetMutableBinding, privEnvCreateSetMutableBinding);
 (name_privEnvDefineArg, privEnvDefineArg);
 (name_privEnvDefineArgsObj, privEnvDefineArgsObj);
 (name_privEnvDefineArgsObjOk, privEnvDefineArgsObjOk);
 (name_privEnvDefineFunc, privEnvDefineFunc);
 (name_privEnvDefineVar, privEnvDefineVar);
 (name_privEnvDelete, privEnvDelete);
 (name_privEnvGet, privEnvGet);
 (name_privEnvGetBindingValue, privEnvGetBindingValue);
 (name_privEnvGetId, privEnvGetId);
 (name_privEnvGetValue, privEnvGetValue);
 (name_privEnvHasBinding, privEnvHasBinding);
 (name_privEnvImplicitThis, privEnvImplicitThis);
 (name_privEnvInitializeImmutableBinding, privEnvInitializeImmutableBinding);
 (name_privEnvModify, privEnvModify);
 (name_privEnvPrepostOp, privEnvPrepostOp);
 (name_privEnvPutValue, privEnvPutValue);
 (name_privEnvSetMutableBinding, privEnvSetMutableBinding);
 (name_privEnvTypeof, privEnvTypeof);
 (name_privEqEq, privEqEq);
 (name_privErrorConstructor, privErrorConstructor);
 (name_privErrorGlobalFuncObj, privErrorGlobalFuncObj);
 (name_privErrorProto, privErrorProto);
 (name_privEvalErrorConstructor, privEvalErrorConstructor);
 (name_privEvalErrorGlobalFuncObj, privEvalErrorGlobalFuncObj);
 (name_privEvalErrorProto, privEvalErrorProto);
 (name_privFunctionConstructor, privFunctionConstructor);
 (name_privFunctionGlobalFuncObj, privFunctionGlobalFuncObj);
 (name_privFunctionProto, privFunctionProto);
 (name_privFunctionProtoCall, privFunctionProtoCall);
 (name_privGeOp, privGeOp);
 (name_privGet, privGet);
 (name_privGet1, privGet1);
 (name_privGetField, privGetField);
 (name_privGetOp, privGetOp);
 (name_privGetOwnProperty, privGetOwnProperty);
 (name_privGetPrim, privGetPrim);
 (name_privGetProperty, privGetProperty);
 (name_privGtOp, privGtOp);
 (name_privHasProperty, privHasProperty);
 (name_privInLeapYear, privInLeapYear);
 (name_privIsCallable, privIsCallable);
 (name_privIsFinite, privIsFinite);
 (name_privIsJSError, privIsJSError);
 (name_privJSError, privJSError);
 (name_privLeOp, privLeOp);
 (name_privLeftShift, privLeftShift);
 (name_privLocalTime, privLocalTime);
 (name_privLtOp, privLtOp);
 (name_privMakeArray, privMakeArray);
 (name_privMakeBind, privMakeBind);
 (name_privMakeBoolean, privMakeBoolean);
 (name_privMakeDate, privMakeDate);
 (name_privMakeDateDayTime, privMakeDateDayTime);
 (name_privMakeDay, privMakeDay);
 (name_privMakeFunctionObject, privMakeFunctionObject);
 (name_privMakeNativeError, privMakeNativeError);
 (name_privMakeNativeErrorProto, privMakeNativeErrorProto);
 (name_privMakeNumber, privMakeNumber);
 (name_privMakeObject, privMakeObject);
 (name_privMakeString, privMakeString);
 (name_privMakeTime, privMakeTime);
 (name_privMath, privMath);
 (name_privMonthFromTime, privMonthFromTime);
 (name_privNativeError, privNativeError);
 (name_privNativeErrorConstructor, privNativeErrorConstructor);
 (name_privNumberCall, privNumberCall);
 (name_privNumberCompareOp, privNumberCompareOp);
 (name_privNumberConstructor, privNumberConstructor);
 (name_privNumberGlobalFuncObj, privNumberGlobalFuncObj);
 (name_privNumberProto, privNumberProto);
 (name_privObjectCall, privObjectCall);
 (name_privObjectConstructor, privObjectConstructor);
 (name_privObjectGlobalFuncObj, privObjectGlobalFuncObj);
 (name_privObjectProto, privObjectProto);
 (name_privObjectTypeCheck, privObjectTypeCheck);
 (name_privPrepostOp, privPrepostOp);
 (name_privPrimAdd, privPrimAdd);
 (name_privPrimComma, privPrimComma);
 (name_privPrimDiv, privPrimDiv);
 (name_privPrimMod, privPrimMod);
 (name_privPrimMult, privPrimMult);
 (name_privPrimMultOp, privPrimMultOp);
 (name_privPrimNew, privPrimNew);
 (name_privPrimSub, privPrimSub);
 (name_privPrimitiveCompareOp, privPrimitiveCompareOp);
 (name_privPropertyAccess, privPropertyAccess);
 (name_privPut, privPut);
 (name_privPut1, privPut1);
 (name_privPutPrim, privPutPrim);
 (name_privRangeError, privRangeError);
 (name_privRangeErrorConstructor, privRangeErrorConstructor);
 (name_privRangeErrorGlobalFuncObj, privRangeErrorGlobalFuncObj);
 (name_privRangeErrorProto, privRangeErrorProto);
 (name_privReferenceError, privReferenceError);
 (name_privReferenceErrorConstructor, privReferenceErrorConstructor);
 (name_privReferenceErrorGlobalFuncObj, privReferenceErrorGlobalFuncObj);
 (name_privReferenceErrorProto, privReferenceErrorProto);
 (name_privRegExpCode, privRegExpCode);
 (name_privRegExpConstructor, privRegExpConstructor);
 (name_privRegExpGlobalFuncObj, privRegExpGlobalFuncObj);
 (name_privRegExpProto, privRegExpProto);
 (name_privRunSelfConstructorCall, privRunSelfConstructorCall);
 (name_privSetField, privSetField);
 (name_privSetOp, privSetOp);
 (name_privSignedRightShift, privSignedRightShift);
 (name_privStringCall, privStringCall);
 (name_privStringConstructor, privStringConstructor);
 (name_privStringGlobalFuncObj, privStringGlobalFuncObj);
 (name_privStringIndices, privStringIndices);
 (name_privStringProto, privStringProto);
 (name_privStxEq, privStxEq);
 (name_privSyntaxError, privSyntaxError);
 (name_privSyntaxErrorConstructor, privSyntaxErrorConstructor);
 (name_privSyntaxErrorGlobalFuncObj, privSyntaxErrorGlobalFuncObj);
 (name_privSyntaxErrorProto, privSyntaxErrorProto);
 (name_privThrowTypeError, privThrowTypeError);
 (name_privThrowTypeErrorFun, privThrowTypeErrorFun);
 (name_privTimeClip, privTimeClip);
 (name_privTimeFromYear, privTimeFromYear);
 (name_privTimeWithinDay, privTimeWithinDay);
 (name_privToBoolean, privToBoolean);
 (name_privToInt32, privToInt32);
 (name_privToInteger, privToInteger);
 (name_privToNumber, privToNumber);
 (name_privToObject, privToObject);
 (name_privToPrimitive, privToPrimitive);
 (name_privToPrimitiveHint, privToPrimitiveHint);
 (name_privToPropertyDescriptor, privToPropertyDescriptor);
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
 (name_privURIErrorProto, privURIErrorProto);
 (name_privUTC, privUTC);
 (name_privUnaryNeg, privUnaryNeg);
 (name_privUnaryNot, privUnaryNot);
 (name_privUnaryPlus, privUnaryPlus);
 (name_privUnboundId, privUnboundId);
 (name_privUnsignedRightShift, privUnsignedRightShift);
 (name_privVoid, privVoid);
 (name_privYearFromTime, privYearFromTime);
 (name_privacos, privacos);
 (name_privacosCall, privacosCall);
 (name_privapply, privapply);
 (name_privapplyCall, privapplyCall);
 (name_privarrayIndexOf, privarrayIndexOf);
 (name_privarrayIndexOfCall, privarrayIndexOfCall);
 (name_privarrayLastIndexOf, privarrayLastIndexOf);
 (name_privarrayLastIndexOfCall, privarrayLastIndexOfCall);
 (name_privarrayTLSCall, privarrayTLSCall);
 (name_privarrayToLocaleString, privarrayToLocaleString);
 (name_privarrayToString, privarrayToString);
 (name_privarrayToStringCall, privarrayToStringCall);
 (name_privasin, privasin);
 (name_privasinCall, privasinCall);
 (name_privassert, privassert);
 (name_privatan, privatan);
 (name_privatan2, privatan2);
 (name_privatan2Call, privatan2Call);
 (name_privatanCall, privatanCall);
 (name_privbind, privbind);
 (name_privbindCall, privbindCall);
 (name_privbooleanToString, privbooleanToString);
 (name_privbooleanToStringCall, privbooleanToStringCall);
 (name_privbooleanValueOf, privbooleanValueOf);
 (name_privcall, privcall);
 (name_privcallCall, privcallCall);
 (name_privcharAt, privcharAt);
 (name_privcharAtCall, privcharAtCall);
 (name_privcharCodeAt, privcharCodeAt);
 (name_privcharCodeAtCall, privcharCodeAtCall);
 (name_privconcat, privconcat);
 (name_privconcatCall, privconcatCall);
 (name_privconfigurableEval, privconfigurableEval);
 (name_privconsole, privconsole);
 (name_privcos, privcos);
 (name_privcosCall, privcosCall);
 (name_privcreate, privcreate);
 (name_privcreateCall, privcreateCall);
 (name_privdateGetTimezoneOffset, privdateGetTimezoneOffset);
 (name_privdateGetTimezoneOffsetCall, privdateGetTimezoneOffsetCall);
 (name_privdateToString, privdateToString);
 (name_privdateToStringCall, privdateToStringCall);
 (name_privdateValueOf, privdateValueOf);
 (name_privdateValueOfCall, privdateValueOfCall);
 (name_privdategetDate, privdategetDate);
 (name_privdategetDateCall, privdategetDateCall);
 (name_privdategetDay, privdategetDay);
 (name_privdategetDayCall, privdategetDayCall);
 (name_privdecodeURI, privdecodeURI);
 (name_privdecodeURICall, privdecodeURICall);
 (name_privdecodeURIComponent, privdecodeURIComponent);
 (name_privdecodeURIComponentCall, privdecodeURIComponentCall);
 (name_privdefine15Property, privdefine15Property);
 (name_privdefineNYIProperty, privdefineNYIProperty);
 (name_privdefineOwnProperty, privdefineOwnProperty);
 (name_privdefineProperties, privdefineProperties);
 (name_privdefinePropertiesCall, privdefinePropertiesCall);
 (name_privdefineProperty, privdefineProperty);
 (name_privdefinePropertyCall, privdefinePropertyCall);
 (name_privencodeURI, privencodeURI);
 (name_privencodeURICall, privencodeURICall);
 (name_privencodeURIComponent, privencodeURIComponent);
 (name_privencodeURIComponentCall, privencodeURIComponentCall);
 (name_privescape, privescape);
 (name_privescapeCall, privescapeCall);
 (name_privets, privets);
 (name_privetsCall, privetsCall);
 (name_priveval, priveval);
 (name_privevalCall, privevalCall);
 (name_privevery, privevery);
 (name_priveveryCall, priveveryCall);
 (name_privexp, privexp);
 (name_privexpCall, privexpCall);
 (name_privfilter, privfilter);
 (name_privfilterCall, privfilterCall);
 (name_privforeach, privforeach);
 (name_privforeachCall, privforeachCall);
 (name_privfreeze, privfreeze);
 (name_privfreezeCall, privfreezeCall);
 (name_privfromCharCode, privfromCharCode);
 (name_privfromccCall, privfromccCall);
 (name_privfunctionToString, privfunctionToString);
 (name_privfunctionToStringCall, privfunctionToStringCall);
 (name_privgetCurrentUTC, privgetCurrentUTC);
 (name_privgetMonth, privgetMonth);
 (name_privgetMonthCall, privgetMonthCall);
 (name_privgetYear, privgetYear);
 (name_privgetYearCall, privgetYearCall);
 (name_privglobal, privglobal);
 (name_privglobalContext, privglobalContext);
 (name_privgopd, privgopd);
 (name_privgopdCall, privgopdCall);
 (name_privgopn, privgopn);
 (name_privgopnCall, privgopnCall);
 (name_privgpo, privgpo);
 (name_privgpoCall, privgpoCall);
 (name_privhasOwnProperty, privhasOwnProperty);
 (name_privhasOwnPropertyCall, privhasOwnPropertyCall);
 (name_privin, privin);
 (name_privinstanceof, privinstanceof);
 (name_privisExtensible, privisExtensible);
 (name_privisExtensibleCall, privisExtensibleCall);
 (name_privisFinite, privisFinite);
 (name_privisFiniteCall, privisFiniteCall);
 (name_privisFrozen, privisFrozen);
 (name_privisFrozenCall, privisFrozenCall);
 (name_privisNaN, privisNaN);
 (name_privisNaNCall, privisNaNCall);
 (name_privisPrototypeOf, privisPrototypeOf);
 (name_privisPrototypeOfCall, privisPrototypeOfCall);
 (name_privisSealed, privisSealed);
 (name_privisSealedCall, privisSealedCall);
 (name_privjoin, privjoin);
 (name_privjoinCall, privjoinCall);
 (name_privkeys, privkeys);
 (name_privkeysCall, privkeysCall);
 (name_privlen, privlen);
 (name_privlocaleCompare, privlocaleCompare);
 (name_privlocaleCompareCall, privlocaleCompareCall);
 (name_privlog, privlog);
 (name_privlogCall, privlogCall);
 (name_privmakeGlobalEnv, privmakeGlobalEnv);
 (name_privmap, privmap);
 (name_privmapCall, privmapCall);
 (name_privmathAbs, privmathAbs);
 (name_privmathAbsCall, privmathAbsCall);
 (name_privmathCeil, privmathCeil);
 (name_privmathCeilCall, privmathCeilCall);
 (name_privmathFloor, privmathFloor);
 (name_privmathFloorCall, privmathFloorCall);
 (name_privmathLog, privmathLog);
 (name_privmathLogCall, privmathLogCall);
 (name_privmathMax, privmathMax);
 (name_privmathMaxCall, privmathMaxCall);
 (name_privmathMin, privmathMin);
 (name_privmathMinCall, privmathMinCall);
 (name_privmathPow, privmathPow);
 (name_privmathPowCall, privmathPowCall);
 (name_privmax, privmax);
 (name_privmin, privmin);
 (name_privminMaxCall, privminMaxCall);
 (name_privmkArgsObj, privmkArgsObj);
 (name_privmsPerDay, privmsPerDay);
 (name_privmsPerHour, privmsPerHour);
 (name_privmsPerMin, privmsPerMin);
 (name_privmsPerSecond, privmsPerSecond);
 (name_privnewDeclEnvRec, privnewDeclEnvRec);
 (name_privnewObjEnvRec, privnewObjEnvRec);
 (name_privnotEqEq, privnotEqEq);
 (name_privnotStxEq, privnotStxEq);
 (name_privnumTLS, privnumTLS);
 (name_privnumTLSCall, privnumTLSCall);
 (name_privnumToStringAbstract, privnumToStringAbstract);
 (name_privnumberPrimval, privnumberPrimval);
 (name_privnumberToString, privnumberToString);
 (name_privnumberToStringCall, privnumberToStringCall);
 (name_privnumberValueOf, privnumberValueOf);
 (name_privobjectToString, privobjectToString);
 (name_privobjectToStringCall, privobjectToStringCall);
 (name_privobjectValueOf, privobjectValueOf);
 (name_privobjectValueOfCall, privobjectValueOfCall);
 (name_privoneArgObj, privoneArgObj);
 (name_privparse, privparse);
 (name_privparseFloat, privparseFloat);
 (name_privparseFloatCall, privparseFloatCall);
 (name_privparseInt, privparseInt);
 (name_privparseIntCall, privparseIntCall);
 (name_privpop, privpop);
 (name_privpopCall, privpopCall);
 (name_privpreventExtensions, privpreventExtensions);
 (name_privpreventExtensionsCall, privpreventExtensionsCall);
 (name_privprimEach, privprimEach);
 (name_privprint, privprint);
 (name_privprintCall, privprintCall);
 (name_privpropEnum, privpropEnum);
 (name_privpropEnumCall, privpropEnumCall);
 (name_privpropertyNames, privpropertyNames);
 (name_privprotoOfField, privprotoOfField);
 (name_privpush, privpush);
 (name_privpushCall, privpushCall);
 (name_privrandom, privrandom);
 (name_privrandomCall, privrandomCall);
 (name_privreduce, privreduce);
 (name_privreduceCall, privreduceCall);
 (name_privreduceRight, privreduceRight);
 (name_privreduceRightCall, privreduceRightCall);
 (name_privreplace, privreplace);
 (name_privreplaceCall, privreplaceCall);
 (name_privresolveThis, privresolveThis);
 (name_privreverse, privreverse);
 (name_privreverseCall, privreverseCall);
 (name_privround, privround);
 (name_privroundCall, privroundCall);
 (name_privrunConstruct, privrunConstruct);
 (name_privseal, privseal);
 (name_privsealCall, privsealCall);
 (name_privset_property, privset_property);
 (name_privshift, privshift);
 (name_privshiftCall, privshiftCall);
 (name_privsin, privsin);
 (name_privsinCall, privsinCall);
 (name_privslice, privslice);
 (name_privsliceCall, privsliceCall);
 (name_privslice_internal, privslice_internal);
 (name_privsome, privsome);
 (name_privsomeCall, privsomeCall);
 (name_privsort, privsort);
 (name_privsortCall, privsortCall);
 (name_privsplice, privsplice);
 (name_privspliceCall, privspliceCall);
 (name_privsplit, privsplit);
 (name_privsplitCall, privsplitCall);
 (name_privsqrt, privsqrt);
 (name_privsqrtCall, privsqrtCall);
 (name_privstringConcat, privstringConcat);
 (name_privstringConcatCall, privstringConcatCall);
 (name_privstringIndexOf, privstringIndexOf);
 (name_privstringIndexOfCall, privstringIndexOfCall);
 (name_privstringLastIndexOf, privstringLastIndexOf);
 (name_privstringLastIndexOfCall, privstringLastIndexOfCall);
 (name_privstringSlice, privstringSlice);
 (name_privstringSliceCall, privstringSliceCall);
 (name_privstringToString, privstringToString);
 (name_privstringToStringCall, privstringToStringCall);
 (name_privstringValueOf, privstringValueOf);
 (name_privsubstring, privsubstring);
 (name_privsubstringCall, privsubstringCall);
 (name_privtan, privtan);
 (name_privtanCall, privtanCall);
 (name_privtest, privtest);
 (name_privtestCall, privtestCall);
 (name_privtoExponential, privtoExponential);
 (name_privtoExponentialCall, privtoExponentialCall);
 (name_privtoFixed, privtoFixed);
 (name_privtoFixedCall, privtoFixedCall);
 (name_privtoLocaleString, privtoLocaleString);
 (name_privtoLocaleStringCall, privtoLocaleStringCall);
 (name_privtoLowerCase, privtoLowerCase);
 (name_privtoLowerCaseCall, privtoLowerCaseCall);
 (name_privtoPrecision, privtoPrecision);
 (name_privtoPrecisionCall, privtoPrecisionCall);
 (name_privtoUpperCase, privtoUpperCase);
 (name_privtoUpperCaseCall, privtoUpperCaseCall);
 (name_privtwoArgObj, privtwoArgObj);
 (name_privunescape, privunescape);
 (name_privunescapeCall, privunescapeCall);
 (name_privunshift, privunshift);
 (name_privunshiftCall, privunshiftCall);
 (name_privvalueOfCall, privvalueOfCall);
 (name_privzeroArgObj, privzeroArgObj);
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
Ltac ctx_compute := cbv beta iota zeta delta -[
privAddAccessorField
privAddDataField
privAppExpr
privAppExprCheck
privAppMethodOp
privArrayCall
privArrayConstructor
privArrayGlobalFuncObj
privArrayIdx
privArrayLengthChange
privArrayProto
privBindConstructor
privBindObjCall
privBitwiseAnd
privBitwiseInfix
privBitwiseNot
privBitwiseOr
privBitwiseXor
privBooleanCall
privBooleanConstructor
privBooleanGlobalFuncObj
privBooleanProto
privCheckObjectCoercible
privCompareOp
privComputeLength
privDateCall
privDateConstructor
privDateFromTime
privDateGlobalFuncObj
privDateProto
privDay
privDayFromYear
privDayWithinYear
privDaysInMonth
privDaysInYear
privDeclEnvAddBinding
privDefaultCall
privDefaultConstruct
privDelete
privDeleteOp
privEnvAppExpr
privEnvAssign
privEnvCreateImmutableBinding
privEnvCreateMutableBinding
privEnvCreateSetMutableBinding
privEnvDefineArg
privEnvDefineArgsObj
privEnvDefineArgsObjOk
privEnvDefineFunc
privEnvDefineVar
privEnvDelete
privEnvGet
privEnvGetBindingValue
privEnvGetId
privEnvGetValue
privEnvHasBinding
privEnvImplicitThis
privEnvInitializeImmutableBinding
privEnvModify
privEnvPrepostOp
privEnvPutValue
privEnvSetMutableBinding
privEnvTypeof
privEqEq
privErrorConstructor
privErrorGlobalFuncObj
privErrorProto
privEvalErrorConstructor
privEvalErrorGlobalFuncObj
privEvalErrorProto
privFunctionConstructor
privFunctionGlobalFuncObj
privFunctionProto
privFunctionProtoCall
privGeOp
privGet
privGet1
privGetField
privGetOp
privGetOwnProperty
privGetPrim
privGetProperty
privGtOp
privHasProperty
privInLeapYear
privIsCallable
privIsFinite
privIsJSError
privJSError
privLeOp
privLeftShift
privLocalTime
privLtOp
privMakeArray
privMakeBind
privMakeBoolean
privMakeDate
privMakeDateDayTime
privMakeDay
privMakeFunctionObject
privMakeNativeError
privMakeNativeErrorProto
privMakeNumber
privMakeObject
privMakeString
privMakeTime
privMath
privMonthFromTime
privNativeError
privNativeErrorConstructor
privNumberCall
privNumberCompareOp
privNumberConstructor
privNumberGlobalFuncObj
privNumberProto
privObjectCall
privObjectConstructor
privObjectGlobalFuncObj
privObjectProto
privObjectTypeCheck
privPrepostOp
privPrimAdd
privPrimComma
privPrimDiv
privPrimMod
privPrimMult
privPrimMultOp
privPrimNew
privPrimSub
privPrimitiveCompareOp
privPropertyAccess
privPut
privPut1
privPutPrim
privRangeError
privRangeErrorConstructor
privRangeErrorGlobalFuncObj
privRangeErrorProto
privReferenceError
privReferenceErrorConstructor
privReferenceErrorGlobalFuncObj
privReferenceErrorProto
privRegExpCode
privRegExpConstructor
privRegExpGlobalFuncObj
privRegExpProto
privRunSelfConstructorCall
privSetField
privSetOp
privSignedRightShift
privStringCall
privStringConstructor
privStringGlobalFuncObj
privStringIndices
privStringProto
privStxEq
privSyntaxError
privSyntaxErrorConstructor
privSyntaxErrorGlobalFuncObj
privSyntaxErrorProto
privThrowTypeError
privThrowTypeErrorFun
privTimeClip
privTimeFromYear
privTimeWithinDay
privToBoolean
privToInt32
privToInteger
privToNumber
privToObject
privToPrimitive
privToPrimitiveHint
privToPropertyDescriptor
privToString
privToUint
privToUint16
privToUint32
privTypeError
privTypeErrorConstructor
privTypeErrorGlobalFuncObj
privTypeErrorProto
privTypeof
privURIErrorConstructor
privURIErrorGlobalFuncObj
privURIErrorProto
privUTC
privUnaryNeg
privUnaryNot
privUnaryPlus
privUnboundId
privUnsignedRightShift
privVoid
privYearFromTime
privacos
privacosCall
privapply
privapplyCall
privarrayIndexOf
privarrayIndexOfCall
privarrayLastIndexOf
privarrayLastIndexOfCall
privarrayTLSCall
privarrayToLocaleString
privarrayToString
privarrayToStringCall
privasin
privasinCall
privassert
privatan
privatan2
privatan2Call
privatanCall
privbind
privbindCall
privbooleanToString
privbooleanToStringCall
privbooleanValueOf
privcall
privcallCall
privcharAt
privcharAtCall
privcharCodeAt
privcharCodeAtCall
privconcat
privconcatCall
privconfigurableEval
privconsole
privcos
privcosCall
privcreate
privcreateCall
privdateGetTimezoneOffset
privdateGetTimezoneOffsetCall
privdateToString
privdateToStringCall
privdateValueOf
privdateValueOfCall
privdategetDate
privdategetDateCall
privdategetDay
privdategetDayCall
privdecodeURI
privdecodeURICall
privdecodeURIComponent
privdecodeURIComponentCall
privdefine15Property
privdefineNYIProperty
privdefineOwnProperty
privdefineProperties
privdefinePropertiesCall
privdefineProperty
privdefinePropertyCall
privencodeURI
privencodeURICall
privencodeURIComponent
privencodeURIComponentCall
privescape
privescapeCall
privets
privetsCall
priveval
privevalCall
privevery
priveveryCall
privexp
privexpCall
privfilter
privfilterCall
privforeach
privforeachCall
privfreeze
privfreezeCall
privfromCharCode
privfromccCall
privfunctionToString
privfunctionToStringCall
privgetCurrentUTC
privgetMonth
privgetMonthCall
privgetYear
privgetYearCall
privglobal
privglobalContext
privgopd
privgopdCall
privgopn
privgopnCall
privgpo
privgpoCall
privhasOwnProperty
privhasOwnPropertyCall
privin
privinstanceof
privisExtensible
privisExtensibleCall
privisFinite
privisFiniteCall
privisFrozen
privisFrozenCall
privisNaN
privisNaNCall
privisPrototypeOf
privisPrototypeOfCall
privisSealed
privisSealedCall
privjoin
privjoinCall
privkeys
privkeysCall
privlen
privlocaleCompare
privlocaleCompareCall
privlog
privlogCall
privmakeGlobalEnv
privmap
privmapCall
privmathAbs
privmathAbsCall
privmathCeil
privmathCeilCall
privmathFloor
privmathFloorCall
privmathLog
privmathLogCall
privmathMax
privmathMaxCall
privmathMin
privmathMinCall
privmathPow
privmathPowCall
privmax
privmin
privminMaxCall
privmkArgsObj
privmsPerDay
privmsPerHour
privmsPerMin
privmsPerSecond
privnewDeclEnvRec
privnewObjEnvRec
privnotEqEq
privnotStxEq
privnumTLS
privnumTLSCall
privnumToStringAbstract
privnumberPrimval
privnumberToString
privnumberToStringCall
privnumberValueOf
privobjectToString
privobjectToStringCall
privobjectValueOf
privobjectValueOfCall
privoneArgObj
privparse
privparseFloat
privparseFloatCall
privparseInt
privparseIntCall
privpop
privpopCall
privpreventExtensions
privpreventExtensionsCall
privprimEach
privprint
privprintCall
privpropEnum
privpropEnumCall
privpropertyNames
privprotoOfField
privpush
privpushCall
privrandom
privrandomCall
privreduce
privreduceCall
privreduceRight
privreduceRightCall
privreplace
privreplaceCall
privresolveThis
privreverse
privreverseCall
privround
privroundCall
privrunConstruct
privseal
privsealCall
privset_property
privshift
privshiftCall
privsin
privsinCall
privslice
privsliceCall
privslice_internal
privsome
privsomeCall
privsort
privsortCall
privsplice
privspliceCall
privsplit
privsplitCall
privsqrt
privsqrtCall
privstringConcat
privstringConcatCall
privstringIndexOf
privstringIndexOfCall
privstringLastIndexOf
privstringLastIndexOfCall
privstringSlice
privstringSliceCall
privstringToString
privstringToStringCall
privstringValueOf
privsubstring
privsubstringCall
privtan
privtanCall
privtest
privtestCall
privtoExponential
privtoExponentialCall
privtoFixed
privtoFixedCall
privtoLocaleString
privtoLocaleStringCall
privtoLowerCase
privtoLowerCaseCall
privtoPrecision
privtoPrecisionCall
privtoUpperCase
privtoUpperCaseCall
privtwoArgObj
privunescape
privunescapeCall
privunshift
privunshiftCall
privvalueOfCall
privzeroArgObj
copy_access_desc
copy_data_desc
copy_when_defined
isAccessorDescriptor
isAccessorField
isDataDescriptor
isDataField
isGenericDescriptor
isGenericField
].
Definition store_items := [
(0, {|object_attrs :=
      {|oattrs_proto := proto;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("make", 
                  attributes_data_of {|attributes_data_value :=
                                       value_closure
                                       (closure_intro
                                        [("%AddAccessorField", privAddAccessorField);
                                         ("%AddDataField", privAddDataField);
                                         ("%AppExpr", privAppExpr);
                                         ("%AppExprCheck", privAppExprCheck);
                                         ("%AppMethodOp", privAppMethodOp);
                                         ("%ArrayCall", privArrayCall);
                                         ("%ArrayConstructor", privArrayConstructor);
                                         ("%ArrayGlobalFuncObj", privArrayGlobalFuncObj);
                                         ("%ArrayIdx", privArrayIdx);
                                         ("%ArrayLengthChange", privArrayLengthChange);
                                         ("%ArrayProto", privArrayProto);
                                         ("%BindConstructor", privBindConstructor);
                                         ("%BindObjCall", privBindObjCall);
                                         ("%BitwiseAnd", privBitwiseAnd);
                                         ("%BitwiseInfix", privBitwiseInfix);
                                         ("%BitwiseNot", privBitwiseNot);
                                         ("%BitwiseOr", privBitwiseOr);
                                         ("%BitwiseXor", privBitwiseXor);
                                         ("%BooleanCall", privBooleanCall);
                                         ("%BooleanConstructor", privBooleanConstructor);
                                         ("%BooleanGlobalFuncObj", privBooleanGlobalFuncObj);
                                         ("%BooleanProto", privBooleanProto);
                                         ("%CheckObjectCoercible", privCheckObjectCoercible);
                                         ("%CompareOp", privCompareOp);
                                         ("%ComputeLength", privComputeLength);
                                         ("%DateCall", privDateCall);
                                         ("%DateConstructor", privDateConstructor);
                                         ("%DateFromTime", privDateFromTime);
                                         ("%DateGlobalFuncObj", privDateGlobalFuncObj);
                                         ("%DateProto", privDateProto);
                                         ("%Day", privDay);
                                         ("%DayFromYear", privDayFromYear);
                                         ("%DayWithinYear", privDayWithinYear);
                                         ("%DaysInMonth", privDaysInMonth);
                                         ("%DaysInYear", privDaysInYear);
                                         ("%DeclEnvAddBinding", privDeclEnvAddBinding);
                                         ("%DefaultCall", privDefaultCall);
                                         ("%DefaultConstruct", privDefaultConstruct);
                                         ("%Delete", privDelete);
                                         ("%DeleteOp", privDeleteOp);
                                         ("%EnvAppExpr", privEnvAppExpr);
                                         ("%EnvAssign", privEnvAssign);
                                         ("%EnvCreateImmutableBinding", privEnvCreateImmutableBinding);
                                         ("%EnvCreateMutableBinding", privEnvCreateMutableBinding);
                                         ("%EnvCreateSetMutableBinding", privEnvCreateSetMutableBinding);
                                         ("%EnvDefineArg", privEnvDefineArg);
                                         ("%EnvDefineArgsObj", privEnvDefineArgsObj);
                                         ("%EnvDefineArgsObjOk", privEnvDefineArgsObjOk);
                                         ("%EnvDefineFunc", privEnvDefineFunc);
                                         ("%EnvDefineVar", privEnvDefineVar);
                                         ("%EnvDelete", privEnvDelete);
                                         ("%EnvGet", privEnvGet);
                                         ("%EnvGetBindingValue", privEnvGetBindingValue);
                                         ("%EnvGetId", privEnvGetId);
                                         ("%EnvGetValue", privEnvGetValue);
                                         ("%EnvHasBinding", privEnvHasBinding);
                                         ("%EnvImplicitThis", privEnvImplicitThis);
                                         ("%EnvInitializeImmutableBinding", privEnvInitializeImmutableBinding);
                                         ("%EnvModify", privEnvModify);
                                         ("%EnvPrepostOp", privEnvPrepostOp);
                                         ("%EnvPutValue", privEnvPutValue);
                                         ("%EnvSetMutableBinding", privEnvSetMutableBinding);
                                         ("%EnvTypeof", privEnvTypeof);
                                         ("%EqEq", privEqEq);
                                         ("%ErrorConstructor", privErrorConstructor);
                                         ("%ErrorGlobalFuncObj", privErrorGlobalFuncObj);
                                         ("%ErrorProto", privErrorProto);
                                         ("%EvalErrorConstructor", privEvalErrorConstructor);
                                         ("%EvalErrorGlobalFuncObj", privEvalErrorGlobalFuncObj);
                                         ("%EvalErrorProto", privEvalErrorProto);
                                         ("%FunctionConstructor", privFunctionConstructor);
                                         ("%FunctionGlobalFuncObj", privFunctionGlobalFuncObj);
                                         ("%FunctionProto", privFunctionProto);
                                         ("%FunctionProtoCall", privFunctionProtoCall);
                                         ("%GeOp", privGeOp);
                                         ("%Get", privGet);
                                         ("%Get1", privGet1);
                                         ("%GetField", privGetField);
                                         ("%GetOp", privGetOp);
                                         ("%GetOwnProperty", privGetOwnProperty);
                                         ("%GetPrim", privGetPrim);
                                         ("%GetProperty", privGetProperty);
                                         ("%GtOp", privGtOp);
                                         ("%HasProperty", privHasProperty);
                                         ("%InLeapYear", privInLeapYear);
                                         ("%IsCallable", privIsCallable);
                                         ("%IsFinite", privIsFinite);
                                         ("%IsJSError", privIsJSError);
                                         ("%JSError", privJSError);
                                         ("%LeOp", privLeOp);
                                         ("%LeftShift", privLeftShift);
                                         ("%LocalTime", privLocalTime);
                                         ("%LtOp", privLtOp);
                                         ("%MakeArray", privMakeArray);
                                         ("%MakeBind", privMakeBind);
                                         ("%MakeBoolean", privMakeBoolean);
                                         ("%MakeDate", privMakeDate);
                                         ("%MakeDateDayTime", privMakeDateDayTime);
                                         ("%MakeDay", privMakeDay);
                                         ("%MakeFunctionObject", privMakeFunctionObject);
                                         ("%MakeNativeError", privMakeNativeError);
                                         ("%MakeNativeErrorProto", privMakeNativeErrorProto);
                                         ("%MakeNumber", privMakeNumber);
                                         ("%MakeObject", privMakeObject);
                                         ("%MakeString", privMakeString);
                                         ("%MakeTime", privMakeTime);
                                         ("%Math", privMath);
                                         ("%MonthFromTime", privMonthFromTime);
                                         ("%NativeError", privNativeError);
                                         ("%NativeErrorConstructor", privNativeErrorConstructor);
                                         ("%NumberCall", privNumberCall);
                                         ("%NumberCompareOp", privNumberCompareOp);
                                         ("%NumberConstructor", privNumberConstructor);
                                         ("%NumberGlobalFuncObj", privNumberGlobalFuncObj);
                                         ("%NumberProto", privNumberProto);
                                         ("%ObjectCall", privObjectCall);
                                         ("%ObjectConstructor", privObjectConstructor);
                                         ("%ObjectGlobalFuncObj", privObjectGlobalFuncObj);
                                         ("%ObjectProto", privObjectProto);
                                         ("%ObjectTypeCheck", privObjectTypeCheck);
                                         ("%PrepostOp", privPrepostOp);
                                         ("%PrimAdd", privPrimAdd);
                                         ("%PrimComma", privPrimComma);
                                         ("%PrimDiv", privPrimDiv);
                                         ("%PrimMod", privPrimMod);
                                         ("%PrimMult", privPrimMult);
                                         ("%PrimMultOp", privPrimMultOp);
                                         ("%PrimNew", privPrimNew);
                                         ("%PrimSub", privPrimSub);
                                         ("%PrimitiveCompareOp", privPrimitiveCompareOp);
                                         ("%PropertyAccess", privPropertyAccess);
                                         ("%Put", privPut);
                                         ("%Put1", privPut1);
                                         ("%PutPrim", privPutPrim);
                                         ("%RangeError", privRangeError);
                                         ("%RangeErrorConstructor", privRangeErrorConstructor);
                                         ("%RangeErrorGlobalFuncObj", privRangeErrorGlobalFuncObj);
                                         ("%RangeErrorProto", privRangeErrorProto);
                                         ("%ReferenceError", privReferenceError);
                                         ("%ReferenceErrorConstructor", privReferenceErrorConstructor);
                                         ("%ReferenceErrorGlobalFuncObj", privReferenceErrorGlobalFuncObj);
                                         ("%ReferenceErrorProto", privReferenceErrorProto);
                                         ("%RegExpCode", privRegExpCode);
                                         ("%RegExpConstructor", privRegExpConstructor);
                                         ("%RegExpGlobalFuncObj", privRegExpGlobalFuncObj);
                                         ("%RegExpProto", privRegExpProto);
                                         ("%RunSelfConstructorCall", privRunSelfConstructorCall);
                                         ("%SetField", privSetField);
                                         ("%SetOp", privSetOp);
                                         ("%SignedRightShift", privSignedRightShift);
                                         ("%StringCall", privStringCall);
                                         ("%StringConstructor", privStringConstructor);
                                         ("%StringGlobalFuncObj", privStringGlobalFuncObj);
                                         ("%StringIndices", privStringIndices);
                                         ("%StringProto", privStringProto);
                                         ("%StxEq", privStxEq);
                                         ("%SyntaxError", privSyntaxError);
                                         ("%SyntaxErrorConstructor", privSyntaxErrorConstructor);
                                         ("%SyntaxErrorGlobalFuncObj", privSyntaxErrorGlobalFuncObj);
                                         ("%SyntaxErrorProto", privSyntaxErrorProto);
                                         ("%ThrowTypeError", privThrowTypeError);
                                         ("%ThrowTypeErrorFun", privThrowTypeErrorFun);
                                         ("%TimeClip", privTimeClip);
                                         ("%TimeFromYear", privTimeFromYear);
                                         ("%TimeWithinDay", privTimeWithinDay);
                                         ("%ToBoolean", privToBoolean);
                                         ("%ToInt32", privToInt32);
                                         ("%ToInteger", privToInteger);
                                         ("%ToNumber", privToNumber);
                                         ("%ToObject", privToObject);
                                         ("%ToPrimitive", privToPrimitive);
                                         ("%ToPrimitiveHint", privToPrimitiveHint);
                                         ("%ToPropertyDescriptor", privToPropertyDescriptor);
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
                                         ("%URIErrorProto", privURIErrorProto);
                                         ("%UTC", privUTC);
                                         ("%UnaryNeg", privUnaryNeg);
                                         ("%UnaryNot", privUnaryNot);
                                         ("%UnaryPlus", privUnaryPlus);
                                         ("%UnboundId", privUnboundId);
                                         ("%UnsignedRightShift", privUnsignedRightShift);
                                         ("%Void", privVoid);
                                         ("%YearFromTime", privYearFromTime);
                                         ("%acos", privacos);
                                         ("%acosCall", privacosCall);
                                         ("%apply", privapply);
                                         ("%applyCall", privapplyCall);
                                         ("%arrayIndexOf", privarrayIndexOf);
                                         ("%arrayIndexOfCall", privarrayIndexOfCall);
                                         ("%arrayLastIndexOf", privarrayLastIndexOf);
                                         ("%arrayLastIndexOfCall", privarrayLastIndexOfCall);
                                         ("%arrayTLSCall", privarrayTLSCall);
                                         ("%arrayToLocaleString", privarrayToLocaleString);
                                         ("%arrayToString", privarrayToString);
                                         ("%arrayToStringCall", privarrayToStringCall);
                                         ("%asin", privasin);
                                         ("%asinCall", privasinCall);
                                         ("%assert", privassert);
                                         ("%atan", privatan);
                                         ("%atan2", privatan2);
                                         ("%atan2Call", privatan2Call);
                                         ("%atanCall", privatanCall);
                                         ("%bind", privbind);
                                         ("%bindCall", privbindCall);
                                         ("%booleanToString", privbooleanToString);
                                         ("%booleanToStringCall", privbooleanToStringCall);
                                         ("%booleanValueOf", privbooleanValueOf);
                                         ("%call", privcall);
                                         ("%callCall", privcallCall);
                                         ("%charAt", privcharAt);
                                         ("%charAtCall", privcharAtCall);
                                         ("%charCodeAt", privcharCodeAt);
                                         ("%charCodeAtCall", privcharCodeAtCall);
                                         ("%concat", privconcat);
                                         ("%concatCall", privconcatCall);
                                         ("%configurableEval", privconfigurableEval);
                                         ("%console", privconsole);
                                         ("%cos", privcos);
                                         ("%cosCall", privcosCall);
                                         ("%create", privcreate);
                                         ("%createCall", privcreateCall);
                                         ("%dateGetTimezoneOffset", privdateGetTimezoneOffset);
                                         ("%dateGetTimezoneOffsetCall", privdateGetTimezoneOffsetCall);
                                         ("%dateToString", privdateToString);
                                         ("%dateToStringCall", privdateToStringCall);
                                         ("%dateValueOf", privdateValueOf);
                                         ("%dateValueOfCall", privdateValueOfCall);
                                         ("%dategetDate", privdategetDate);
                                         ("%dategetDateCall", privdategetDateCall);
                                         ("%dategetDay", privdategetDay);
                                         ("%dategetDayCall", privdategetDayCall);
                                         ("%decodeURI", privdecodeURI);
                                         ("%decodeURICall", privdecodeURICall);
                                         ("%decodeURIComponent", privdecodeURIComponent);
                                         ("%decodeURIComponentCall", privdecodeURIComponentCall);
                                         ("%define15Property", privdefine15Property);
                                         ("%defineNYIProperty", privdefineNYIProperty);
                                         ("%defineOwnProperty", privdefineOwnProperty);
                                         ("%defineProperties", privdefineProperties);
                                         ("%definePropertiesCall", privdefinePropertiesCall);
                                         ("%defineProperty", privdefineProperty);
                                         ("%definePropertyCall", privdefinePropertyCall);
                                         ("%encodeURI", privencodeURI);
                                         ("%encodeURICall", privencodeURICall);
                                         ("%encodeURIComponent", privencodeURIComponent);
                                         ("%encodeURIComponentCall", privencodeURIComponentCall);
                                         ("%escape", privescape);
                                         ("%escapeCall", privescapeCall);
                                         ("%ets", privets);
                                         ("%etsCall", privetsCall);
                                         ("%eval", priveval);
                                         ("%evalCall", privevalCall);
                                         ("%every", privevery);
                                         ("%everyCall", priveveryCall);
                                         ("%exp", privexp);
                                         ("%expCall", privexpCall);
                                         ("%filter", privfilter);
                                         ("%filterCall", privfilterCall);
                                         ("%foreach", privforeach);
                                         ("%foreachCall", privforeachCall);
                                         ("%freeze", privfreeze);
                                         ("%freezeCall", privfreezeCall);
                                         ("%fromCharCode", privfromCharCode);
                                         ("%fromccCall", privfromccCall);
                                         ("%functionToString", privfunctionToString);
                                         ("%functionToStringCall", privfunctionToStringCall);
                                         ("%getCurrentUTC", privgetCurrentUTC);
                                         ("%getMonth", privgetMonth);
                                         ("%getMonthCall", privgetMonthCall);
                                         ("%getYear", privgetYear);
                                         ("%getYearCall", privgetYearCall);
                                         ("%global", privglobal);
                                         ("%globalContext", privglobalContext);
                                         ("%gopd", privgopd);
                                         ("%gopdCall", privgopdCall);
                                         ("%gopn", privgopn);
                                         ("%gopnCall", privgopnCall);
                                         ("%gpo", privgpo);
                                         ("%gpoCall", privgpoCall);
                                         ("%hasOwnProperty", privhasOwnProperty);
                                         ("%hasOwnPropertyCall", privhasOwnPropertyCall);
                                         ("%in", privin);
                                         ("%instanceof", privinstanceof);
                                         ("%isExtensible", privisExtensible);
                                         ("%isExtensibleCall", privisExtensibleCall);
                                         ("%isFinite", privisFinite);
                                         ("%isFiniteCall", privisFiniteCall);
                                         ("%isFrozen", privisFrozen);
                                         ("%isFrozenCall", privisFrozenCall);
                                         ("%isNaN", privisNaN);
                                         ("%isNaNCall", privisNaNCall);
                                         ("%isPrototypeOf", privisPrototypeOf);
                                         ("%isPrototypeOfCall", privisPrototypeOfCall);
                                         ("%isSealed", privisSealed);
                                         ("%isSealedCall", privisSealedCall);
                                         ("%join", privjoin);
                                         ("%joinCall", privjoinCall);
                                         ("%keys", privkeys);
                                         ("%keysCall", privkeysCall);
                                         ("%len", privlen);
                                         ("%localeCompare", privlocaleCompare);
                                         ("%localeCompareCall", privlocaleCompareCall);
                                         ("%log", privlog);
                                         ("%logCall", privlogCall);
                                         ("%makeGlobalEnv", privmakeGlobalEnv);
                                         ("%map", privmap);
                                         ("%mapCall", privmapCall);
                                         ("%mathAbs", privmathAbs);
                                         ("%mathAbsCall", privmathAbsCall);
                                         ("%mathCeil", privmathCeil);
                                         ("%mathCeilCall", privmathCeilCall);
                                         ("%mathFloor", privmathFloor);
                                         ("%mathFloorCall", privmathFloorCall);
                                         ("%mathLog", privmathLog);
                                         ("%mathLogCall", privmathLogCall);
                                         ("%mathMax", privmathMax);
                                         ("%mathMaxCall", privmathMaxCall);
                                         ("%mathMin", privmathMin);
                                         ("%mathMinCall", privmathMinCall);
                                         ("%mathPow", privmathPow);
                                         ("%mathPowCall", privmathPowCall);
                                         ("%max", privmax);
                                         ("%min", privmin);
                                         ("%minMaxCall", privminMaxCall);
                                         ("%mkArgsObj", privmkArgsObj);
                                         ("%msPerDay", privmsPerDay);
                                         ("%msPerHour", privmsPerHour);
                                         ("%msPerMin", privmsPerMin);
                                         ("%msPerSecond", privmsPerSecond);
                                         ("%newDeclEnvRec", privnewDeclEnvRec);
                                         ("%newObjEnvRec", privnewObjEnvRec);
                                         ("%notEqEq", privnotEqEq);
                                         ("%notStxEq", privnotStxEq);
                                         ("%numTLS", privnumTLS);
                                         ("%numTLSCall", privnumTLSCall);
                                         ("%numToStringAbstract", privnumToStringAbstract);
                                         ("%numberPrimval", privnumberPrimval);
                                         ("%numberToString", privnumberToString);
                                         ("%numberToStringCall", privnumberToStringCall);
                                         ("%numberValueOf", privnumberValueOf);
                                         ("%objectToString", privobjectToString);
                                         ("%objectToStringCall", privobjectToStringCall);
                                         ("%objectValueOf", privobjectValueOf);
                                         ("%objectValueOfCall", privobjectValueOfCall);
                                         ("%oneArgObj", privoneArgObj);
                                         ("%parse", privparse);
                                         ("%parseFloat", privparseFloat);
                                         ("%parseFloatCall", privparseFloatCall);
                                         ("%parseInt", privparseInt);
                                         ("%parseIntCall", privparseIntCall);
                                         ("%pop", privpop);
                                         ("%popCall", privpopCall);
                                         ("%preventExtensions", privpreventExtensions);
                                         ("%preventExtensionsCall", privpreventExtensionsCall);
                                         ("%primEach", privprimEach);
                                         ("%print", privprint);
                                         ("%printCall", privprintCall);
                                         ("%propEnum", privpropEnum);
                                         ("%propEnumCall", privpropEnumCall);
                                         ("%propertyNames", privpropertyNames);
                                         ("%protoOfField", privprotoOfField);
                                         ("%push", privpush);
                                         ("%pushCall", privpushCall);
                                         ("%random", privrandom);
                                         ("%randomCall", privrandomCall);
                                         ("%reduce", privreduce);
                                         ("%reduceCall", privreduceCall);
                                         ("%reduceRight", privreduceRight);
                                         ("%reduceRightCall", privreduceRightCall);
                                         ("%replace", privreplace);
                                         ("%replaceCall", privreplaceCall);
                                         ("%resolveThis", privresolveThis);
                                         ("%reverse", privreverse);
                                         ("%reverseCall", privreverseCall);
                                         ("%round", privround);
                                         ("%roundCall", privroundCall);
                                         ("%runConstruct", privrunConstruct);
                                         ("%seal", privseal);
                                         ("%sealCall", privsealCall);
                                         ("%set-property", privset_property);
                                         ("%shift", privshift);
                                         ("%shiftCall", privshiftCall);
                                         ("%sin", privsin);
                                         ("%sinCall", privsinCall);
                                         ("%slice", privslice);
                                         ("%sliceCall", privsliceCall);
                                         ("%slice_internal", privslice_internal);
                                         ("%some", privsome);
                                         ("%someCall", privsomeCall);
                                         ("%sort", privsort);
                                         ("%sortCall", privsortCall);
                                         ("%splice", privsplice);
                                         ("%spliceCall", privspliceCall);
                                         ("%split", privsplit);
                                         ("%splitCall", privsplitCall);
                                         ("%sqrt", privsqrt);
                                         ("%sqrtCall", privsqrtCall);
                                         ("%stringConcat", privstringConcat);
                                         ("%stringConcatCall", privstringConcatCall);
                                         ("%stringIndexOf", privstringIndexOf);
                                         ("%stringIndexOfCall", privstringIndexOfCall);
                                         ("%stringLastIndexOf", privstringLastIndexOf);
                                         ("%stringLastIndexOfCall", privstringLastIndexOfCall);
                                         ("%stringSlice", privstringSlice);
                                         ("%stringSliceCall", privstringSliceCall);
                                         ("%stringToString", privstringToString);
                                         ("%stringToStringCall", privstringToStringCall);
                                         ("%stringValueOf", privstringValueOf);
                                         ("%substring", privsubstring);
                                         ("%substringCall", privsubstringCall);
                                         ("%tan", privtan);
                                         ("%tanCall", privtanCall);
                                         ("%test", privtest);
                                         ("%testCall", privtestCall);
                                         ("%toExponential", privtoExponential);
                                         ("%toExponentialCall", privtoExponentialCall);
                                         ("%toFixed", privtoFixed);
                                         ("%toFixedCall", privtoFixedCall);
                                         ("%toLocaleString", privtoLocaleString);
                                         ("%toLocaleStringCall", privtoLocaleStringCall);
                                         ("%toLowerCase", privtoLowerCase);
                                         ("%toLowerCaseCall", privtoLowerCaseCall);
                                         ("%toPrecision", privtoPrecision);
                                         ("%toPrecisionCall", privtoPrecisionCall);
                                         ("%toUpperCase", privtoUpperCase);
                                         ("%toUpperCaseCall", privtoUpperCaseCall);
                                         ("%twoArgObj", privtwoArgObj);
                                         ("%unescape", privunescape);
                                         ("%unescapeCall", privunescapeCall);
                                         ("%unshift", privunshift);
                                         ("%unshiftCall", privunshiftCall);
                                         ("%valueOfCall", privvalueOfCall);
                                         ("%zeroArgObj", privzeroArgObj);
                                         ("copy-access-desc", copy_access_desc);
                                         ("copy-data-desc", copy_data_desc);
                                         ("copy-when-defined", copy_when_defined);
                                         ("isAccessorDescriptor", isAccessorDescriptor);
                                         ("isAccessorField", isAccessorField);
                                         ("isDataDescriptor", isDataDescriptor);
                                         ("isDataField", isDataField);
                                         ("isGenericDescriptor", isGenericDescriptor);
                                         ("isGenericField", isGenericField)]
                                        None [] ex_dataval);
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(1, {|object_attrs :=
      {|oattrs_proto := proto;
        oattrs_class := "Object";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 33;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("hasOwnProperty", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 42;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isPrototypeOf", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 43;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("propertyIsEnumerable", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 39;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("toLocaleString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 40;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 38;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("valueOf", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 41;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(2, {|object_attrs :=
      {|oattrs_proto := privObjectProto;
        oattrs_class := "GlobalObject";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("Array", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 101;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Boolean", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 31;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Date", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 171;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Error", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 44;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("EvalError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 46;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Function", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 311;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Infinity", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number JsNumber.infinity;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("Math", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 255;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("NaN", 
                  attributes_data_of {|attributes_data_value :=
                                       value_number JsNumber.nan;
                                       attributes_data_writable := false;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := false|});
                 ("Number", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 24;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("Object", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 33;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("RangeError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 47;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("ReferenceError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 48;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("RegExp", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 248;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("String", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 27;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("SyntaxError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 45;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("TypeError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 49;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("URIError", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 51;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("console", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 309;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("decodeURI", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 250;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("decodeURIComponent", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 251;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("encodeURI", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 252;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("encodeURIComponent", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 253;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("escape", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 314;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("eval", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 310;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isFinite", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 312;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("isNaN", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 21;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("parseFloat", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 313;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("parseInt", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 249;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("print", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 15;
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
                                       value_object 316;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("window", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 2;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(3, {|object_attrs :=
      {|oattrs_proto := privObjectProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 44;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "Error";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 22;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(4, {|object_attrs :=
      {|oattrs_proto := privErrorProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 49;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "TypeError";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(5, {|object_attrs :=
      {|oattrs_proto := privErrorProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 48;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "ReferenceError";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(6, {|object_attrs :=
      {|oattrs_proto := privErrorProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 45;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "SyntaxError";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(7, {|object_attrs :=
      {|oattrs_proto := privErrorProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 46;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "EvalError";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(8, {|object_attrs :=
      {|oattrs_proto := privErrorProto;
        oattrs_class := "Error";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 47;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("message", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("name", 
                  attributes_data_of {|attributes_data_value :=
                                       value_string "RangeError";
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|})];
      object_internal := from_list []|});
(9, {|object_attrs :=
      {|oattrs_proto := privObjectProto;
        oattrs_class := "Boolean";
        oattrs_extensible := true;
        oattrs_code := objCode|};
      object_properties :=
      from_list [("constructor", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 31;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|});
                 ("toString", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 28;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := false;
                                       attributes_data_configurable := true|});
                 ("valueOf", 
                  attributes_data_of {|attributes_data_value :=
                                       value_object 296;
                                       attributes_data_writable := true;
                                       attributes_data_enumerable := true;
                                       attributes_data_configurable := true|})];
      object_internal := from_list [("primval",  value_false)]|});
(10, {|object_attrs :=
       {|oattrs_proto := privObjectProto;
         oattrs_class := "Number";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 24;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toExponential", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 303;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toFixed", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 298;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLocaleString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 301;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toPrecision", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 305;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 153;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("valueOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 294;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|})];
       object_internal :=
       from_list [("primval",  value_number (JsNumber.of_int (0)))]|});
(11, {|object_attrs :=
       {|oattrs_proto := privObjectProto;
         oattrs_class := "String";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("charAt", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 103;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("charCodeAt", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 106;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("concat", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 109;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 27;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("indexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 156;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("lastIndexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 158;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("localeCompare", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 159;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("replace", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 157;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("slice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 160;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("split", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 163;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("substring", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 112;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLocaleLowerCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 161;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLocaleUpperCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 162;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLowerCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 161;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 25;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toUpperCase", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 162;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("valueOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 292;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|})];
       object_internal := from_list [("primval",  value_string "")]|});
(12, {|object_attrs :=
       {|oattrs_proto := privObjectProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privFunctionProtoCall|};
       object_properties :=
       from_list [("apply", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 18;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("bind", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 150;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("call", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 17;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 311;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 13;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%AppExpr", privAppExpr);
                     ("%Get1", privGet1);
                     ("%ObjectProto", privObjectProto)] None
                    ["constr"; "args"] ex_internal))]|});
(13, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privfunctionToStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(14, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := false;
         oattrs_code := privThrowTypeErrorFun|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(15, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privprintCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(16, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privdefinePropertyCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(17, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privcallCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(18, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privapplyCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(19, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(20, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(21, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privisNaNCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(22, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privetsCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(23, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 22;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(24, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privNumberCall|};
       object_properties :=
       from_list [("MAX_VALUE", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("MIN_VALUE", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("NEGATIVE_INFINITY", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number JsNumber.neg_infinity;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("NaN", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number JsNumber.nan;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("POSITIVE_INFINITY", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number JsNumber.infinity;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 10;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%ComputeLength", privComputeLength);
                     ("%MakeNumber", privMakeNumber);
                     ("%ToNumber", privToNumber)] None ["constr"; "args"]
                    ex_internal1))]|});
(25, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privstringToStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(26, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 25;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(27, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privStringCall|};
       object_properties :=
       from_list [("fromCharCode", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 74;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 11;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeString", privMakeString);
                     ("%StringCall", privStringCall)] None ["constr"; "args"]
                    ex_internal2))]|});
(28, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privbooleanToStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(29, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(30, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 28;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(31, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privBooleanCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 9;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeBoolean", privMakeBoolean);
                     ("%ToBoolean", privToBoolean)] None ["constr"; "args"]
                    ex_internal3))]|});
(32, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 9;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(33, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privObjectCall|};
       object_properties :=
       from_list [("create", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 58;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("defineProperties", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 56;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("defineProperty", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 16;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("freeze", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 62;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("getOwnPropertyDescriptor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 36;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("getOwnPropertyNames", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 53;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("getPrototypeOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 34;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("isExtensible", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 70;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("isFrozen", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 66;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("isSealed", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 68;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("keys", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 72;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("preventExtensions", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 64;
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
                                        value_object 60;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro [("%ObjectCall", privObjectCall)] None
                    ["constr"; "args"] ex_internal4))]|});
(34, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privgpoCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(35, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 34;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(36, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privgopdCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(37, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(38, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privobjectToStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(39, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privpropEnumCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(40, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privtoLocaleStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(41, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privobjectValueOfCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(42, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privhasOwnPropertyCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(43, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privisPrototypeOfCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(44, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 3;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privErrorProto)] None ["this"; "args"]
                    ex_internal5))]|});
(45, {|object_attrs :=
       {|oattrs_proto := privSyntaxErrorProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 6;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privSyntaxErrorProto)] None ["this"; "args"]
                    ex_internal6))]|});
(46, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 7;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privEvalErrorProto)] None ["this"; "args"]
                    ex_internal7))]|});
(47, {|object_attrs :=
       {|oattrs_proto := privRangeErrorProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 8;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privRangeErrorProto)] None ["this"; "args"]
                    ex_internal8))]|});
(48, {|object_attrs :=
       {|oattrs_proto := privReferenceErrorProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 5;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privReferenceErrorProto)] None
                    ["this"; "args"] ex_internal9))]|});
(49, {|object_attrs :=
       {|oattrs_proto := privTypeErrorProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privRunSelfConstructorCall|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 4;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privTypeErrorProto)] None ["this"; "args"]
                    ex_internal10))]|});
(50, {|object_attrs :=
       {|oattrs_proto := privErrorProto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_string "URIError";
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(51, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privURIErrorConstructor|};
       object_properties :=
       from_list [("prototype", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 50;
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal :=
       from_list [("construct", 
                   value_closure
                   (closure_intro
                    [("%MakeNativeError", privMakeNativeError);
                     ("%ToString", privToString);
                     ("proto", privURIErrorProto)] None ["this"; "args"]
                    ex_internal11))]|});
(52, {|object_attrs :=
       {|oattrs_proto := privObjectProto;
         oattrs_class := "Array";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("concat", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 95;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("constructor", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 101;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("every", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 138;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("filter", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 133;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("forEach", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 127;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("indexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 121;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("join", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 76;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("lastIndexOf", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 124;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("map", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 130;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("pop", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 78;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("push", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 81;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("reduce", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 135;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("reduceRight", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 144;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("reverse", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 84;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("shift", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 87;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("slice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 147;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("some", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 141;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("sort", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 98;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|});
                  ("splice", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 115;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toLocaleString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 93;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("toString", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 90;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|});
                  ("unshift", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 118;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := true|})];
       object_internal := from_list []|});
(53, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privgopnCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(54, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 53;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(55, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 16;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(56, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privdefinePropertiesCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(57, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 56;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(58, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privcreateCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(59, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 58;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(60, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privsealCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(61, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 60;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(62, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privfreezeCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(63, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 62;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(64, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privpreventExtensionsCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(65, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_object 64;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(66, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privisFrozenCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(67, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(68, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privisSealedCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(69, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(70, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privisExtensibleCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(71, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(72, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privkeysCall|};
       object_properties := from_list [];
       object_internal := from_list []|});
(73, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 72;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(74, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privfromccCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(75, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(76, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privjoinCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(77, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(78, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privpopCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(79, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(80, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(81, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privpushCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(82, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(83, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 81;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(84, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privreverseCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(85, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(86, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(87, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privshiftCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := true;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(88, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(89, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(90, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privarrayToStringCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(91, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|});
                  ("writable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(92, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("configurable", 
                   attributes_data_of {|attributes_data_value := value_true;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 76;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(93, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privarrayTLSCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (0));
                                        attributes_data_writable := false;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(94, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
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
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(95, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privconcatCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})];
       object_internal := from_list []|});
(96, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(97, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_object 95;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(98, {|object_attrs :=
       {|oattrs_proto := privFunctionProto;
         oattrs_class := "Function";
         oattrs_extensible := true;
         oattrs_code := privsortCall|};
       object_properties :=
       from_list [("length", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := true|})];
       object_internal := from_list []|});
(99, {|object_attrs :=
       {|oattrs_proto := proto;
         oattrs_class := "Object";
         oattrs_extensible := true;
         oattrs_code := objCode|};
       object_properties :=
       from_list [("enumerable", 
                   attributes_data_of {|attributes_data_value := value_false;
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|});
                  ("value", 
                   attributes_data_of {|attributes_data_value :=
                                        value_number (JsNumber.of_int (1));
                                        attributes_data_writable := true;
                                        attributes_data_enumerable := false;
                                        attributes_data_configurable := false|})];
       object_internal := from_list []|});
(100, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 98;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(101, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privArrayCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 52;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal :=
        from_list [("construct", 
                    value_closure
                    (closure_intro
                     [("%ComputeLength", privComputeLength);
                      ("%JSError", privJSError);
                      ("%MakeArray", privMakeArray);
                      ("%RangeErrorProto", privRangeErrorProto);
                      ("%ToUint32", privToUint32);
                      ("%defineOwnProperty", privdefineOwnProperty)] 
                     None ["this"; "args"] ex_internal12))]|});
(102, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 101;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(103, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privcharAtCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(104, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(105, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 103;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(106, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privcharCodeAtCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(107, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(108, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 106;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(109, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privstringConcatCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(110, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(111, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(112, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsubstringCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(113, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(114, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(115, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privspliceCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(116, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(117, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(118, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privunshiftCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(119, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(120, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(121, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privarrayIndexOfCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(122, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(123, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(124, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privarrayLastIndexOfCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(125, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(126, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(127, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privforeachCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(128, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(129, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 127;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(130, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmapCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(131, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(132, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(133, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privfilterCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(134, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 133;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(135, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privreduceCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(136, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(137, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 135;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(138, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := priveveryCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(139, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(140, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 138;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(141, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsomeCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(142, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(143, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(144, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privreduceRightCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(145, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(146, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(147, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsliceCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(148, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(149, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(150, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privbindCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(151, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(152, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 150;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(153, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privnumberToStringCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(154, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_false;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(155, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 153;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(156, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privstringIndexOfCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(157, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privreplaceCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(158, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privstringLastIndexOfCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(159, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privlocaleCompareCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(160, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privstringSliceCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(161, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtoLowerCaseCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(162, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtoUpperCaseCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(163, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsplitCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(164, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 163;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(165, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := privgetYearCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(166, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := privgetMonthCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(167, {|object_attrs :=
        {|oattrs_proto := privObjectProto;
          oattrs_class := "Date";
          oattrs_extensible := true;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("getDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 176;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getDay", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 174;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 184;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 194;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 206;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 198;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 166;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("getSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 202;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getTime", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 182;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getTimezoneOffset", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 172;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 190;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCDay", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 192;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 186;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 196;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 208;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 200;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 188;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getUTCSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 204;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("getYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 165;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("setDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 228;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 236;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 224;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 212;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 220;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 232;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 216;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setTime", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 210;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCDate", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 230;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCFullYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 238;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCHours", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 226;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMilliseconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 214;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMinutes", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 222;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCMonth", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 234;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setUTCSeconds", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 218;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("setYear", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 244;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toGMTString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 242;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 168;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("toUTCString", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 240;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("valueOf", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 170;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(168, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdateToStringCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(169, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 168;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(170, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdateValueOfCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(171, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privDateCall|};
        object_properties :=
        from_list [("UTC", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 180;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("parse", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 178;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable := true|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 167;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal :=
        from_list [("construct", 
                    value_closure
                    (closure_intro
                     [("%ComputeLength", privComputeLength);
                      ("%DateProto", privDateProto);
                      ("%MakeDate", privMakeDate);
                      ("%MakeDateDayTime", privMakeDateDayTime);
                      ("%MakeDay", privMakeDay);
                      ("%MakeTime", privMakeTime);
                      ("%TimeClip", privTimeClip);
                      ("%ToInteger", privToInteger);
                      ("%ToNumber", privToNumber);
                      ("%ToPrimitive", privToPrimitive);
                      ("%UTC", privUTC);
                      ("%getCurrentUTC", privgetCurrentUTC);
                      ("%parse", privparse)] None ["constr"; "args"]
                     ex_internal13))]|});
(172, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := privdateGetTimezoneOffsetCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(173, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 172;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(174, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdategetDayCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(175, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(176, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdategetDateCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(177, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 176;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(178, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode1|};
        object_properties := from_list [];
        object_internal := from_list []|});
(179, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(180, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode2|};
        object_properties := from_list [];
        object_internal := from_list []|});
(181, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(182, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode3|};
        object_properties := from_list [];
        object_internal := from_list []|});
(183, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(184, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode4|};
        object_properties := from_list [];
        object_internal := from_list []|});
(185, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(186, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode5|};
        object_properties := from_list [];
        object_internal := from_list []|});
(187, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(188, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode6|};
        object_properties := from_list [];
        object_internal := from_list []|});
(189, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(190, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode7|};
        object_properties := from_list [];
        object_internal := from_list []|});
(191, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(192, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode8|};
        object_properties := from_list [];
        object_internal := from_list []|});
(193, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(194, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode9|};
        object_properties := from_list [];
        object_internal := from_list []|});
(195, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(196, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode10|};
        object_properties := from_list [];
        object_internal := from_list []|});
(197, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(198, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode11|};
        object_properties := from_list [];
        object_internal := from_list []|});
(199, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(200, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode12|};
        object_properties := from_list [];
        object_internal := from_list []|});
(201, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(202, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode13|};
        object_properties := from_list [];
        object_internal := from_list []|});
(203, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(204, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode14|};
        object_properties := from_list [];
        object_internal := from_list []|});
(205, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(206, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode15|};
        object_properties := from_list [];
        object_internal := from_list []|});
(207, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(208, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode16|};
        object_properties := from_list [];
        object_internal := from_list []|});
(209, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(210, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode17|};
        object_properties := from_list [];
        object_internal := from_list []|});
(211, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(212, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode18|};
        object_properties := from_list [];
        object_internal := from_list []|});
(213, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(214, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode19|};
        object_properties := from_list [];
        object_internal := from_list []|});
(215, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(216, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode20|};
        object_properties := from_list [];
        object_internal := from_list []|});
(217, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(218, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode21|};
        object_properties := from_list [];
        object_internal := from_list []|});
(219, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(220, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode22|};
        object_properties := from_list [];
        object_internal := from_list []|});
(221, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(222, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode23|};
        object_properties := from_list [];
        object_internal := from_list []|});
(223, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(224, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode24|};
        object_properties := from_list [];
        object_internal := from_list []|});
(225, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(226, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode25|};
        object_properties := from_list [];
        object_internal := from_list []|});
(227, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(228, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode26|};
        object_properties := from_list [];
        object_internal := from_list []|});
(229, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(230, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode27|};
        object_properties := from_list [];
        object_internal := from_list []|});
(231, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(232, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode28|};
        object_properties := from_list [];
        object_internal := from_list []|});
(233, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(234, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode29|};
        object_properties := from_list [];
        object_internal := from_list []|});
(235, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(236, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode30|};
        object_properties := from_list [];
        object_internal := from_list []|});
(237, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(238, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode31|};
        object_properties := from_list [];
        object_internal := from_list []|});
(239, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(240, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode32|};
        object_properties := from_list [];
        object_internal := from_list []|});
(241, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(242, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode33|};
        object_properties := from_list [];
        object_internal := from_list []|});
(243, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(244, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode34|};
        object_properties := from_list [];
        object_internal := from_list []|});
(245, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(246, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := privtestCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(247, {|object_attrs :=
        {|oattrs_proto := privObjectProto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("constructor", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 248;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("test", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 246;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(248, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privRegExpCode|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 247;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal :=
        from_list [("construct", 
                    value_closure
                    (closure_intro [("%RegExpProto", privRegExpProto)] 
                     None ["obj"; "this"; "args"] ex_internal14))]|});
(249, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privparseIntCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(250, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdecodeURICall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(251, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privdecodeURIComponentCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(252, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privencodeURICall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(253, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privencodeURIComponentCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(254, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := privexpCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(255, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LN10", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LN2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (0));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LOG10E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (0));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("LOG2E", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("PI", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (3));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("SQRT1_2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (0));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("SQRT2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("abs", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 262;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("acos", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 264;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("asin", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 266;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("atan", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 268;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("atan2", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 270;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("ceil", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 286;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("cos", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 272;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("exp", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 254;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("floor", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 288;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("log", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 284;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("max", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 259;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("min", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 256;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("pow", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 290;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("random", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 274;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("round", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 276;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("sin", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 278;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("sqrt", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 280;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|});
                   ("tan", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 282;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(256, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathMinCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(257, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(258, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 256;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(259, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathMaxCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(260, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (2));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(261, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 259;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(262, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathAbsCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(263, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(264, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privacosCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(265, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 264;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(266, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privasinCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(267, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 266;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(268, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privatanCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(269, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(270, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privatan2Call|};
        object_properties := from_list [];
        object_internal := from_list []|});
(271, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(272, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privcosCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(273, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(274, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privrandomCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(275, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(276, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privroundCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(277, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(278, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsinCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(279, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(280, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privsqrtCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(281, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(282, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtanCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(283, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(284, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathLogCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(285, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(286, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathCeilCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(287, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(288, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathFloorCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(289, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(290, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privmathPowCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(291, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(292, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode35|};
        object_properties := from_list [];
        object_internal := from_list []|});
(293, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(294, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode36|};
        object_properties := from_list [];
        object_internal := from_list []|});
(295, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(296, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := objCode37|};
        object_properties := from_list [];
        object_internal := from_list []|});
(297, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(298, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtoFixedCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := true;
                                         attributes_data_configurable := true|})];
        object_internal := from_list []|});
(299, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_number (JsNumber.of_int (1));
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(300, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         false|})];
        object_internal := from_list []|});
(301, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privnumTLSCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(302, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 301;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(303, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtoExponentialCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(304, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 303;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(305, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privtoPrecisionCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(306, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 305;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(307, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "ObjEnvRec";
          oattrs_extensible := true;
          oattrs_code := objCode|};
        object_properties := from_list [];
        object_internal :=
        from_list [("bindings",  value_object 2);
                   ("parent",  value_null);
                   ("provideThis",  value_false)]|});
(308, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privlogCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(309, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
          oattrs_code := objCode|};
        object_properties :=
        from_list [("error", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 308;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("info", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 308;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("log", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 308;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("warn", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 308;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(310, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privevalCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(311, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privRunSelfConstructorCall|};
        object_properties :=
        from_list [("length", 
                    attributes_data_of {|attributes_data_value :=
                                         value_number (JsNumber.of_int (0));
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("prototype", 
                    attributes_data_of {|attributes_data_value :=
                                         value_object 12;
                                         attributes_data_writable := false;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal :=
        from_list [("construct", 
                    value_closure
                    (closure_intro
                     [("%ComputeLength", privComputeLength);
                      ("%ToString", privToString);
                      ("%evalCall", privevalCall)] None ["this"; "args"]
                     ex_internal15))]|});
(312, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privisFiniteCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(313, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privparseFloatCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(314, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privescapeCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(315, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 314;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|});
(316, {|object_attrs :=
        {|oattrs_proto := privFunctionProto;
          oattrs_class := "Function";
          oattrs_extensible := true;
          oattrs_code := privunescapeCall|};
        object_properties := from_list [];
        object_internal := from_list []|});
(317, {|object_attrs :=
        {|oattrs_proto := proto;
          oattrs_class := "Object";
          oattrs_extensible := true;
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
                                         value_object 316;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|});
                   ("writable", 
                    attributes_data_of {|attributes_data_value := value_true;
                                         attributes_data_writable := true;
                                         attributes_data_enumerable := false;
                                         attributes_data_configurable :=
                                         false|})];
        object_internal := from_list []|})
].
Definition init_ctx : ctx := from_list ctx_items.
Definition init_store : store := from_list store_items.