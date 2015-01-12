Require Import LibInt.
Require Import JsNumber.
Require Import String.
Require Import Store.
Require Import Monads.
Require Import Values.
Require Import Context.
Open Scope string_scope.

Implicit Type runs : Context.runs_type.
Implicit Type store : Store.store.

(****** Unary operators ******)

Definition typeof store (v : value) :=
  match v with
  | Undefined => result_value store (String "undefined")
  | Null => result_value store (String  "null")
  | String _ => result_value store (String  "string")
  | Number _ => result_value store (String  "number")
  | True | False => result_value store (String  "boolean")
  | Object ptr =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (object_code obj) with
      | Some  _ => result_value store (String "function")
      | None => result_value store (String  "object")
      end
    )
  | Closure _ _ _ _ => result_fail "typeof got lambda"
  end
.

Definition is_primitive store v :=
  match v with
  | Undefined | Null | String _ | Number _ | True | False =>
    result_value store True
  | _ =>
    result_value store False
  end
.

Definition void store (v : value) :=
  result_value store Undefined
.

Definition prim_to_str store (v : value) :=
  match v with
  | Undefined => result_value store (String "undefined")
  | Null => result_value store (String "null")
  | String s => result_value store (String s)
  | Number n => result_value store (String (JsNumber.to_string n))
  | True => result_value store (String "true")
  | False => result_value store (String "false")
  | _ => result_fail "prim_to_str not implemented for this type."
  end
.

Definition prim_to_num store (v : value) :=
  match v with
  | Undefined => result_value store (Number JsNumber.nan)
  | Null => result_value store (Number JsNumber.zero)
  | True => result_value store (Number JsNumber.one)
  | False => result_value store (Number JsNumber.zero)
  | Number n => result_value store (Number n)
  | String "" => result_value store (Number JsNumber.zero)
  | String s => result_value store (Number (JsNumber.from_string s))
  | _ => result_fail "prim_to_num got invalid value."
  end
.

Definition prim_to_bool store (v : value) :=
  match v with
  | True => result_value store True
  | False => result_value store False
  | Undefined => result_value store False
  | Null => result_value store False
  | Number n => result_value store (
      if (decide(n = JsNumber.nan)) then
        False
      else if (decide(n = JsNumber.zero)) then
        False
      else if (decide(n = JsNumber.neg_zero)) then
        False
      else
        True
    )
  | String "" => result_value store False
  | String _ => result_value store True
  | _ => result_value store True
  end
.

Definition nnot store (v : value) :=
  match v with
  | Undefined => result_value store True
  | Null => result_value store True
  | True => result_value store False
  | False => result_value store True
  | Number d => result_value store (
      if (decide(d = JsNumber.zero)) then
        True
      else if (decide(d = JsNumber.neg_zero)) then
        True
      else if (decide(d <> d)) then
        True
      else
        False
    )
  | String "" => result_value store True
  | String _ => result_value store False
  | Object _ => result_value store False
  | Closure _ _ _ _ => result_value store False
  end
.

Parameter _print_string : string -> unit.
Parameter _pretty : store -> value -> unit.
Definition _seq {X Y : Type} (x : X) (y : Y) : Y :=
  y
.

Definition print store (v : value) :=
  match v with
  | String s => _seq (_print_string s) (result_value store Undefined)
  | Number n => _seq (_print_string (JsNumber.to_string n)) (result_value store Undefined)
  | _ => result_fail "print of non-string and non-number."
  end
.

Definition pretty runs store v :=
  _seq
  (_pretty store v)
  (result_value store Undefined)
.

Definition strlen store v :=
  match v with
  | String s => result_value store (Number (JsNumber.of_int (String.length s)))
  | _ => result_fail "strlen got non-string."
  end
.

Definition numstr_to_num store (v : value) :=
  match v with
  | String "" => result_value store (Number JsNumber.zero)
  | String s => result_value store (Number (JsNumber.from_string s))
  | _ => result_fail "numstr_to_num got invalid value."
  end
.

Definition unary_arith store (op : number -> number) (v : value) : result :=
  match v with
  | Number n => result_value store (Number (op n))
  | _ => result_fail "Arithmetic with non-number."
  end
.

Definition unary (op : Syntax.unary_op) runs store v : result :=
    match op with
    | Syntax.unary_op_print => print store v
    | Syntax.unary_op_pretty => pretty runs store v
    | Syntax.unary_op_strlen => strlen store v
    | Syntax.unary_op_typeof => typeof store v
    | Syntax.unary_op_is_primitive => is_primitive store v
    | Syntax.unary_op_abs => unary_arith store JsNumber.absolute v
    | Syntax.unary_op_void => void store v
    | Syntax.unary_op_floor => unary_arith store JsNumber.floor v
    | Syntax.unary_op_prim_to_str => prim_to_str store v
    | Syntax.unary_op_prim_to_num => prim_to_num store v
    | Syntax.unary_op_prim_to_bool => prim_to_bool store v
    | Syntax.unary_op_not => nnot store v
    | Syntax.unary_op_numstr_to_num => numstr_to_num store v
    | _ => result_fail ("Unary operator " ++ " not implemented.")
    end
.

(****** Binary operators ******)

Parameter _number_eq_bool : number -> number -> bool.

Definition stx_eq store v1 v2 :=
  match (v1, v2) with
  | (String s1, String s2) => result_value store (if (decide(s1 = s2)) then True else False)
  | (Null, Null) => result_value store True
  | (Undefined, Undefined) => result_value store True
  | (True, True) => result_value store True
  | (False, False) => result_value store True
  | (Number n1, Number n2) =>
    return_bool store (_number_eq_bool n1 n2) 
  | (Object ptr1, Object ptr2) => result_value store (if (beq_nat ptr1 ptr2) then True else False)
  | (Closure id1 _ _ _, Closure id2 _ _ _) => result_value store (if (beq_nat id1 id2) then True else False)
  | _ => result_value store False
  (*| _ => result_value store (if (beq_nat v1_loc v2_loc) then True else False)*)
  end
.

Definition has_property runs store v1_loc v2 :=
  match v2 with
  | String s =>
    let res := Context.runs_type_get_property runs store (v1_loc, s) in
    if_result_some res (fun ret =>
      match ret with
      | Some _ => result_value store True
      | None => result_value store False
      end
    )
  | _ => result_fail "hasProperty expected a string."
  end
.

Definition has_own_property store v1 v2 :=
  match (v1, v2) with
  | (Object ptr, String s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (get_object_property obj s) with
      | Some _ => result_value store True
      | None => result_value store False
      end
    )
  | _ => result_fail "hasOwnProperty expected an object and a string."
  end
.
      

Definition prop_to_obj store v1 v2 :=
  let make_attr := (fun x => attributes_data_of (attributes_data_intro x false false false)) in
  match (v1, v2) with
  | (Object ptr, String s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (get_object_property obj s) with
      | Some (attributes_data_of (attributes_data_intro val writ enum config)) =>
        let props := Heap.write Heap.empty "configurable" (make_attr (bool_to_value config)) in
        let props := Heap.write props "enumerable" (make_attr (bool_to_value enum)) in
        let props := Heap.write props "writable" (make_attr (bool_to_value writ)) in
        let props := Heap.write props "value" (make_attr val) in
        let obj := object_intro Undefined "Object" false None props None in
        let (store, loc) := Store.add_object store obj in
        result_value store loc
      | Some (attributes_accessor_of (attributes_accessor_intro get set enum config)) =>
        let props := Heap.write Heap.empty "configurable" (make_attr (bool_to_value config)) in
        let props := Heap.write props "enumerable" (make_attr (bool_to_value enum)) in
        let props := Heap.write props "setter" (make_attr set) in
        let props := Heap.write props "getter" (make_attr get) in
        let obj := object_intro Undefined "Object" false None props None in
        let (store, loc) := Store.add_object store obj in
        result_value store loc
      | None => result_value store Undefined
      end
    )
  | _ => result_fail "hasOwnProperty expected an object and a string."
  end
.

Definition string_plus store v1 v2 : result :=
  match (v1, v2) with
  | (String s1, String s2) => result_value store (String (s1++s2))
  | _ => result_fail "Only strings can be concatenated."
  end
.

Parameter _nat_of_float : number -> nat.

Definition char_at store v1 v2 :=
  match (v1, v2) with
  | (String s, Number n) =>
      match (String.get (_nat_of_float n) s) with
      | Some char => result_value store (String (String.String char String.EmptyString))
      | None => result_fail "char_at called with index larger than length."
      end
  | _ => result_fail "char_at called with wrong argument types."
  end
.

Definition is_accessor runs store v1_loc v2 :=
  match v2 with
  | String s =>
    let res := Context.runs_type_get_property runs store (v1_loc, s) in
    if_result_some res (fun ret =>
      match ret with
      | Some (attributes_data_of _) => result_value store False
      | Some (attributes_accessor_of _) => result_value store True
      | None => result_fail "isAccessor topped out."
      end
    )
  | _ => result_fail "isAccessor expected an object and a string."
  end
.

Parameter _same_value : value -> value -> bool.

Definition same_value store v1 v2 :=
  return_bool store (_same_value v1 v2)
.

Definition arith store (op : number -> number -> number) (v1 v2 : value) : result :=
  match (v1, v2) with
  | (Number n1, Number n2) => result_value store (Number (op n1 n2))
  | _ => result_fail "Arithmetic with non-numbers."
  end
.

Definition cmp store undef_left undef_both undef_right (op : number -> number -> bool) (v1 v2 : value) : result :=
  match (v1, v2) with
  | (Number n1, Number n2) => result_value store (if (op n1 n2) then True else False)
  | (Undefined, Number _) => result_value store undef_left
  | (Undefined, Undefined) => result_value store undef_both
  | (Number _, Undefined) => result_value store undef_right
  | _ => result_fail "Comparison/order of non-numbers."
  end
.

Parameter le_bool : number -> number -> bool.
Parameter gt_bool : number -> number -> bool.
Parameter ge_bool : number -> number -> bool.


Definition binary (op : Syntax.binary_op) runs store v1 v2 : result :=
      match op with
      | Syntax.binary_op_add => arith store JsNumber.add v1 v2
      | Syntax.binary_op_sub => arith store JsNumber.sub v1 v2
      | Syntax.binary_op_mul => arith store JsNumber.mult v1 v2
      | Syntax.binary_op_div => arith store JsNumber.div v1 v2
      | Syntax.binary_op_mod => arith store JsNumber.fmod v1 v2
      | Syntax.binary_op_lt => cmp store True False False JsNumber.lt_bool v1 v2
      | Syntax.binary_op_le => cmp store True True False le_bool v1 v2
      | Syntax.binary_op_gt => cmp store False False True gt_bool v1 v2
      | Syntax.binary_op_ge => cmp store False True True ge_bool v1 v2
      | Syntax.binary_op_stx_eq => stx_eq store v1 v2
      | Syntax.binary_op_same_value => same_value store v1 v2
      | Syntax.binary_op_has_property => has_property runs store v1 v2
      | Syntax.binary_op_has_own_property => has_own_property store v1 v2
      | Syntax.binary_op_string_plus => string_plus store v1 v2
      | Syntax.binary_op_char_at => char_at store v1 v2
      | Syntax.binary_op_is_accessor => is_accessor runs store v1 v2
      | Syntax.binary_op_prop_to_obj => prop_to_obj store v1 v2 (* For debugging purposes *)
      | _ => result_fail ("Binary operator " ++ " not implemented.")
      end
.
