Require Import LibInt.
Require Import JsNumber.
Require Import String.
Require Import LjsSyntax.
Require Import LjsStore.
Require Import LjsMonads.
Require Import LjsCommon.
Require Import LjsValues.
Open Scope string_scope.

Implicit Type store : store.

Implicit Type st : store.
Implicit Type v : value.
Implicit Type s : string.
Implicit Type n : number.
Implicit Type i : id.
Implicit Type o : out.
Implicit Type c : ctx.
Implicit Type ptr : object_ptr.
Implicit Type obj : object.

(****** Unary operators ******)

Definition nnot store (v : value) :=
  match v with
  | value_bool b => result_some (value_bool (!b))
  | _ => result_fail "negation with non-boolean"
  end
.

Parameter _print_string : string -> unit.
Parameter _pretty : store -> value -> unit.
Definition _seq {X Y : Type} (x : X) (y : Y) : Y :=
  y
.

Definition print st v :=
  _seq (_print_string (value_to_str_cast v)) (result_some value_undefined)
.

Definition pretty store v :=
  _seq
  (_pretty store v)
  (result_some value_undefined)
.

Definition strlen store v :=
  match v with
  | value_string s => result_some (value_number (JsNumber.of_int (String.length s)))
  | _ => result_fail "strlen got non-string."
  end
.

Definition unary_arith (op : number -> number) (v : value) : resultof value :=
  match v with
  | value_number n => result_some (value_number (op n))
  | _ => result_fail "Arithmetic with non-number."
  end
.

Definition unary_int_arith (op : int -> int) (v : value) : resultof value :=
  match v with
  | value_number n => result_some (value_number (of_int (op (to_int32 n))))
  | _ => result_fail "Arithmetic with non-number."
  end
.

Definition ascii_ntoc (v : value) : resultof value :=
  match v with
  | value_number n => result_some (value_string (String (_ascii_of_int (to_int32 n)) EmptyString))
  | _ => result_fail "ascii_ntoc"
  end
.

Definition ascii_cton (v : value) : resultof value :=
  match v with
  | value_string (String c _) => result_some (value_number (of_int (_int_of_ascii c)))
  | _ => result_fail "ascii_cton"
  end
.

Definition unary_operator (op : unary_op) store v : resultof value :=
    match op with
    | unary_op_print => print store v
    | unary_op_pretty => pretty store v
    | unary_op_strlen => strlen store v
    | unary_op_typeof => result_some (value_string (typeof v))
    | unary_op_is_primitive => result_some (value_bool (decide (is_primitive v)))
    | unary_op_is_closure => result_some (value_bool (decide (is_closure v)))
    | unary_op_is_object => result_some (value_bool (decide (is_object v)))
    | unary_op_abs => unary_arith JsNumber.absolute v
    | unary_op_floor => unary_arith JsNumber.floor v
    | unary_op_prim_to_str => result_some (value_string (value_to_str_cast v))
    | unary_op_prim_to_num => result_some (value_number (value_to_num_cast v))
    | unary_op_prim_to_bool => result_some (value_bool (value_to_bool_cast v))
    | unary_op_not => nnot store v
    | unary_op_bnot => unary_int_arith int32_bitwise_not v
    | unary_op_to_int32 => unary_int_arith (fun x => x) v
    | unary_op_ascii_ntoc => ascii_ntoc v
    | unary_op_ascii_cton => ascii_cton v
    | _ => result_fail ("Unary operator " ++ " not implemented.")
    end
.

(****** Binary operators ******)

Definition has_property store v1_loc v2 :=
  assert_get_object_ptr v1_loc (fun ptr =>
    match v2 with
    | value_string s =>
      assert_get_object_from_ptr store ptr (fun obj =>
        if_result_some (get_property store obj s) (fun ret =>
          match ret with
          | Some _ => result_some value_true
          | None => result_some value_false
          end
      ))
    | _ => result_fail "hasProperty expected a string."
    end
  )
.

Definition has_own_property store v1 v2 :=
  match (v1, v2) with
  | (value_object ptr, value_string s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (get_object_property obj s) with
      | Some _ => result_some value_true
      | None => result_some value_false
      end
    )
  | _ => result_fail "hasOwnProperty expected an object and a string."
  end
.
      
Definition prop_to_obj store v1 v2 :=
  let make_attr := (fun x => attributes_data_of (attributes_data_intro x false false false)) in
  match (v1, v2) with
  | (value_object ptr, value_string s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (get_object_property obj s) with
      | Some (attributes_data_of (attributes_data_intro val writ enum config)) =>
        let props := \{} \("configurable" := make_attr (value_bool config))
                         \("enumerable" := make_attr (value_bool enum)) 
                         \("writable" := make_attr (value_bool writ)) 
                         \("value" := make_attr val) in
        let obj := object_intro (oattrs_intro value_undefined "Object" false value_undefined value_null) props in
        let (store, loc) := add_object store obj in
        result_some loc
      | Some (attributes_accessor_of (attributes_accessor_intro get set enum config)) =>
        let props := \{} \("configurable" := make_attr (value_bool config)) 
                         \("enumerable" := make_attr (value_bool enum)) 
                         \("setter" := make_attr set) 
                         \("getter" := make_attr get) in
        let obj := object_intro (oattrs_intro value_undefined "Object" false value_undefined value_null) props in
        let (store, loc) := add_object store obj in
        result_some loc
      | None => result_some value_undefined
      end
    )
  | _ => result_fail "hasOwnProperty expected an object and a string."
  end
.

Definition string_plus store v1 v2 : resultof value :=
  match (v1, v2) with
  | (value_string s1, value_string s2) => result_some (value_string (s1++s2))
  | _ => result_fail "Only strings can be concatenated."
  end
.

Parameter _nat_of_float : number -> nat.

Definition char_at store v1 v2 :=
  match (v1, v2) with
  | (value_string s, value_number n) =>
      match (String.get (_nat_of_float n) s) with
      | Some char => result_some (value_string (String.String char String.EmptyString))
      | None => result_fail "char_at called with index larger than length."
      end
  | _ => result_fail "char_at called with wrong argument types."
  end
.

Definition is_accessor store v1_loc v2 :=
  assert_get_object_ptr v1_loc (fun ptr =>
    match v2 with
    | value_string s =>
      assert_get_object_from_ptr store ptr (fun obj =>
        if_result_some (get_property store obj s) (fun ret =>
          match ret with
          | Some (attributes_data_of _) => result_some value_false
          | Some (attributes_accessor_of _) => result_some value_true
          | None => result_fail "isAccessor topped out."
          end
      ))
    | _ => result_fail "isAccessor expected an object and a string."
    end
  )
.

Parameter _same_value : value -> value -> bool.

Definition same_value store v1 v2 :=
  result_some (value_bool (_same_value v1 v2))
.

Definition arith (op : number -> number -> number) (v1 v2 : value) : resultof value :=
  match v1, v2 with
  | value_number n1, value_number n2 => result_some (value_number (op n1 n2))
  | _, _ => result_fail "Arithmetic with non-numbers."
  end
.

Definition int_arith (op : int -> int -> int) (v1 v2 : value) : resultof value :=
  match v1, v2 with
  | value_number n1, value_number n2 => result_some (value_number (of_int (op (to_int32 n1) (to_int32 n2))))
  | _, _ => result_fail "Arithmetic with non-numbers."
  end
.

Definition cmp store undef_left undef_both undef_right (op : number -> number -> bool) (v1 v2 : value) : resultof value :=
  match (v1, v2) with
  | (value_number n1, value_number n2) => result_some (if (op n1 n2) then value_true else value_false)
  | (value_undefined, value_number _) => result_some undef_left
  | (value_undefined, value_undefined) => result_some undef_both
  | (value_number _, value_undefined) => result_some undef_right
  | _ => result_fail "Comparison/order of non-numbers."
  end
.

Parameter le_bool : number -> number -> bool.
Parameter gt_bool : number -> number -> bool.
Parameter ge_bool : number -> number -> bool.

Parameter _string_lt_bool : string -> string -> bool.

Definition string_lt v1 v2 : resultof value :=
  match v1, v2 with
  | value_string s1, value_string s2 => result_some (value_bool (_string_lt_bool s1 s2))
  | _, _ => result_fail "string_lt"
  end
.

Definition locale_compare v1 v2 : resultof value :=
  match v1, v2 with
  | value_string s1, value_string s2 => result_some (value_bool (_string_lt_bool s1 s2))
  | _, _ => result_fail "locale_compare"
  end
.

Definition binary_operator (op : binary_op) store v1 v2 : resultof value :=
      match op with
      | binary_op_add => arith JsNumber.add v1 v2
      | binary_op_sub => arith JsNumber.sub v1 v2
      | binary_op_mul => arith JsNumber.mult v1 v2
      | binary_op_div => arith JsNumber.div v1 v2
      | binary_op_mod => arith JsNumber.fmod v1 v2
      | binary_op_lt => cmp store value_true value_false value_false JsNumber.lt_bool v1 v2
      | binary_op_le => cmp store value_true value_true value_false le_bool v1 v2
      | binary_op_gt => cmp store value_false value_false value_true gt_bool v1 v2
      | binary_op_ge => cmp store value_false value_true value_true ge_bool v1 v2
      | binary_op_stx_eq => result_some (value_bool (decide (stx_eq v1 v2)))
      | binary_op_same_value => same_value store v1 v2
      | binary_op_has_property => has_property store v1 v2
      | binary_op_has_own_property => has_own_property store v1 v2
      | binary_op_string_plus => string_plus store v1 v2
      | binary_op_char_at => char_at store v1 v2
      | binary_op_is_accessor => is_accessor store v1 v2
      | binary_op_prop_to_obj => prop_to_obj store v1 v2 (* For debugging purposes *)
      | binary_op_band => int_arith int32_bitwise_and v1 v2
      | binary_op_bor => int_arith int32_bitwise_or v1 v2
      | binary_op_bxor => int_arith int32_bitwise_xor v1 v2
      | binary_op_shiftl => int_arith int32_left_shift v1 v2
      | binary_op_shiftr => int_arith int32_right_shift v1 v2
      | binary_op_zfshiftr => int_arith uint32_right_shift v1 v2
      | binary_op_string_lt => string_lt v1 v2
      | binary_op_locale_compare => locale_compare v1 v2
      | _ => result_fail ("Binary operator " ++ " not implemented.")
      end
.
