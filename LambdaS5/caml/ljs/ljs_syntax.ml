
module Pos = 
  struct
    type t = Lexing.position * Lexing.position * bool (* start, end, is synthetic? *)
    let dummy = (Lexing.dummy_pos, Lexing.dummy_pos, true)
    let real (p_start, p_end) = (p_start, p_end, false)
  end

type id = string

type oattr = 
  | Proto
  | Klass
  | Extensible
  | Code

let string_of_oattr oattr = match oattr with
  | Proto -> "#proto"
  | Klass -> "#class"
  | Extensible -> "#extensible"
  | Code -> "#code"

type pattr =
  | Value
  | Getter
  | Setter
  | Config
  | Writable
  | Enum

let string_of_attr attr = match attr with
  | Value -> "#value"
  | Getter -> "#getter"
  | Setter -> "#setter"
  | Config -> "#configurable"
  | Writable -> "#writable"
  | Enum -> "#enumerable"

type exp =
  | Empty of Pos.t
  | Null of Pos.t
  | Undefined of Pos.t
  | String of Pos.t * string
  | Num of Pos.t * float
  | Int of Pos.t * int
  | True of Pos.t
  | False of Pos.t
  | Id of Pos.t * id
  | Object of Pos.t * attrs * (string * exp) list * (string * prop) list
      (* GetAttr (Pos.t, property, object, field name) *)
  | GetAttr of Pos.t * pattr * exp * exp
      (* SetAttr (Pos.t, property, object, field name, new value) *)
  | SetAttr of Pos.t * pattr * exp * exp * exp
  | GetObjAttr of Pos.t * oattr * exp
  | SetObjAttr of Pos.t * oattr * exp * exp
  | DeleteField of Pos.t * exp * exp (* Pos.t, obj, field *)
  | GetInternal of Pos.t * string * exp
  | SetInternal of Pos.t * string * exp * exp
  | OwnFieldNames of Pos.t * exp
  | Op1 of Pos.t * string * exp
  | Op2 of Pos.t * string * exp * exp
  | If of Pos.t * exp * exp * exp
  | App of Pos.t * exp * exp list
  | Seq of Pos.t * exp * exp
  | JSeq of Pos.t * exp * exp
  | Let of Pos.t * id * exp * exp
  | Rec of Pos.t * id * exp * exp (** value bound must be an [ELambda] *)
  | Label of Pos.t * id * exp
  | Break of Pos.t * id * exp
  | TryCatch of Pos.t * exp * exp
      (** Catch block must be an [ELambda] *)
  | TryFinally of Pos.t * exp * exp
  | Throw of Pos.t * exp
  | Lambda of Pos.t * id list * exp
  | Eval of Pos.t * exp * exp (* Pos.t, string to be evaled, env object  *)
  | Hint of Pos.t * string * exp
  | Fail of Pos.t * string
  | Dump
and data =       
    {value : exp;
     writable : bool; }
and accessor =       
    {getter : exp;
     setter : exp; }
and prop =
  | Data of data * bool * bool (* value, enumerable, configurable *)
  | Accessor of accessor * bool * bool
and attrs =
    { primval : exp option;
      code : exp option;
      proto : exp option;
      klass : string;
      extensible : bool; }

(* Some useful defaults for these things, to avoid typing too much *)
let d_attrs = 
  { primval = None;
    code = None;
    proto = Some (Null Pos.dummy); 
    klass = "Object";
    extensible = true; }

let d_data =
  { value = Undefined Pos.dummy;
    writable = true; }

let d_accessor = 
  { getter = Undefined Pos.dummy;
    setter = Undefined Pos.dummy; }

let with_enum p v = 
  match p with
  | Data (x, e, c) -> Data (x, v, c)
  | Accessor (x, e, c) -> Accessor (x, v, c)

let with_config p v = 
  match p with
  | Data (x, e, c) -> Data (x, e, v)
  | Accessor (x, e, c) -> Accessor (x, e, v)

