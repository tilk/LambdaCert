%{
open Ljs_syntax

let with_pos exp pos = match exp with
  | Empty _ -> Empty pos
  | Null _ -> Null pos
  | Undefined _ -> Undefined pos
  | String (_, str) -> String (pos, str)
  | Int (_, str) -> Int (pos, str)
  | Num (_, num) -> Num (pos, num)
  | True _ -> True pos
  | False _ -> False pos
  | Id (_, id) -> Id (pos, id)
  | Object (_, attrs, iattrs, props) -> Object (pos, attrs, iattrs, props)
  | GetAttr (_, pattr, obj, field) -> GetAttr (pos, pattr, obj, field)
  | SetAttr (_, prop, obj, field, value) -> SetAttr (pos, prop, obj, field, value)
  | GetObjAttr (_, oattr, obj) -> GetObjAttr (pos, oattr, obj)
  | SetObjAttr (_, oattr, obj, v) -> SetObjAttr (pos, oattr, obj, v)
  | DeleteField (_, obj, field) -> DeleteField (pos, obj, field)
  | GetInternal (_, oattr, obj) -> GetInternal (pos, oattr, obj)
  | SetInternal (_, oattr, obj, v) -> SetInternal (pos, oattr, obj, v)
  | OwnFieldNames (_, obj) -> OwnFieldNames(pos, obj)
  | Op1 (_, op, exp) -> Op1 (pos, op, exp)
  | Op2 (_, op, left, right) -> Op2 (pos, op, left, right)
  | If (_, test, trueBlock, falseBlock) -> If (pos, test, trueBlock, falseBlock)
  | App (_, func, args) -> App (pos, func, args)
  | Seq (_, left, right) -> Seq (pos, left, right)
  | JSeq (_, left, right) -> Seq (pos, left, right)
  | Let (_, id, value, body) -> Let (pos, id, value, body)
  | Rec (_, id, value, body) -> Rec (pos, id, value, body)
  | Label (_, id, exp) -> Label (pos, id, exp)
  | Break (_, id, exp) -> Break (pos, id, exp)
  | TryCatch (_, tryBlock, catchBlock) -> TryCatch (pos, tryBlock, catchBlock)
  | TryFinally (_, tryBlock, finallyBlock) -> TryFinally (pos, tryBlock, finallyBlock)
  | Throw (_, value) -> Throw (pos, value)
  | Lambda (_, ids, body) -> Lambda (pos, ids, body)
  | Eval (_, exp, obj) -> Eval (pos, exp, obj)
  | Hint (_, label, exp) -> Hint (pos, label, exp)
  | Fail (_, str) -> Fail (pos, str)
  | Dump -> Dump

%}
 
%token <int> INT
%token <float> NUM
%token <string> STRING
%token <string> HINT
%token <bool> BOOL
%token <string> ID
%token UNDEFINED EMPTY NULL FUNC LET DELETE LBRACE RBRACE LPAREN RPAREN LBRACK
  RBRACK EQUALS COMMA BANG REF COLON PRIM IF ELSE SEMI JSEMI
  LABEL BREAK TRY CATCH FINALLY THROW EQEQEQUALS EQEQUALS TYPEOF FAIL
  ISCLOSURE ISPRIMITIVE ISOBJECT
  PLUS MINUS MULT DIV
  AMPAMP PIPEPIPE RETURN BANGEQEQUALS BANGEQUALS FUNCTION REC WRITABLE GETTER SETTER
  CONFIG VALUE ENUM LT GT PROTO CODE EXTENSIBLE CLASS EVAL GETFIELDS PRIMVAL
  INTCAST

%token EOF
%right SEMI
%left LET REC
%left THROW CATCH FINALLY 
%left PIPEPIPE
%left AMPAMP
%left EQEQEQUALS BANGEQEQUALS EQEQUALS BANGEQUALS
%left BANG
%left PLUS MINUS
%left MULT DIV
%left UMINUS
%left LBRACK
%nonassoc THEN
%left ELSE
%left LPAREN

%type <Ljs_syntax.exp> prog
%type <Ljs_syntax.exp -> Ljs_syntax.exp> env

%start prog
%start env


%%

const :
 | NUM { Num (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | INT {  Num (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), (float_of_int $1)) }
 | INTCAST INT {  Int (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $2) }
 | STRING {  String (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | UNDEFINED { Undefined (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) }
 | EMPTY { Empty (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) }
 | NULL { Null (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) }
 | BOOL { if $1 
          then True (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) 
          else False (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) }

more_oattrs :
 | COMMA oattrsv { $2 }
 | COMMA { (d_attrs, []) }
 | { (d_attrs, []) }

oattrsv :
 | EXTENSIBLE COLON BOOL more_oattrs { ({ (fst $4) with extensible = $3 }, snd $4) }
 | PROTO COLON exp more_oattrs { ({ (fst $4) with proto = Some $3 }, snd $4) }
 | CODE COLON exp more_oattrs { ({ (fst $4) with code = Some $3 }, snd $4) }
 | CLASS COLON STRING more_oattrs { ({ (fst $4) with klass = $3 }, snd $4) }
 | ID COLON exp more_oattrs { (fst $4, ($1, $3) :: snd $4) }

oattr_name :
 | PROTO { Proto }
 | CODE { Code }
 | CLASS { Klass }
 | EXTENSIBLE { Extensible }

attr_name :
 | WRITABLE { Writable }
 | CONFIG { Config }
 | VALUE { Value }
 | SETTER { Setter }
 | GETTER { Getter }
 | ENUM { Enum }

pattrs :
 | VALUE exp COMMA WRITABLE BOOL
     { Data ({ value = $2; writable = $5 }, false, false) }
 | GETTER exp COMMA SETTER exp
     { Accessor ({ getter = $2; setter = $5 }, false, true) }

prop_attrs :
 | pattrs { $1 }
 | prop_attrs COMMA ENUM BOOL { with_enum $1 $4 }
 | prop_attrs COMMA CONFIG BOOL { with_config $1 $4 }

prop :
 | STRING COLON LBRACE prop_attrs RBRACE { ($1, $4) }
 | ID COLON LBRACE prop_attrs RBRACE { ($1, $4) }

props :
 | { [] }
 | prop { [$1] }
 | prop COMMA props { $1 :: $3 }

exps :
 | { [] }
 | exp { [$1] }
 | exp COMMA exps { $1 :: $3 }

ids :
 | { [] }
 | ID { [$1] }
 | ID COMMA ids { $1 :: $3 }

func :
 | FUNC LPAREN ids RPAREN atom
   { Lambda (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), $3, $5) }

ifexp :
 | IF LPAREN exp RPAREN exp ELSE atom
     { If (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | IF LPAREN exp RPAREN exp %prec THEN
     { If (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), $3, $5, 
	    Undefined (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5))) }

atom :
 | const { $1 }
 | ID { Id (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | LBRACE LBRACK oattrsv RBRACK props RBRACE 
   { Object (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), fst $3, snd $3, $5 )}
 | LBRACE LBRACK RBRACK props RBRACE 
   { Object (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), d_attrs, [], $4 )}
 | braced_seq_exp
   { $1 }
 | LPAREN exp RPAREN { $2 }
 | func { $1 }
 | ifexp { $1 }
 | TYPEOF atom
     { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "typeof", $2) }
 | ISOBJECT atom
     { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "object?", $2) }
 | ISPRIMITIVE atom
     { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "primitive?", $2) }
 | ISCLOSURE atom
     { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "closure?", $2) }
     
exp :
 | atom { $1 }
 | exp LPAREN exps RPAREN 
   { App (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $1, $3) }
 | FAIL LPAREN STRING RPAREN
   { Fail (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $3) }
 | GETFIELDS LPAREN exp RPAREN
   { OwnFieldNames (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $3) }
 | EVAL LPAREN exp COMMA exp RPAREN
     { Eval (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $3, $5) }
 | PRIM LPAREN STRING COMMA exp COMMA exp RPAREN
   { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), $3, $5, $7) }
 | PRIM LPAREN STRING COMMA exp RPAREN
   { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), $3, $5) }
 | BANG exp
   { Op1(Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "!", $2) }
 | exp PLUS exp
   { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), "+", $1, $3) }
 | exp MINUS exp
   { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), "-", $1, $3) }
 | exp MULT exp
   { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), "*", $1, $3) }
 | exp DIV exp
   { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), "/", $1, $3) }
 | MINUS exp %prec UMINUS
   { Op1 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "-", $2) }
 | exp EQEQUALS exp
     { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), "stx=", $1, $3) }
 | exp BANGEQUALS exp
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         Op1(p, "!", Op2 (p, "stx=", $1, $3)) }
 | exp EQEQEQUALS exp
     { Op2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), "sameValue", $1, $3) }
 | exp BANGEQEQUALS exp
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         Op1(p, "!", Op2 (p, "sameValue", $1, $3)) }
 | exp LBRACK DELETE exp RBRACK
     { DeleteField (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), $1, $4) }
 | exp LBRACK exp LT attr_name GT RBRACK
     { GetAttr (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $5, $1, $3) }
 | exp LBRACK exp LT attr_name GT EQUALS exp RBRACK
     { SetAttr (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 9), $5, $1, $3, $8) }
 | exp LBRACK LT oattr_name GT RBRACK
     { GetObjAttr(Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6),
                  $4, $1) }
 | exp LBRACK LT oattr_name GT EQUALS exp RBRACK
     { SetObjAttr(Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8),
                  $4, $1, $7) }
 | exp LBRACK LT ID GT RBRACK
     { GetInternal(Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6),
                  $4, $1) }
 | exp LBRACK LT ID GT EQUALS exp RBRACK
     { SetInternal(Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8),
                  $4, $1, $7) } 
 | exp AMPAMP exp
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         If (p, $1, $3, False(p)) }
 | exp PIPEPIPE exp
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         If (p, $1, True(p), $3) }
 | LPAREN HINT exp RPAREN
     { Hint (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $2, $3) }
 | LABEL ID COLON exp %prec THROW
     { Label (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $2, $4) } 
 | BREAK ID exp %prec THROW
   { Break (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $2, $3) }
 | THROW exp
   { Throw (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), $2) }
 | TRY exp CATCH exp
   { TryCatch (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $2, $4) }
 | TRY exp FINALLY exp
   { TryFinally (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $2, $4) }
 | LET LPAREN ID EQUALS exp RPAREN exp %prec LET
   { Let (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | REC LPAREN ID EQUALS func RPAREN exp %prec LET
   { Rec (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | exp SEMI exp { Seq (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $1, $3) }

braced_seq_exp :
 | LBRACE exp RBRACE { with_pos $2 (Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3)) }

env :
 | EOF
     { fun x -> x }
 | LET LBRACK ID RBRACK EQUALS exp env
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7) in
         fun x -> 
           Let (p, $3, $6, $7 x) }
 | REC LBRACK ID RBRACK EQUALS exp env
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7) in
         fun x -> 
           Rec (p, $3, $6, $7 x) }
 | braced_seq_exp env
     { let p = Pos.real (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2) in
         fun x -> Seq (p, $1, $2 x) }

prog :
 | exp EOF { $1 }
%%
