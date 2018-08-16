type token =
  | NUM of (int)
  | STR of (string)
  | ID of (string)
  | INT
  | IF
  | WHILE
  | SPRINT
  | IPRINT
  | SCAN
  | EQ
  | NEQ
  | GT
  | LT
  | GE
  | LE
  | ELSE
  | RETURN
  | NEW
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | RESIDUE
  | POW
  | LB
  | RB
  | LS
  | RS
  | LP
  | RP
  | ASSIGN
  | SEMI
  | COMMA
  | TYPE
  | VOID

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 46 "parser.ml"
let yytransl_const = [|
  260 (* INT *);
  261 (* IF *);
  262 (* WHILE *);
  263 (* SPRINT *);
  264 (* IPRINT *);
  265 (* SCAN *);
  266 (* EQ *);
  267 (* NEQ *);
  268 (* GT *);
  269 (* LT *);
  270 (* GE *);
  271 (* LE *);
  272 (* ELSE *);
  273 (* RETURN *);
  274 (* NEW *);
  275 (* PLUS *);
  276 (* MINUS *);
  277 (* TIMES *);
  278 (* DIV *);
  279 (* RESIDUE *);
  280 (* POW *);
  281 (* LB *);
  282 (* RB *);
  283 (* LS *);
  284 (* RS *);
  285 (* LP *);
  286 (* RP *);
  287 (* ASSIGN *);
  288 (* SEMI *);
  289 (* COMMA *);
  290 (* TYPE *);
  291 (* VOID *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* STR *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\005\000\005\000\
\005\000\005\000\006\000\006\000\007\000\007\000\009\000\009\000\
\010\000\010\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\013\000\
\013\000\014\000\014\000\008\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\012\000\012\000\012\000\012\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\006\000\006\000\003\000\001\000\000\000\001\000\004\000\002\000\
\002\000\001\000\004\000\007\000\005\000\007\000\005\000\005\000\
\005\000\005\000\005\000\005\000\003\000\001\000\001\000\000\000\
\001\000\003\000\001\000\004\000\001\000\001\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\002\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\031\000\055\000\001\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\037\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\047\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\029\000\000\000\000\000\000\000\000\000\
\000\000\018\000\000\000\005\000\000\000\000\000\000\000\000\000\
\019\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\048\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\036\000\017\000\000\000\028\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\023\000\
\024\000\025\000\026\000\040\000\039\000\027\000\000\000\000\000\
\000\000\000\000\007\000\000\000\000\000\000\000\003\000\004\000\
\000\000\000\000\000\000\000\000\000\000\011\000\020\000\022\000\
\008\000\016\000\000\000\000\000\000\000\010\000\000\000\009\000\
\015\000"

let yydgoto = "\002\000\
\013\000\014\000\122\000\030\000\060\000\091\000\123\000\015\000\
\124\000\061\000\032\000\037\000\033\000\034\000"

let yysindex = "\010\000\
\106\255\000\000\241\254\242\254\255\254\049\255\059\255\065\255\
\018\255\068\255\000\000\000\000\000\000\000\000\000\000\018\255\
\018\255\018\255\018\255\018\255\098\255\018\255\096\255\000\000\
\062\255\018\255\018\255\037\255\102\255\000\255\029\000\043\255\
\071\255\073\255\097\255\050\000\077\255\092\255\095\255\056\000\
\100\255\018\255\018\255\000\000\068\000\018\255\018\255\018\255\
\018\255\018\255\018\255\000\000\109\255\241\254\081\255\123\255\
\124\255\000\000\125\255\000\000\078\255\116\255\108\255\018\255\
\000\000\018\255\018\255\018\255\018\255\018\255\018\255\106\255\
\106\255\117\255\119\255\121\255\080\000\118\255\000\000\019\255\
\019\255\138\255\138\255\138\255\138\255\131\255\163\255\139\255\
\142\255\143\255\004\255\000\000\000\000\018\255\000\000\043\255\
\043\255\043\255\043\255\043\255\043\255\043\255\157\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\147\255\045\255\
\045\255\045\255\000\000\174\255\235\255\106\255\000\000\000\000\
\154\255\184\255\158\255\161\255\165\255\000\000\000\000\000\000\
\000\000\000\000\171\255\045\255\171\255\000\000\196\255\000\000\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\167\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\122\255\000\000\000\000\000\000\000\000\000\000\000\000\046\255\
\000\000\180\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\167\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\198\255\007\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\
\026\000\146\255\170\255\194\255\218\255\000\000\000\000\000\000\
\000\000\060\255\000\000\000\000\000\000\000\000\000\000\047\255\
\181\255\182\255\188\255\189\255\190\255\191\255\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\193\255\193\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\195\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\228\255\226\255\000\000\000\000\000\000\120\000\152\255\
\000\000\000\000\004\000\215\000\193\000\000\000"

let yytablesize = 364
let yytable = "\059\000\
\021\000\058\000\054\000\055\000\004\000\005\000\006\000\007\000\
\008\000\002\000\001\000\016\000\028\000\017\000\019\000\018\000\
\009\000\010\000\024\000\031\000\025\000\035\000\036\000\036\000\
\011\000\040\000\134\000\020\000\136\000\044\000\045\000\012\000\
\093\000\056\000\057\000\115\000\116\000\026\000\002\000\048\000\
\049\000\050\000\051\000\103\000\104\000\077\000\027\000\120\000\
\055\000\080\000\081\000\082\000\083\000\084\000\085\000\046\000\
\047\000\048\000\049\000\050\000\051\000\046\000\047\000\048\000\
\049\000\050\000\051\000\096\000\052\000\097\000\098\000\099\000\
\100\000\101\000\102\000\035\000\034\000\021\000\035\000\034\000\
\003\000\121\000\004\000\005\000\006\000\007\000\008\000\022\000\
\042\000\128\000\043\000\012\000\012\000\023\000\009\000\010\000\
\029\000\117\000\041\000\039\000\063\000\135\000\011\000\092\000\
\053\000\064\000\072\000\087\000\003\000\012\000\004\000\005\000\
\006\000\007\000\008\000\046\000\047\000\048\000\049\000\050\000\
\051\000\073\000\009\000\010\000\074\000\088\000\089\000\090\000\
\065\000\076\000\011\000\038\000\038\000\038\000\038\000\038\000\
\038\000\012\000\086\000\095\000\038\000\038\000\038\000\038\000\
\038\000\038\000\094\000\109\000\105\000\038\000\106\000\038\000\
\107\000\038\000\038\000\043\000\043\000\043\000\043\000\043\000\
\043\000\051\000\110\000\111\000\043\000\043\000\043\000\043\000\
\043\000\112\000\113\000\114\000\118\000\043\000\119\000\043\000\
\126\000\043\000\043\000\044\000\044\000\044\000\044\000\044\000\
\044\000\129\000\130\000\131\000\044\000\044\000\044\000\044\000\
\044\000\132\000\133\000\011\000\032\000\044\000\137\000\044\000\
\004\000\044\000\044\000\045\000\045\000\045\000\045\000\045\000\
\045\000\033\000\049\000\050\000\045\000\045\000\045\000\045\000\
\045\000\051\000\052\000\053\000\054\000\045\000\013\000\045\000\
\014\000\045\000\045\000\046\000\046\000\046\000\046\000\046\000\
\046\000\125\000\038\000\078\000\046\000\046\000\046\000\046\000\
\046\000\000\000\000\000\000\000\000\000\046\000\000\000\046\000\
\000\000\046\000\046\000\000\000\000\000\046\000\047\000\048\000\
\049\000\050\000\051\000\021\000\000\000\021\000\021\000\021\000\
\021\000\021\000\127\000\041\000\041\000\041\000\041\000\041\000\
\041\000\021\000\021\000\000\000\041\000\041\000\000\000\000\000\
\000\000\021\000\021\000\000\000\000\000\041\000\000\000\041\000\
\021\000\041\000\041\000\042\000\042\000\042\000\042\000\042\000\
\042\000\000\000\000\000\000\000\042\000\042\000\000\000\046\000\
\047\000\048\000\049\000\050\000\051\000\042\000\000\000\042\000\
\062\000\042\000\042\000\066\000\067\000\068\000\069\000\070\000\
\071\000\000\000\000\000\000\000\046\000\047\000\048\000\049\000\
\050\000\051\000\046\000\047\000\048\000\049\000\050\000\051\000\
\000\000\000\000\000\000\000\000\000\000\075\000\046\000\047\000\
\048\000\049\000\050\000\051\000\000\000\000\000\000\000\000\000\
\000\000\079\000\046\000\047\000\048\000\049\000\050\000\051\000\
\000\000\000\000\000\000\108\000"

let yycheck = "\030\000\
\000\000\030\000\003\001\004\001\005\001\006\001\007\001\008\001\
\009\001\003\001\001\000\027\001\009\000\029\001\029\001\031\001\
\017\001\018\001\001\001\016\000\003\001\018\000\019\000\020\000\
\025\001\022\000\131\000\029\001\133\000\026\000\027\000\032\001\
\061\000\034\001\035\001\032\001\033\001\020\001\032\001\021\001\
\022\001\023\001\024\001\072\000\073\000\042\000\029\001\003\001\
\004\001\046\000\047\000\048\000\049\000\050\000\051\000\019\001\
\020\001\021\001\022\001\023\001\024\001\019\001\020\001\021\001\
\022\001\023\001\024\001\064\000\032\001\066\000\067\000\068\000\
\069\000\070\000\071\000\030\001\030\001\029\001\033\001\033\001\
\003\001\112\000\005\001\006\001\007\001\008\001\009\001\029\001\
\027\001\118\000\029\001\032\001\033\001\029\001\017\001\018\001\
\029\001\094\000\003\001\002\001\030\001\132\000\025\001\026\001\
\003\001\033\001\030\001\027\001\003\001\032\001\005\001\006\001\
\007\001\008\001\009\001\019\001\020\001\021\001\022\001\023\001\
\024\001\030\001\017\001\018\001\030\001\003\001\003\001\003\001\
\032\001\030\001\025\001\010\001\011\001\012\001\013\001\014\001\
\015\001\032\001\030\001\032\001\019\001\020\001\021\001\022\001\
\023\001\024\001\031\001\030\001\032\001\028\001\032\001\030\001\
\032\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\024\001\032\001\001\001\019\001\020\001\021\001\022\001\
\023\001\031\001\029\001\029\001\016\001\028\001\028\001\030\001\
\003\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\032\001\003\001\030\001\019\001\020\001\021\001\022\001\
\023\001\033\001\030\001\025\001\030\001\028\001\003\001\030\001\
\003\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\030\001\030\001\030\001\019\001\020\001\021\001\022\001\
\023\001\030\001\030\001\030\001\030\001\028\001\030\001\030\001\
\030\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\114\000\020\000\043\000\019\001\020\001\021\001\022\001\
\023\001\255\255\255\255\255\255\255\255\028\001\255\255\030\001\
\255\255\032\001\033\001\255\255\255\255\019\001\020\001\021\001\
\022\001\023\001\024\001\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\032\001\010\001\011\001\012\001\013\001\014\001\
\015\001\017\001\018\001\255\255\019\001\020\001\255\255\255\255\
\255\255\025\001\026\001\255\255\255\255\028\001\255\255\030\001\
\032\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\255\255\255\255\255\255\019\001\020\001\255\255\019\001\
\020\001\021\001\022\001\023\001\024\001\028\001\255\255\030\001\
\028\001\032\001\033\001\010\001\011\001\012\001\013\001\014\001\
\015\001\255\255\255\255\255\255\019\001\020\001\021\001\022\001\
\023\001\024\001\019\001\020\001\021\001\022\001\023\001\024\001\
\255\255\255\255\255\255\255\255\255\255\030\001\019\001\020\001\
\021\001\022\001\023\001\024\001\255\255\255\255\255\255\255\255\
\255\255\030\001\019\001\020\001\021\001\022\001\023\001\024\001\
\255\255\255\255\255\255\028\001"

let yynames_const = "\
  INT\000\
  IF\000\
  WHILE\000\
  SPRINT\000\
  IPRINT\000\
  SCAN\000\
  EQ\000\
  NEQ\000\
  GT\000\
  LT\000\
  GE\000\
  LE\000\
  ELSE\000\
  RETURN\000\
  NEW\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  RESIDUE\000\
  POW\000\
  LB\000\
  RB\000\
  LS\000\
  RS\000\
  LP\000\
  RP\000\
  ASSIGN\000\
  SEMI\000\
  COMMA\000\
  TYPE\000\
  VOID\000\
  "

let yynames_block = "\
  NUM\000\
  STR\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 27 "parser.mly"
             (  _1  )
# 319 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
           ( IntTyp )
# 325 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 31 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 332 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 32 "parser.mly"
               ( NameTyp _1 )
# 339 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 35 "parser.mly"
                ( _1@_2 )
# 347 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                ( [] )
# 353 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 39 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x)) _2 )
# 361 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 41 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 369 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 379 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 43 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 388 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( _1@[_3] )
# 396 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 47 "parser.mly"
                       ( [_1]  )
# 403 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                        ( [] )
# 409 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 51 "parser.mly"
                        ( _1 )
# 416 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( _1@[(_3,_4)] )
# 425 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 55 "parser.mly"
                             ( [(_1,_2)] )
# 433 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( _1@[_2] )
# 441 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 59 "parser.mly"
                   ( [_1] )
# 448 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                              ( Assign (Var _1, _3) )
# 456 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 465 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 65 "parser.mly"
                              ( If (_3, _5, None) )
# 473 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 482 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 68 "parser.mly"
                              ( While (_3, _5) )
# 490 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 497 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 504 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 511 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 72 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 518 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 73 "parser.mly"
                                ( CallProc (_1, _3) )
# 526 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 74 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 533 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 75 "parser.mly"
             ( _1 )
# 540 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
            ( NilStmt )
# 546 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
                           ( [] )
# 552 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 80 "parser.mly"
                           ( _1 )
# 559 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                          ( _1@[_3] )
# 567 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                           ( [_1] )
# 574 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 87 "parser.mly"
                         ( Block (_2, _3) )
# 582 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 90 "parser.mly"
           ( IntExp _1  )
# 589 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 91 "parser.mly"
          ( VarExp (Var _1) )
# 596 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 92 "parser.mly"
                          ( CallFunc (_1, _3) )
# 604 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                      ( VarExp (IndexedVar (Var _1, _3)) )
# 612 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                      ( CallFunc ("+", [_1; _3]) )
# 620 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                       ( CallFunc ("-", [_1; _3]) )
# 628 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                       ( CallFunc ("*", [_1; _3]) )
# 636 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                     ( CallFunc ("/", [_1; _3]) )
# 644 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                         ( CallFunc ("%", [_1; _3]) )
# 652 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                     ( CallFunc ("^", [_1; _3]) )
# 660 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
                               ( CallFunc("!", [_2]) )
# 667 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                   ( _2 )
# 674 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 682 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 690 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 698 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 706 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 714 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 722 "parser.ml"
               : 'cond))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.stmt)
;;
