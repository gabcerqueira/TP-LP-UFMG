%%

%name PlcParser

%pos int

%term VAR | NAME of string | EQ | FUN | REC | COLON
| IF | THEN | ELSE | MATCH | WITH | INV | HD | TL | ISE | NEG
| PRINT | CONJ | PLUS | MINUS | TIMES | DIV | DIFF | LT | LTE
| CONCAT | SEMIC | LCOLCH | RCOLCH | LPAR | RPAR | LCHAV | RCHAV
| FN | ARROW | END | CBOOL of bool | CINT of int | COMMA | BAR
| AROW | UNDERL | NIL | BOOL | INT | EOF

%nonterm Const of expr
| TypedVar of plcType * string
| Args of (plcType * string) list
| Params of (plcType * string) list
| AtomicType of plcType
| Type of plcType
| Types of plcType list
| Comps of expr list
| AtomicExpr of expr
| AppExpr of expr
| CondExpr of expr option
| MatchExpr of (expr option * expr) list
| Expr of expr
| Decl of expr
| Prog of expr

%right SEMIC AROW 
%nonassoc IF
%left ELSE 
%left CONJ 
%left EQ DIFF 
%left LT LTE 
%right CONCAT
%left PLUS MINUS 
%left TIMES DIV 
%nonassoc NEG HD TL ISE PRINT FUN
%left LCOLCH

%eop EOF

%noshift EOF

%start Prog

%%

Const : CINT (ConI(CINT))
| CBOOL (ConB(CBOOL))
| LPAR RPAR (List [])
| LPAR Type LCOLCH RCOLCH RPAR (ESeq (Type))

TypedVar : Type NAME ((Type,NAME))

Params : TypedVar (TypedVar::[])
 | TypedVar COMMA Params (TypedVar::Params)

Args : LPAR RPAR ([])
| LPAR Params RPAR (Params)

AtomicType : NIL (ListT [])
| INT (IntT)
| BOOL (BoolT)
| LPAR Type RPAR (Type)

Type : AtomicType (AtomicType)
| LPAR Types RPAR (ListT Types)
| LCOLCH Type RCOLCH (SeqT Type)
| Type AROW Type (FunT (Type1, Type2))

Types : Type COMMA Type (Type1::[Type2])
| Type COMMA Types (Type::Types)

Comps : Expr COMMA Expr (Expr1::[Expr2])
| Expr COMMA Comps (Expr::Comps)

AtomicExpr : Const (Const)
| NAME (Var(NAME))
| LCHAV Prog RCHAV (Prog)
| LPAR Expr RPAR (Expr)
| LPAR Comps RPAR (List Comps)
| FN Args ARROW Expr END (makeAnon(Args, Expr))

AppExpr : AtomicExpr AtomicExpr (Call (AtomicExpr1, AtomicExpr2))
| AppExpr AtomicExpr (Call (AppExpr, AtomicExpr))

CondExpr : UNDERL (NONE)
| Expr (SOME Expr)

MatchExpr : END ([])
| BAR CondExpr AROW Expr MatchExpr ((CondExpr, Expr) :: MatchExpr)

Expr : AtomicExpr (AtomicExpr)
| AppExpr (AppExpr)
| IF Expr THEN Expr ELSE Expr (If (Expr1, Expr2, Expr3))
| MATCH Expr WITH MatchExpr (Match (Expr, MatchExpr))
| NEG Expr (Prim1("!", Expr))
| MINUS Expr (Prim1("-", Expr))
| HD Expr (Prim1("hd", Expr))
| TL Expr (Prim1("tl", Expr))
| ISE Expr (Prim1("ise", Expr))
| PRINT Expr (Prim1("print", Expr))
| Expr CONJ Expr (Prim2("&&", Expr1, Expr2))
| Expr PLUS Expr (Prim2("+", Expr1, Expr2))
| Expr MINUS Expr (Prim2("-", Expr1, Expr2))
| Expr TIMES Expr (Prim2("*", Expr1, Expr2))
| Expr DIV Expr (Prim2("/", Expr1, Expr2))
| Expr EQ Expr (Prim2("=", Expr1, Expr2))
| Expr DIFF Expr (Prim2("!=", Expr1, Expr2))
| Expr LT Expr (Prim2("<", Expr1, Expr2))
| Expr LTE Expr (Prim2("<=", Expr1, Expr2))
| Expr CONCAT Expr (Prim2("::", Expr1, Expr2))
| Expr SEMIC Expr (Prim2(";", Expr1, Expr2))
| Expr LCOLCH CINT RCOLCH (Item (CINT, Expr))

Prog: Expr (Expr)
| Decl (Decl)

Decl : VAR NAME EQ Expr SEMIC Prog (Let(NAME, Expr, Prog))
| FUN NAME Args EQ Expr SEMIC Prog (Let(NAME, makeAnon(Args, Expr), Prog))
| FUN REC NAME Args COLON Type EQ Expr SEMIC Prog (makeFun(NAME, Args, Type, Expr, Prog))
