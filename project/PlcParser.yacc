%%

%name PlcParser

%pos int

%term SEMIC 
    | ARROW | FUNARROW
    | VAR | ANONFUN | FUN | REC | END
    | IF | THEN | ELSE
    | AND | PLUS | MINUS | MULTI | DIV 
    | EQ | NOTEQ | LESS | LESSEQ | DOUBLEPOINT
    | TNIL | TBOOL | TINT
    | NAME of string | CINT of int
    | EOF
    | MATCH | WITH | PIPE | UNDERSCORE
    | LPAR | RPAR | LCOL | RCOL | LBRACKET | RBRACKET
    | TRUE | FALSE
    | COMMA| DPOINT
    | NOT | HD | TL | ISE | PRINT
    

%nonterm Prog of expr
    | Decl of expr
    | Expr of expr
    | MatchExpr of (expr option * expr) list
    | CondExpr of expr option
    | Args of (plcType * string) list
    | Params of (plcType * string) list
    | TypedVar of plcType * string
    | Type of plcType
    | AtomType of plcType
    | Types of plcType list
    | AtomExpr of expr
    | AppExpr of expr
    | Const of expr
    | Comps of expr list
    

%right SEMIC ARROW 
%nonassoc IF
%left ELSE AND EQ
%left NOTEQ LESS LESSEQ
%right DOUBLEPOINT 
%left PLUS MINUS MULTI DIV
%nonassoc NOT HD TL ISE PRINT 
%left LCOL

%eop EOF

%noshift EOF

%start Prog

%%



AtomExpr : Const (Const)
    | NAME (Var NAME)
    | LBRACKET Prog RBRACKET (Prog)
    | LPAR Expr RPAR (Expr)
    | LPAR Comps RPAR (List(Comps))
    | ANONFUN Args FUNARROW Expr END (makeAnon(Args, Expr))

AppExpr : AtomExpr AtomExpr (Call(AtomExpr1, AtomExpr2))
    | AppExpr AtomExpr (Call(AppExpr, AtomExpr))

Const : TRUE (ConB true)
    | FALSE (ConB false)
    | CINT (ConI CINT)
    | LPAR RPAR (List [])
    | LPAR Type LCOL RCOL RPAR (ESeq(Type))

Comps : Expr COMMA Expr (Expr1::Expr2::[])
    | Expr COMMA Comps (Expr::Comps)

MatchExpr : END ([])
    | PIPE CondExpr ARROW Expr MatchExpr ((CondExpr, Expr)::MatchExpr)

CondExpr : Expr (SOME(Expr))
    | UNDERSCORE (NONE)

Args : LPAR RPAR ([])
    | LPAR Params RPAR (Params)

Expr : AtomExpr (AtomExpr)
    | AppExpr (AppExpr)
    | IF Expr THEN Expr ELSE Expr (If(Expr1, Expr2, Expr3))
    | MATCH Expr WITH MatchExpr (Match(Expr, MatchExpr))
    | NOT Expr (Prim1("!", Expr1))
    | MINUS Expr (Prim1("-", Expr1))
    | HD Expr (Prim1("hd", Expr1))
    | TL Expr (Prim1("tl", Expr1))
    | ISE Expr (Prim1("ise", Expr1))
    | PRINT Expr (Prim1("print", Expr1))
    | Expr AND Expr (Prim2("&&", Expr1, Expr2))
    | Expr PLUS Expr (Prim2("+", Expr1, Expr2))
    | Expr MINUS Expr (Prim2("-", Expr1, Expr2))
    | Expr MULTI Expr (Prim2("*", Expr1, Expr2))
    | Expr DIV Expr (Prim2("/", Expr1, Expr2))
    | Expr EQ Expr (Prim2("=", Expr1, Expr2))
    | Expr DOUBLEPOINT Expr (Prim2("::", Expr1, Expr2))
    | Expr SEMIC Expr (Prim2(";", Expr1, Expr2))
    | Expr LCOL CINT RCOL (Item(CINT, Expr))
    | Expr NOTEQ Expr (Prim2("!=", Expr1, Expr2))
    | Expr LESS Expr (Prim2("<", Expr1, Expr2))
    | Expr LESSEQ Expr (Prim2("<=", Expr1, Expr2))

Params : TypedVar (TypedVar::[])
    | TypedVar COMMA Params (TypedVar::Params)

TypedVar : Type NAME (Type, NAME)

Type : AtomType (AtomType)
    | LPAR Types RPAR (ListT(Types))
    | LCOL Type RCOL (SeqT(Type))
    | Type ARROW Type (FunT(Type1, Type2))

AtomType : TNIL (ListT [])
    | TBOOL (BoolT)
    | TINT (IntT)
    | LPAR Type RPAR (Type)

Types : Type COMMA Type (Type1::Type2::[])
    | Type COMMA Types (Type::Types)


Prog : Expr (Expr)
    | Decl (Decl)    

Decl : VAR NAME EQ Expr SEMIC Prog (Let(NAME, Expr, Prog))
    | FUN NAME Args EQ Expr SEMIC Prog (Let(NAME, makeAnon(Args, Expr), Prog))
    | FUN REC NAME Args DPOINT Type EQ Expr SEMIC Prog (makeFun(NAME, Args, Type, Expr, Prog))
