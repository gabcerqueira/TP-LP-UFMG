(* Plc Lexer *)

(* User declarations *)

open Tokens
type pos = int
type slvalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (slvalue, pos)token



fun keyword (s, l, r) = 
	case s of 

    "end"       => END (l,r)

    | "fn"      => FN (l,r)
    | "fun"     => FUN (l,r)
    | "rec"     => REC (l,r)

    | "if"      => IF (l,r)
    | "then"    => THEN (l,r)
    | "else"    => ELSE (l,r)
    | "match"   => MATCH (l,r)
    | "with"    => WITH (l,r)
    | "hd"      => HD (l,r)
    | "tl"      => TL (l,r)
    | "ise"     => ISE (l,r)
    
    | "true"    => CBOOL (true, l, r)
    | "false"   => CBOOL (false, l, r)

    | "Nil"     => NIL (l,r)
    | "Int"     => INT (l, r)
    | "Bool"    => BOOL (l, r)

    | "var"     => VAR (l, r)
    | _         => NAME (s, l, r)

(* A function to print a message error on the screen. *)
val error = fn x => TextIO.output(TextIO.stdOut, x ^ "\n")
val lineNumber = ref 0

(* Get the current line being read. *)
fun getLineAsString() =
    let
        val lineNum = !lineNumber
    in
        Int.toString lineNum
    end

(* Define what to do when the end of the file is reached. *)
fun eof () = Tokens.EOF(0,0)

fun strToInt s =
	case Int.fromString s of
		SOME i => i
	  | NONE => raise Fail ("Could not convert string '" ^ s ^ "' to integer")

(* Initialize the lexer. *)
fun init() = ()
%%
%header (functor PlcLexerFun(structure Tokens: PlcParser_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
whitespace=[\ \t];
identifier=[a-zA-Z_][a-zA-Z_0-9]*;
%%
\n              => (lineNumber := !lineNumber + 1; lex());
{whitespace}+   => (lex());
{digit}+        => (CINT (strToInt(yytext),yypos, yypos));
"!"       => (NEG (yypos, yypos));
"&&"      => (CONJ (yypos, yypos));
"("       => (LPAR (yypos, yypos));
")"       => (RPAR (yypos, yypos));
"["       => (LCOLCH (yypos, yypos));
"]"       => (RCOLCH (yypos, yypos));
"{"       => (LCHAV (yypos, yypos));
"}"       => (RCHAV (yypos, yypos));
":"       => (COLON (yypos, yypos));
","       => (COMMA (yypos, yypos));
";"       => (SEMIC (yypos, yypos));
"|"       => (BAR (yypos, yypos));
"_"       => (UNDERL (yypos, yypos));
"->"      => (AROW (yypos, yypos));
"=>"      => (ARROW (yypos, yypos));
"+"       => (PLUS (yypos, yypos));
"-"       => (MINUS (yypos, yypos));
"*"       => (TIMES (yypos, yypos));
"/"       => (DIV (yypos, yypos));
"="       => (EQ (yypos, yypos));
"!="      => (DIFF (yypos, yypos));
"<"       => (LT (yypos, yypos));
"<="      => (LTE (yypos, yypos));
"::"      => (CONCAT (yypos, yypos));
{identifier}    => (keyword (yytext, yypos, yypos));
. => (error("\n***Lexer error: bad character ***\n"); raise Fail("Lexer error: bad character "^yytext));
