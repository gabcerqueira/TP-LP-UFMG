(* Plc Lexer *)

(* User declarations *)

open Tokens
type pos = int
type slvalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (slvalue, pos)token

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


fun strToInt s =
    case Int.fromString s of
        SOME i => i
    |   NONE => raise Fail ("Could not convert string '" ^ s ^ "' to integer")


fun keyWord (s, lpos, rpos) =
    case s of 
        "var" => VAR (lpos, rpos)
        | "Bool" => TBOOL (lpos, rpos)
        | "else" => ELSE (lpos, rpos)
        | "end" => END (lpos, rpos)
        | "false" => FALSE (lpos, rpos)
        | "fn" => ANONFUN (lpos, rpos)
        | "fun" => FUN (lpos, rpos)
        | "hd" => HD (lpos, rpos)
        | "if" => IF (lpos, rpos)
        | "Int" => TINT (lpos, rpos)
        | "ise" => ISE (lpos, rpos)
        | "match" => MATCH (lpos, rpos)
        | "Nil" => TNIL (lpos, rpos)
        | "print" => PRINT (lpos, rpos)
        | "rec" => REC (lpos, rpos)
        | "then" => THEN (lpos, rpos)
        | "tl" => TL (lpos, rpos)
        | "true" => TRUE (lpos, rpos)
        | "with" => WITH (lpos, rpos)
        | "_" => UNDERSCORE (lpos, rpos)
        | _   => NAME (s, lpos, rpos)

(* Define what to do when the end of the file is reached. *)
fun eof () = Tokens.EOF(0,0)

(* Initialize the lexer. *)
fun init() = ()
%%
%header (functor PlcLexerFun(structure Tokens: PlcParser_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
whitespace=[\ \t];
identifier=[a-zA-Z_][a-zA-Z_0-9]*;
%s COMMENT;
startcomment=\(\*;
endcomment=\*\);
%%

\n => (lineNumber := !lineNumber + 1; lex());
<INITIAL>{whitespace}+ => (lex());
<INITIAL>{digit}+ => (CINT(strToInt(yytext), yypos, yypos));
<INITIAL>{identifier} => (keyWord(yytext, yypos, yypos));
<INITIAL>"+" => (PLUS(yypos, yypos));
<INITIAL>"-" => (MINUS(yypos, yypos));
<INITIAL>"*" => (MULTI(yypos, yypos));
<INITIAL>"/" => (DIV(yypos, yypos));
<INITIAL>"!" => (NOT(yypos, yypos));
<INITIAL>"=" => (EQ(yypos, yypos));
<INITIAL>"<" => (LESS(yypos, yypos));
<INITIAL>"<=" => (LESSEQ(yypos, yypos));
<INITIAL>"&&" => (AND(yypos, yypos));
<INITIAL>"!=" => (NOTEQ(yypos, yypos));
<INITIAL>"(" => (LPAR(yypos, yypos));
<INITIAL>")" => (RPAR(yypos, yypos));
<INITIAL>"{" => (LBRACKET(yypos, yypos));
<INITIAL>"}" => (RBRACKET(yypos, yypos));
<INITIAL>"[" => (LCOL(yypos, yypos));
<INITIAL>"]" => (RCOL(yypos, yypos));
<INITIAL>"|" => (PIPE(yypos, yypos));
<INITIAL>":" => (DPOINT(yypos, yypos));
<INITIAL>"::" => (DOUBLEPOINT(yypos, yypos));
<INITIAL>";" => (SEMIC(yypos, yypos));
<INITIAL>"," => (COMMA(yypos, yypos));
<INITIAL>"->" => (ARROW(yypos, yypos));
<INITIAL>"=>" => (FUNARROW(yypos, yypos));
<INITIAL>{startcomment} => (YYBEGIN COMMENT; lex());
<COMMENT>{endcomment} => (YYBEGIN INITIAL; lex());
<COMMENT>. => (lex());
<INITIAL>. => (error("\n***Lexer errorbad character ***\n");
    raise Fail("Lexer error: bad character " ^yytext));