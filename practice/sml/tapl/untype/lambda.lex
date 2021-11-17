(* -*- mode: smllex -*- *)
structure Tokens = Tokens
type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) Tokens.token

val pos = ref 0

fun error x = print x
fun eof () = Tokens.EOF (!pos,!pos)

%%
%header (functor LambdaLexFun(structure Tokens: Lambda_TOKENS));

digit = [0-9];
ws = [\ \t\n];

%%

{ws}+ => (lex());
"\." => (Tokens.ABS(!pos, !pos));
"("  => (Tokens.LPAREN(!pos, !pos));
")"  => (Tokens.RPAREN(!pos, !pos));
{digit}+ => (Tokens.ID ((foldl (fn(a, r)=> (ord(a)-ord(#"0")) + 10*r) 0 (explode yytext)), !pos, !pos));
