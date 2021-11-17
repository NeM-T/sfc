(*Thanks to https://keens.github.io/blog/2015/01/31/mlyaccwotsukattemitehamattatokoro/*)
structure Print =
struct 
  fun Term_to_String t = case t of
                           Def.Var n => "Var " ^ Int.toString n
                         | Def.Abs n => "λ.(" ^ Term_to_String n ^ ")"
                         | Def.App (t1, t2) => 
                             "(" ^ (Term_to_String t1)  ^ ") @ (" ^ (Term_to_String t2) ^ ")"

  structure LambdaParserLrVals = 
    LambdaLrValsFun(structure Token = LrParser.Token)

  (* CalcLexFun は .lex.sml で定義されている *)
  structure LambdaLex = 
    LambdaLexFun(structure Tokens = LambdaParserLrVals.Tokens)

  structure LambdaParser = 
    Join(structure Lex = LambdaLex
         structure ParserData = LambdaParserLrVals.ParserData 
         structure LrParser = LrParser)

  fun invoke lexstream =
      let
          fun print_error (s, _, _) =
              TextIO.output(TextIO.stdOut, "Error: " ^ s ^ "\n")
      in
          LambdaParser.parse(0, lexstream, print_error, ())
      end

  fun parse filename =
      let
          val f = TextIO.openIn filename
          val lexer = LambdaParser.makeLexer
                          (fn i => TextIO.inputN(f, i))
          fun run lexer =
              let
                  val (result,lexer) = invoke lexer
              in
                  TextIO.output(TextIO.stdOut, "result = " ^ (Term_to_String result) ^ "\n")
              end
      in
          run lexer
      end

end
