(*
These lines are just place holders for automated testing
*)
val dir_inname = "../../testcases/syntax-and-sem-analysis/"
val dir_outname = "./outputs/"

signature PARSE =
sig
  val parse: string -> string -> unit
  val parse': string -> unit
  val parseall: string -> unit
end

functor ParseFun(structure Symbol: SYMBOL) : PARSE=
struct 

  structure Absyn = AbsynFun(structure Symbol = Symbol)
  structure TigerLrVals = TigerLrValsFun(
                             structure Token = LrParser.Token
                             structure A = Absyn
                             structure Symbol = Symbol)
  structure Lex = TigerLexFun(structure Tokens = TigerLrVals.Tokens)
  structure TigerP = Join(structure ParserData = TigerLrVals.ParserData
			structure Lex=Lex
			structure LrParser = LrParser)
  structure Env = EnvFun(structure Symbol = Symbol)
  structure TigerSem = SemantFun(structure A = Absyn
                                 structure E = Env
                                 structure Symbol = Symbol)
  structure PrintAbsyn = PrintAbsynFun(structure A = Absyn
                                       structure Symbol = Symbol)
  structure PrintType = PrintTypeFun(structure E= Env
                                     structure Symbol = Symbol)

  fun parse infilename outfilename =
      let 
        val _ = (ErrorMsg.reset(); ErrorMsg.fileName := infilename)
	val infile = TextIO.openIn infilename
	fun get _ = TextIO.input infile
	fun parseerror(s,p1,p2) = ErrorMsg.error p1 s
	val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	val (absyn, _) = TigerP.parse(30,lexer,parseerror,())
        val ty = (TigerSem.transProg absyn)
        val outfile = TextIO.openOut outfilename
      in
        TextIO.closeIn infile;
	PrintAbsyn.print (outfile,absyn);
	TextIO.closeOut outfile;
	
        (PrintType.print ty)
      end handle LrParser.ParseError => print ("Unable to handle ParseError\n")

  fun parse' infilename =
      let 
        val _ = (ErrorMsg.reset(); ErrorMsg.fileName := infilename)
	val infile = TextIO.openIn infilename
	fun get _ = TextIO.input infile
	fun parseerror(s,p1,p2) = ErrorMsg.error p1 s
	val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	val (absyn, _) = TigerP.parse(30,lexer,parseerror,())
        val ty = (TigerSem.transProg absyn)
      in
        TextIO.closeIn infile;
        (PrintType.print ty)
      end handle LrParser.ParseError => print ("Unable to handle ParseError\n")

   exception FileError;

  fun parseall filename =
    let val infile = TextIO.openIn filename
        fun process_file(infile) =
          let val current_file = TextIO.inputLine(infile)
              val current_filename = case current_file of
                                        NONE => (print ("error reading" ^ filename); raise FileError) |
                                        SOME str1 => str1;
              val current_size = String.size(current_filename);
              val current_size = current_size - 1;
              val current_filename = String.substring(current_filename,0,current_size);
              val full_inname = dir_inname ^ current_filename
              val full_outname = dir_outname ^ current_filename
              val full_outname = full_outname ^ ".out";
              val temp = (print ("Parsing... " ^ current_filename ^ ".....\n" );parse full_inname full_outname)
          in
            if(TextIO.endOfStream(infile))
              then
                ()
              else
                process_file(infile)
          end
    in
      if(TextIO.endOfStream(infile))
        then
          (print (filename ^ "is empty"))
        else
          process_file(infile)
    end
end

structure Parse = ParseFun(structure Symbol = Symbol)
