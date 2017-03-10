(*
These lines are just place holders for automated testing
*)
val dir_inname = "../../testcases/syntax-and-sem-analysis/"
val dir_outname = "./outputs/"

structure Parse : sig val parse : string -> Absyn.exp 
                      val parseandprint: string -> string -> unit
		      val parseall: string->unit	
                  end =
struct 
  structure TigerLrVals = TigerLrValsFun(structure Token = LrParser.Token)
  structure Lex = TigerLexFun(structure Tokens = TigerLrVals.Tokens)
  structure TigerP = Join(structure ParserData = TigerLrVals.ParserData
			structure Lex=Lex
			structure LrParser = LrParser)
  fun parse filename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.fileName := filename)
	  val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  fun parseerror(s,p1,p2) = ErrorMsg.error p1 s
	  val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	  val (absyn, _) = TigerP.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
	   absyn
      end handle LrParser.ParseError => raise ErrorMsg.Error

  fun parseandprint infilename outfilename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.fileName := infilename)
	  val infile = TextIO.openIn infilename
	  fun get _ = TextIO.input infile
	  fun parseerror(s,p1,p2) = ErrorMsg.error p1 s
	  val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	  val (absyn, _) = TigerP.parse(30,lexer,parseerror,())
          val outfile = TextIO.openOut outfilename
       in TextIO.closeIn infile;
	   PrintAbsyn.print (outfile,absyn);
	   TextIO.closeOut outfile
      end handle LrParser.ParseError => (print "unable to handle error\n")

  exception FileError;

  fun parseall filename =
    let val infile = TextIO.openIn filename
        fun process_file(infile) =
          let val current_file = TextIO.inputLine(infile)
              val current_filename = 
                case current_file of
                   NONE => (print ("error reading" ^ filename); 
                            raise FileError) 
                 | SOME str1 => str1;
              val current_size = String.size(current_filename);
              val current_size = current_size - 1;
              val current_filename = 
                      String.substring(current_filename,0,current_size);
              val full_inname = dir_inname ^ current_filename
              val full_outname = dir_outname ^ current_filename
              val full_outname = full_outname ^ ".out";
              val _ = (print ("Parsing... " ^ current_filename ^ ".....\n" );
                       parseandprint full_inname full_outname)
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



