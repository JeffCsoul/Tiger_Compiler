structure Parse =
struct 
  fun reinit () = 
      (ErrorMsg.lineNum := 1;
       ErrorMsg.linePos := [1];
       ErrorMsg.anyErrors := false
      )
  fun parse filename =
      let val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  val lexer = Mlex.makeLexer get
	  fun do_it() =
	      let val t = lexer()
	       in print t; print "\n";
		   if substring(t,0,3)="EOF" 
                   then (reinit()) 
                   else do_it()
	      end
      in ErrorMsg.fileName := filename;
	 do_it();
	 TextIO.closeIn file
      end

  fun parseandprint infilename outfilename =
      let val infile = TextIO.openIn infilename
          val outfile = TextIO.openOut outfilename
	  fun get _ = TextIO.input infile
	  val lexer = Mlex.makeLexer get
	  fun do_it() =
	      let val t = lexer()
	       in  TextIO.output (outfile,t); 
                   TextIO.output(outfile,"\n");
		   if substring(t,0,3)="EOF" 
                   then (reinit()) 
                   else do_it()
	      end
      in ErrorMsg.fileName := infilename;
	 do_it();
	 TextIO.closeIn infile;
         TextIO.closeOut outfile
      end
end

