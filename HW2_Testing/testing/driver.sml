(* These lines are just place holders for automated testing *)
val dir_inname = "/web/classes/Spring-2017/csci5161/resources/hws/testcases/syntax-and-sem-analysis/"
val dir_outname = "/home/fac05/gopalan/test/testing/outputs/"

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

  exception FileError;
  
(* Useful in automated testing. The filename argument is expected to 
   be the name of a file containing the collection of test cases you 
   want to generate outputs for. *)
  fun parseall filename = 
    let val infile = TextIO.openIn filename
	fun process_file infile = 
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
	      val _ = (print ("Lexing ... " ^ current_filename ^ ".....\n" );
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

