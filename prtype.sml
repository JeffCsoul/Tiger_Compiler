signature PRINTTYPE =
sig
  type ty

  val print: ty -> unit
end

functor PrintTypeFun(structure E: ENV
                     structure Symbol: SYMBOL
                       sharing type E.symbol = Symbol.symbol): PRINTTYPE =
struct
 
type ty = E.ty

fun print ty =
  let 
    fun say msg = (TextIO.print msg)
    fun sayln msg = (say msg; say "\n")

    fun indent 0 = ()
      | indent i = (say " "; indent (i - 1))
		    
    fun dolist n [] i k ls = ()
      | dolist n ((sy,ty) :: l) i k ls =
	((sayln ""); (indent n); 
         let 
           val label = (Symbol.name sy)
           val len = (String.size label)
           val i' = (i ^ "." ^ (Int.toString k))
         in ((say (label ^ ": ")); (print' ty (n+len+2) i' ls);
	     (dolist n l i (k+1) ls))
         end)

    and
        print' (E.RECORD(l,rd)) d i ls = 
           (case (List.find (fn (x,_) => (x = rd)) ls) of
              NONE => ((say ("record" ^ i ^ "{")); 
                       (dolist (d+4) l i 1 ((rd,i)::ls)); (say "}"))
	    | SOME(_,i) => (say ("record" ^ i)))
      | print' E.NIL _ _ _ = (say "NIL")
      | print' E.INT _ _ _ = (say "INT")
      | print' E.STRING _ _ _ = (say "STRING")
      | print' (E.ARRAY(ty,_)) d i ls = 
            ((say "array[INT] of "); (print' ty (d+14) i ls))
      | print' (E.NAME(sy,ref(SOME(ty)))) d i ls = 
          (print' ty d i ls)
      | print' E.UNIT _ _ _ = (say "UNIT")
      | print' E.ERROR _ _ _ = (say "ERROR")
  in 
    ((say "\n\nThe type of the program parsed:\n");
     (print' ty 0 "1" []);
     (say "\n\n"))

  end
  
end
