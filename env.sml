signature ENV =
sig

  type unique = unit ref

  eqtype symbol

  type 'a table

  datatype ty = 
            RECORD of (symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	  | NAME of symbol * ty option ref
	  | UNIT
	  | ERROR


  datatype fnvar =
       VarEntry of {ty: ty, loopvar:bool}
     | FunEntry of {formals: ty list, result: ty}

  val base_tenv : ty table      (* predefined types *)

  val base_venv : fnvar table   (* predefined functions *)
end


functor EnvFun(structure Symbol : SYMBOL) : ENV =
struct

  type unique = unit ref

  type symbol = Symbol.symbol

  type 'a table = 'a Symbol.table

  datatype ty = 
            RECORD of (symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	  | NAME of symbol * ty option ref
	  | UNIT
	  | ERROR


  datatype fnvar =
       VarEntry of {ty: ty, loopvar: bool}
     | FunEntry of {formals: ty list, result: ty}

  
  (* predefined types *)
  val base_tenv : ty table = 
    (Symbol.enter 
           ((Symbol.enter (Symbol.empty,
                           (Symbol.symbol "string"),
                           STRING)),
            (Symbol.symbol "int"),
           INT))


  (* predefined functions; incomplete and should be completed using the
     list on page 519 *)
  val base_venv : fnvar table = 
         (Symbol.enter
           ((Symbol.enter 
              ((Symbol.enter 
                 ((Symbol.enter 
                    ((Symbol.enter 
                       ((Symbol.enter 
                          ((Symbol.enter
                             (Symbol.empty,
                              (Symbol.symbol "print"),
                              (FunEntry {formals=[STRING],result=UNIT}))),
                          (Symbol.symbol "flush"),
                          (FunEntry {formals=[],result=UNIT}))),
                       (Symbol.symbol "getchar"),
                       (FunEntry {formals=[],result=STRING}))),
                    (Symbol.symbol "ord"),
                    (FunEntry {formals=[STRING],result=INT}))),
                 (Symbol.symbol "chr"),
                 (FunEntry {formals=[INT],result=STRING}))),
              (Symbol.symbol "size"),
              (FunEntry {formals=[STRING],result=INT}))),
           (Symbol.symbol "substring"),
           (FunEntry {formals=[STRING,INT,INT],result=STRING})))

end

