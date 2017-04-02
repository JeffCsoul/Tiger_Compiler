signature SEMANT =
sig
  type exp
  type transty
  val transProg: exp -> transty
end


functor SemantFun(structure A: ABSYN
                  structure E: ENV
                  structure Symbol: SYMBOL
                    sharing type A.symbol = E.symbol = Symbol.symbol
                        and type E.table = Symbol.table) : SEMANT
             where type transty = E.ty
               and type exp = A.exp =
struct

type  exp = A.exp
type  transty = E.ty
val error = ErrorMsg.error
fun transProg (e: A.exp) = E.NIL
(* need to provided a definition of transProg that takes an abstract
   syntax representation whose type is exp and returns a type or prints
   an error. This function will use transExp transTy and transDec as
   discussed in the book and in class *)

end
