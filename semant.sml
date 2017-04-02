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

fun lookup_env tenv n pos =
  let val res = Symbol.look (tenv, n)
  in
  (
    case res of
      SOME ans => ans
    | NONE =>
      (
        error pos ("Not in scope: " ^ Symbol.name n);
        E.UNIT
      )
  )
  end

fun transExp venv tenv e =
  let fun texp (A.VarExp (v)) = tvar v

        | texp (A.NilExp) = E.NIL

        | texp (A.IntExp (i)) = E.INT

        | texp (A.StringExp (s, pos)) = E.STRING

        | texp (A.CallExp {func, args, pos}) =
          let
            val res = Symbol.look (venv, func)
          in
            case res of
              SOME (E.FunEntry {formals, result}) =>
              (
                if (length args = length formals)
                then
                  (
                    checkRecType(args, formals, pos);
                    result
                  )
                else
                  (
                    error pos ("Error args num: " ^ Symbol.name func);
                    result
                  )
              )
            | _ =>
              (
                error pos ("Func not found: " ^ Symbol.name func);
                E.UNIT
              )
          end

        | texp (A.OpExp {left, oper, right, pos}) = E.NIL

        | texp (A.RecordExp {fields, typ, pos}) = E.NIL

        | texp (A.SeqExp (explist)) = E.NIL

        | texp (A.AssignExp {var, exp, pos}) = E.NIL

        | texp (A.IfExp {test, then', else', pos}) = E.NIL

        | texp (A.WhileExp {test, body, pos}) = E.NIL

        | texp (A.ForExp {var, escape, lo, hi, body, pos}) = E.NIL

        | texp (A.BreakExp (pos)) = E.NIL

        | texp (A.LetExp {decs, body, pos}) = E.NIL

        | texp (A.ArrayExp {typ, size, init, pos}) = E.NIL

      and tvar (A.SimpleVar(id, pos)) = E.NIL

        | tvar (A.FieldVar (v, id, pos)) = E.NIL

        | tvar (A.SubscriptVar (v, e, pos)) = E.NIL
      (* helper function*)
      and checkRecType (a::a_tl, b::b_tl, pos) =
          let val a_ty = texp a
          in
            if (a_ty = b)
              then
                checkRecType (a_tl, b_tl, pos)
              else
                (
                  error pos ("Args type not match");
                  checkRecType (a_tl, b_tl, pos)
                )
          end
        | checkRecType (nil, _, pos) = ( )
        | checkRecType (_, nil, pos) = ( )
  in
    texp e
  end

fun transProg e =
  transExp E.base_venv E.base_tenv e
(* need to provided a definition of transProg that takes an abstract
   syntax representation whose type is exp and returns a type or prints
   an error. This function will use transExp transTy and transDec as
   discussed in the book and in class *)

end
