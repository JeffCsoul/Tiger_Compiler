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

(* return UNIT if type for the target not found *)
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

(* NAME helper function*)
exception NullPointExeception
fun find_induc_type (E.NAME (s, tyref)) =
    (
      case !tyref of
        NONE => raise NullPointExeception
      | SOME t => find_induc_type t
    )
  | find_induc_type t = t

fun transExp venv tenv e =
  let fun texp (A.VarExp (v)) = tvar v

        | texp (A.NilExp) = E.NIL

        | texp (A.IntExp (i)) = E.INT

        | texp (A.StringExp (s, pos)) = E.STRING
        (* CallExp: result*)
        | texp (A.CallExp {func, args, pos}) =
          let
            val res = Symbol.look (venv, func)
          in
            case res of
              SOME (E.FunEntry {formals, result}) =>
              (
                (
                  if (length args = length formals)
                  then
                      checkRecType(args, formals, pos)
                  else
                      error pos ("Error args number: " ^ Symbol.name func)
                );
                result
              )
            | _ =>
              (
                error pos ("Func not found: " ^ Symbol.name func);
                E.UNIT
              )
          end
        (* OpExp: INT*)
        | texp (A.OpExp {left, oper, right, pos}) =
        (
          (* INT oper*)
          if (oper = A.PlusOp orelse
              oper = A.MinusOp orelse
              oper = A.TimesOp orelse
              oper = A.DivideOp)
            then
            (
              checkInt(left, pos);
              checkInt(right, pos);
              E.INT
            )
            (* BOOL oper*)
            else
            (
              let
                val leftty = texp left
              in
              (
                (if leftty = E.INT
                  then
                    (
                      checkInt(left, pos);
                      checkInt(right, pos)
                    )
                  else
                    if leftty = E.STRING
                      then
                      (
                        checkString(left, pos);
                        checkString(right, pos)
                      )
                      else
                        error pos "Type not match on comparison"
                )
              )
              end;
              E.INT
            )
        )
        (* RecordExp: inductive type and depends env*)
        | texp (A.RecordExp {fields, typ, pos}) =
          let val typ_r = lookup_env tenv typ pos
              val res = find_induc_type typ_r
              val f_id_list = map #1 fields
              val f_exp_res_list = map texp (map #2 fields)
              val f_pos_list = map #3 fields
          in
            case res of
              E.RECORD(d, u) =>
              (
                let
                  val dec_id_list = map #1 d
                  val dec_res_list = map find_induc_type (map #2 d)
                in
                  if f_id_list = dec_id_list andalso
                     f_exp_res_list = dec_res_list
                    then
                      ()
                    else
                      error pos ("Field types not match: " ^ Symbol.name typ)
                end;
                E.RECORD(d, u)
              )
            | _ =>
              (
                error pos ("Invalid record: " ^ Symbol.name typ);
                E.UNIT
              )
          end

        | texp (A.SeqExp (explist)) = parseSeq explist

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

      (* helper function for transExp*)
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
      and checkInt(i, pos) =
          let val n = texp i
          in
            if (n = E.INT)
              then
                ()
              else
              (
                error pos "Error: expected INT here";
                ()
              )
          end
      and checkString(s, pos) =
          let val n = texp s
          in
            if (n = E.STRING)
              then
                ()
              else
              (
                error pos "Error: expected STRING here";
                ()
              )
          end
      and parseSeq (s::nil) =
          texp (#1 s)
        | parseSeq (s::s_tl) =
          (
            texp (#1 s);
            parseSeq s_tl
          )
        | parseSeq nil = E.UNIT
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
