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
val loop_level = ref 0

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
        E.ERROR
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
                        error pos "Types cannot be compared"
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
                E.ERROR
              )
          end

        | texp (A.SeqExp (explist)) = parseSeq explist

        | texp (A.AssignExp {var, exp, pos}) =
          (
            let
              val id_type = tvar var
              val res_type = texp exp
            in
              if (id_type = res_type)
                then
                  ()
                else
                  error pos "Type not match in assignment"
            end;
            E.UNIT
          )
        | texp (A.IfExp {test, then', else', pos}) =
          (
            (
              case else' of
                NONE =>
                (
                  checkInt(test, pos);
                  checkUnit(then', pos)
                )
              | SOME s_else =>
                (
                  checkInt(test, pos);
                  checkUnit(then', pos);
                  checkUnit(s_else, pos)
                )
            );
            E.UNIT
          )

        | texp (A.WhileExp {test, body, pos}) =
          (
            loop_level := !loop_level + 1;
            checkInt(test, pos);
            checkUnit(body, pos);
            loop_level := !loop_level - 1;
            E.UNIT
          )

        | texp (A.ForExp {var, escape, lo, hi, body, pos}) =
          (
            loop_level := !loop_level + 1;
            checkInt(lo, pos);
            checkInt(hi, pos);
            checkUnit(body, pos);
            loop_level := !loop_level - 1;
            E.UNIT
          )
        | texp (A.BreakExp (pos)) =
          (
            (
              if (!loop_level > 0)
                then
                  ()
                else
                  error pos "Break cannot be placed out of loop"
            );
            E.UNIT
          )

        | texp (A.LetExp {decs, body, pos}) =
          (
            let val {venv=venv', tenv=tenv'} = transDecs(venv, tenv, decs)
            in
              transExp venv' tenv' body
            end
          )

        | texp (A.ArrayExp {typ, size, init, pos}) =
          (
            let
              val res = find_induc_type (lookup_env tenv typ pos)
              val init_res = texp init
            in
              (
                if (res = E.ERROR)
                then
                  E.ERROR
                else
                  if (res = init_res)
                  then
                    (
                      checkInt(size, pos);
                      E.ARRAY(res, ref ())
                    )
                  else
                    (
                      error pos ("initial error on array: " ^ Symbol.name typ);
                      E.ARRAY(res, ref ())
                    )
              )
            end
          )

      and tvar (A.SimpleVar(id, pos)) =
          (
            case Symbol.look(venv, id) of
              SOME (E.VarEntry{ty, ... }) =>
                find_induc_type ty
            | _ =>
              (
                error pos ("Unbound variable: " ^ Symbol.name id);
                E.ERROR
              )
          )

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
      and checkUnit(u, pos) =
          let val n = texp u
          in
            if (n = E.UNIT)
              then
                ()
              else
              (
                error pos "Error: expected UNIT here";
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

and transDec (venv, tenv, A.VarDec{name, typ, init, ...}) =
    let
      val init_ty = transExp venv tenv init
    in
      case typ of
        NONE =>
        {venv = Symbol.enter(venv,
                             name,
                             E.VarEntry{ty = init_ty, loopvar = false}),
         tenv = tenv                             
        }
      | SOME(id, pos) =>
        (
          let
            val res = Symbol.look (tenv, id)
          in
            case res of
              NONE =>
              (
                error pos ("Unbound type: " ^ Symbol.name id);
                {venv = Symbol.enter(venv,
                                     name,
                                     E.VarEntry{ty = init_ty, loopvar = false}
                                    ),
                 tenv = tenv
                }
                (* follow the init value's type*)
              )
            | SOME res_ty =>
              (
                if res_ty = init_ty
                then
                ()
                else
                error pos "type not match";
                {venv = Symbol.enter(venv,
                                     name,
                                     E.VarEntry{ty = res_ty, loopvar = false}),
                 tenv = tenv
                }
                (* follow the specified type *)
              )
          end
        )
    end
  | transDec (venv, tenv, _) => {venv = venv, tenv = tenv}

and transDecs (venv, tenv, decs) =
    (
      case decs of
        nil => {venv=venv, tenv=tenv}
      | (d::d_tl) =>
        let
          val {venv=venv', tenv=tenv'} = transDec(venv, tenv, d)
        in
          transDecs(venv', tenv', d_tl)
        end
    )
fun transProg e =
  transExp E.base_venv E.base_tenv e
(* need to provided a definition of transProg that takes an abstract
   syntax representation whose type is exp and returns a type or prints
   an error. This function will use transExp transTy and transDec as
   discussed in the book and in class *)

end
