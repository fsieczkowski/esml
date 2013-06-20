
structure DTFunctors =
struct

  datatype ('tvar, 'typ) typF
    = TyArr  of 'typ * 'typ
    | TyProd of 'typ * 'typ
    | TyInt | TyBool
    | TyVar  of 'tvar

  datatype btinop = Add | Sub | Mul | Div | Mod | Neg | Eq | Lt | Gt
                  | LEq | GEq | Not | And | Or

  datatype ('var, 'arg, 'dec, 'term, 'ann) termF
    = Var of 'var * 'ann
    | Abs of 'arg * 'term * 'ann
    | App of 'term * 'term * 'ann
    | Pair of 'term * 'term * 'ann
    | Proj1 of 'term * 'ann
    | Proj2 of 'term * 'ann
    | IntLit of int * 'ann
    | BoolLit of bool * 'ann
    | Op of btinop * 'ann
    | Let of 'dec list * 'term * 'ann
    | If of 'term * 'term * 'term * 'ann
  datatype ('var, 'arg, 'tvar, 'typ, 'term, 'ann) decF
    = Fun of ('var * 'arg list * 'term * 'ann) list
    | PFun of ('var * 'tvar list * ('var * 'typ) list * 'typ * 'term * 'ann) list

  fun annE (Var (x, a)) = a
    | annE (Abs (arg, e, a)) = a
    | annE (App (e1, e2, a)) = a
    | annE (Pair (e1, e2, a)) = a
    | annE (Proj1 (e, a)) = a
    | annE (Proj2 (e, a)) = a
    | annE (IntLit (n, a)) = a
    | annE (BoolLit (b, a)) = a
    | annE (Op (bop, a)) = a
    | annE (Let (ds, e, a)) = a
    | annE (If (e1, e2, e3, a)) = a

  local fun parens s = "(" ^ s ^ ")"
  in

  fun ppty f g n (TyArr  (t1, t2)) =
      let val r = f 2 t1 ^ " -> " ^ f 1 t2
      in if n > 1 then parens r else r
      end
    | ppty f g n (TyProd (t1, t2)) =
      let val r = f 2 t1 ^ " * " ^ f 3 t2
      in if n > 2 then parens r else r
      end
    | ppty f g n TyInt  = "int"
    | ppty f g n TyBool = "bool"
    | ppty f g n (TyVar a) = g a

  end

end

structure PAst =
struct

  local open DTFunctors in

  datatype pTyp = PTyp of (string, pTyp) typF

  type var = string
  type pos = Pos.pos

  (* FIXME: once stuff typechecks, uncomment the optional typing of arguments *)
  datatype pTerm = PT of (var, var (* * pTyp option *), pDec, pTerm, pos) termF
                 | PHole of pos | PAnn of pTerm * pTyp * pos
       and pDec  = PD of (var, var (* * pTyp option *), string, pTyp, pTerm, pos) decF

  end

  fun annE (PT t) = DTFunctors.annE t
    | annE (PAnn (_, _, p)) = p
    | annE (PHole p) = p

end

structure CGAst =
struct

  local open DTFunctors in

  type var = string
  type pos = Pos.pos
  type tvar = int
  type tname = string

  datatype cgTyp = CTyUVar of int | CTyp of (tvar, cgTyp) typF
  datatype cgTyS = CSPoly of (tname * tvar) list * cgTyp | CSMono of cgTyp
  type cgContext  = (var * cgTyS) list
  type cgTContext = (tname * tvar) list

  datatype cgTerm = CTerm of (var, var * cgTyp, cgDec, cgTerm, pos * cgTyp) termF
                  | CHole of pos * cgTContext * cgContext * cgTyp
       and cgDec  = CDec  of (var, var * cgTyp, tname * tvar, cgTyp, cgTerm, pos * cgTyS) decF

  datatype constr = CEqc of cgTyp * cgTyp * pos

  fun ppuvar n = "?X" ^ Int.toString n
  fun ppty ty =
      let fun pptyvar n = "?V" ^ Int.toString n
          fun aux _ (CTyUVar n) = ppuvar n
            | aux n (CTyp t) = DTFunctors.ppty aux pptyvar n t
      in aux 1 ty
      end
  end

end

structure TAst =
struct

  local open DTFunctors in

  type tvar = int
  type tname = string
  type var = string
  type pos = Pos.pos

  datatype typ = TyF of (tvar, typ) typF | TyMono of tvar
  datatype tyS = SPoly of (tvar * tname) list * typ | SMono of typ
  type tycontext = (tvar * tname) list
  type context   = (var * tyS) list

  datatype hole = Open of tycontext * context * typ | Closed of term
       and term = TmF of (var, var * typ, dec, term, pos * typ) termF
                | THole of pos * hole ref
       and dec  = DF of (var, var * typ, tvar * tname, typ, term,  pos * tyS) decF

  fun annE (TmF t) = DTFunctors.annE t
    | annE (THole (p, hr)) = (case !hr of
                                  Open h => (p, #3 h)
                                | Closed t => annE t)

  fun ppty (D, ty) =
      let fun pptyvar n = (case Util.lookup (D, n) of
                               SOME s => s
                             | NONE => "?V" ^ Int.toString n)
          fun aux _ (TyMono n) = "_t" ^ Int.toString n
            | aux n (TyF t) = DTFunctors.ppty aux pptyvar n t
      in aux 1 ty
      end

  fun pptys (D, SMono t) = ppty (D, t)
    | pptys (D, SPoly (s, t)) =
      let val ctx = s @ D
          val tc = "[" ^ String.concatWith " " (map #2 s) ^ "] "
          fun pptyvar n = (case Util.lookup (ctx, n) of
                               SOME s => s
                             | NONE => "?V" ^ Int.toString n)
          fun aux _ (TyMono n) = "_t" ^ Int.toString n
            | aux n (TyF t) = DTFunctors.ppty aux pptyvar n t
      in tc ^ aux 1 t
      end

  end

end
