
structure DTFunctors =
struct

  datatype kind = KTyp | KArr of kind * kind
  datatype bdesc = Ctor | BVar

  datatype ('tvar, 'typ) typF
    = TyArr  of 'typ * 'typ
    | TyProd of 'typ * 'typ
    | TyApp  of 'typ * 'typ
    | TyInt | TyBool
    | TyVar  of 'tvar

  datatype btinop = Add | Sub | Mul | Div | Mod | Neg | Eq | Lt | Gt
                  | LEq | GEq | Not | And | Or

  datatype ('var, 'arg, 'alt, 'dec, 'term, 'ann) termF
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
    | Case of 'term * 'alt list * 'ann
  datatype ('var, 'arg, 'tvar, 'typ, 'term, 'eann, 'tann) decF
    = Fun of ('var * 'arg list * 'term * 'eann) list
    | PFun of ('var * 'tvar list * ('var * 'typ) list * 'typ * 'term * 'eann) list
    | Data of ('tvar * kind * ('var * 'tvar list * 'typ) list * 'tann) list
(*    | Type of ('tvar * 'typ * 'tann)*)

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
    | annE (Case (e, alts, a)) = a

  local fun parens s = "(" ^ s ^ ")"
  in

  fun ppknd k =
      let fun aux KTyp = "*"
            | aux (KArr (k1, k2)) = "(" ^ aux k1 ^ " -> " ^ ppknd k2 ^ ")"
      in case k of
             KTyp => "*"
           | KArr (k1, k2) => aux k1 ^ " -> " ^ ppknd k2
      end

  fun ppty f g n (TyArr  (t1, t2)) =
      let val r = f 2 t1 ^ " -> " ^ f 1 t2
      in if n > 1 then parens r else r
      end
    | ppty f g n (TyProd (t1, t2)) =
      let val r = f 2 t1 ^ " * " ^ f 2 t2
      in if n > 2 then parens r else r
      end
    | ppty f g n (TyApp  (t1, t2)) =
      let val r = f 3 t1 ^ " " ^ f 3 t2
      in if n > 3 then parens r else r
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

  type pPat = var * var list

  (* FIXME: once stuff typechecks, uncomment the optional typing of arguments *)
  datatype pTerm = PT of (var, var (* * pTyp option *), pAlt, pDec, pTerm, pos) termF
                 | PHole of pos | PAnn of pTerm * pTyp * pos
       and pDec  = PD of (var, var (* * pTyp option *), string, pTyp, pTerm, pos, pos) decF
                                                                                       
  withtype pAlt = pPat * pTerm


  end

  fun annE (PT t) = DTFunctors.annE t
    | annE (PAnn (_, _, p)) = p
    | annE (PHole p) = p

end

structure TAst =
struct

  local open DTFunctors in

  type tvar = int
  type tname = string
  type var = string
  type pos = Pos.pos

  datatype typ = TyF of (tvar, typ) typF | TyMono of tvar
  datatype tyS = SPoly of (tvar * (tname * kind)) list * typ | SMono of typ
  type tycontext = (tvar * (tname * kind)) list
  type context   = (var * (tyS * bdesc)) list
  type env       = tycontext * context

  type pattern  = var * (var * tyS) list

  datatype hole = Open of pos * env * (tycontext * context * typ) | Closed of term
       and term = TmF of (var, var * typ, alt, dec, term, pos * typ) termF
                | THole of hole ref
       and dec  = DF of (var, var * typ, tvar * (tname * kind), typ, term,  pos * tyS, pos * (var * tyS) list) decF
  withtype alt  = pattern * term

  fun extWith ((D, G), DF (Fun  ds)) = (D, foldl (fn (fd, G) => (#1 fd, (#2 (#4 fd), BVar)) :: G) G ds)
    | extWith ((D, G), DF (PFun ds)) = (D, foldl (fn (fd, G) => (#1 fd, (#2 (#6 fd), BVar)) :: G) G ds)
    | extWith (E,      DF (Data dt)) =
      let fun hData ((tvb, _, _, (_, cts)), (D, G)) =
              (tvb :: D, foldl (fn ((x, tS), G) => (x, (tS, Ctor)) :: G) G cts)
      in  foldl hData E dt
      end

  fun annE (TmF t) = DTFunctors.annE t
    | annE (THole hr) = (case !hr of
                             Open (pos, _, nty) => (pos, #3 nty)
                           | Closed t => annE t)

  fun ppty (D, ty) =
      let fun pptyvar n = (case Util.lookup (D, n) of
                               SOME (s, _) => s
                             | NONE => "?V" ^ Int.toString n)
          fun aux _ (TyMono n) = "_t" ^ Int.toString n
            | aux n (TyF t) = DTFunctors.ppty aux pptyvar n t
      in aux 1 ty
      end

  fun pptys (D, SMono t) = ppty (D, t)
    | pptys (D, SPoly (s, t)) =
      let val ctx = s @ D
          val tc = "[" ^ String.concatWith " " (map (#1 o #2) s) ^ "] "
          fun pptyvar n = (case Util.lookup (ctx, n) of
                               SOME (s, _) => s
                             | NONE => "?V" ^ Int.toString n)
          fun aux _ (TyMono n) = "_t" ^ Int.toString n
            | aux n (TyF t) = DTFunctors.ppty aux pptyvar n t
      in tc ^ aux 1 t
      end

  end

end

structure CGAst =
struct

  local open DTFunctors in

  type var = string
  type pos = Pos.pos
  type tvar = int
  type tname = string

  datatype cgTyp = CTyUVar of int | CTyp of (tvar, cgTyp) typF
  datatype cgTyS = CSPoly of (tname * (tvar * kind)) list * cgTyp | CSMono of cgTyp
  type cgContext  = (var * (cgTyS * bdesc)) list
  type cgTContext = (tname * (tvar * kind)) list
  type cgEnv      = cgTContext * cgContext

  type cgPat  = var * (var * cgTyS) list

  datatype cgTerm = CTerm of (var, var * cgTyp, cgAlt, cgDec, cgTerm, pos * cgTyp) termF
                  | CHole of pos * TAst.env * cgEnv * cgTyp
       and cgDec  = CDec  of (var, var * cgTyp, tname * (tvar * kind), cgTyp, cgTerm, pos * cgTyS, pos * (var * cgTyS) list) decF
  withtype cgAlt  = cgPat * cgTerm


  datatype constr = CEqc of cgTyp * cgTyp * pos

  fun ppuvar n = "?X" ^ Int.toString n
  fun ppty D ty =
      let fun pptyvar n = (case List.find (fn (_, (tv, _)) => n = tv) D of
                               SOME (s, _) => s
                             | NONE => "?V" ^ Int.toString n)
          fun aux _ (CTyUVar n) = ppuvar n
            | aux n (CTyp t) = DTFunctors.ppty aux pptyvar n t
      in aux 1 ty
      end
  end

  fun ppconstr (CEqc (t1, t2, pos)) = ppty [] t1 ^ " ~ " ^ ppty [] t2 ^ " @ " ^ Pos.toString pos ^ "\n"

end
