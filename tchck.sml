structure ConstrGen :
sig

    datatype 'ed err = VarUndef of CGAst.var * 'ed | TVarUndef of CGAst.tname * 'ed | Other of string * 'ed
    val genConstrExpr : TAst.env * PAst.pTerm -> CGAst.cgTerm * CGAst.constr list
    val genConstrDec  : TAst.env * PAst.pDec  -> CGAst.cgDec  * CGAst.constr list
    val genConstrFrom : TAst.env * CGAst.cgEnv * CGAst.cgTyp * PAst.pTerm ->
                        CGAst.cgTerm * CGAst.constr list
    val getErrors : unit -> PAst.pos err list
    val toString : CGAst.pos -> string
    val restart  : unit -> unit
    exception Fatal of PAst.pos err

end =
struct

  open DTFunctors
  open CGAst
  open PAst
  open Util

  exception NotFound

  val uvcntr = ref 0
  fun newUVar () = 
      let val n = !uvcntr
      in  CTyUVar n
          before uvcntr := n + 1
      end

  val tvcntr = ref 0
  fun newTVar () =
      let val n = !tvcntr
      in  n before tvcntr := n + 1
      end

  datatype 'ed err = VarUndef of var * 'ed | TVarUndef of tname * 'ed | Other of string * 'ed
  val errors = ref [] : pos err list ref

  exception Fatal of PAst.pos err

  fun tcop bop =
      let val arr  = CTyp o TyArr
          val prod = CTyp o TyProd
          val int  = CTyp TyInt
          val bool = CTyp TyBool
          val bi   = arr (prod (int, int), int)
          val bb   = arr (prod (bool, bool), bool)
          val rel  = arr (prod (int, int), bool)
      in case bop of
             Add => bi
           | Sub => bi
           | Mul => bi
           | Div => bi
           | Mod => bi
           | Neg => arr (int, int)
           | Eq  => rel
           | Lt  => rel
           | Gt  => rel
           | LEq => rel
           | GEq => rel
           | Not => arr (bool, bool)
           | And => bb
           | Or  => bb
      end

  fun kindSynth (D, pos, PTyp (TyArr  (t1, t2))) =
      let val t1' = kindCheck (D, pos, t1, KTyp)
          val t2' = kindCheck (D, pos, t2, KTyp)
      in (CTyp (TyArr  (t1', t2')), KTyp)
      end
    | kindSynth (D, pos, PTyp (TyProd (t1, t2))) =
      let val t1' = kindCheck (D, pos, t1, KTyp)
          val t2' = kindCheck (D, pos, t2, KTyp)
      in (CTyp (TyProd (t1', t2')), KTyp)
      end
    | kindSynth (D, pos, PTyp (TyApp  (t1, t2))) =
      let val (t1', kf) = kindSynth (D, pos, t1)
          val (t2', ka) = kindSynth (D, pos, t2)
          val errstr = "Kind mismatch: " ^ ppty D t1' ^ " : " ^ ppknd kf ^
                       " applied to " ^ ppty D t2' ^ " : " ^ ppknd ka ^ "."
      in case kf of
             KArr (karg, kres) => if karg = ka then (CTyp (TyApp (t1', t2')), KTyp)
                                  else raise Fatal (Other (errstr, pos))
           | _ => raise Fatal (Other (errstr, pos))
      end
    | kindSynth (D, pos, PTyp TyInt)  = (CTyp TyInt, KTyp)
    | kindSynth (D, pos, PTyp TyBool) = (CTyp TyBool, KTyp)
    | kindSynth (D, pos, PTyp (TyVar s)) =
      (case lookup (D, s) of
           SOME (n, k) => (CTyp (TyVar n), k)
         | NONE => (newUVar (), KTyp) before errors := TVarUndef (s, pos) :: !errors)

  and kindCheck (D, pos, pty, k) =
      let val (cty, k') = kindSynth (D, pos, pty)
      in  if k = k' then cty
          else raise Fatal (Other ("Kind mismatch in type '" ^ ppty D cty ^ "' : " ^ ppknd k' ^
                                   " does not match the expected " ^ ppknd k ^ ".", pos))
      end

  fun ctorCheck (D, pos, tv, CTyp (TyArr (_, t))) = ctorCheck (D, pos, tv, t)
    | ctorCheck (D, pos, tv, CTyp (TyApp (t, _))) = ctorCheck (D, pos, tv, t)
    | ctorCheck (D, pos, tv, CTyp (TyVar tv'))    =
      if tv = tv' then ()
      else raise Fatal (Other ("Couldn't match " ^ ppty D (CTyp (TyVar tv)) ^ " against " ^
                               ppty D (CTyp (TyVar tv')) ^ ".", pos))
    | ctorCheck (D, pos, tv, _) =  raise Fatal (Other ("Constructor does not end in a variable or type application", pos))

  fun instTy (targs, ty) =
      let val subst = map (fn (_, (tv, _)) => (tv, newUVar ())) targs
          fun aux (CTyp (TyArr  (t1, t2))) = (CTyp (TyArr  (aux t1, aux t2)))
            | aux (CTyp (TyProd (t1, t2))) = (CTyp (TyProd (aux t1, aux t2)))
            | aux (CTyp (TyApp  (t1, t2))) = (CTyp (TyApp  (aux t1, aux t2)))
            | aux (t as CTyp (TyVar tv)) = (case lookup (subst, tv) of
                                                SOME tu => tu
                                              | NONE => t)
            | aux t = t
      in  aux ty
      end

  fun instTyS (CSMono t)  = t
    | instTyS (CSPoly ts) = instTy ts

  fun bindArgs (pos, args, ty) =
      let fun nArr (CTyp (TyArr _)) = false
            | nArr _ = true
          fun aux ([], ty, acc) = if nArr ty then (ty, rev acc)
                                  else raise Fatal (Other ("Constructor not fully applied", pos))
            | aux (a :: args, CTyp (TyArr (t1, t2)), acc) = aux (args, t2, (a, CSMono t1) :: acc)
            | aux _ = raise Fatal (Other ("Constructor applied to too many arguments", pos))
      in aux (args, ty, [])
      end

  val toString = Pos.toString

  (* Environments for constraint generation *)
  type env = {lty : cgTContext, gty : TAst.tycontext, lvar : cgContext, gvar : TAst.context}

  fun mkEnv ((D, G), (DL, GL)) = {lty = DL, gty = D, lvar = GL, gvar = G}
  fun withLV (E : env, GL) = {lty = #lty E, gty = #gty E, lvar = GL,      gvar = #gvar E}
  fun withLT  (E : env, DL) = {lty = DL,     gty = #gty E, lvar = #lvar E, gvar = #gvar E}

  infix 1 withLV
  infix 1 withLT

  fun getTEnv (env : env) = #lty env @ map flip (#gty env)

  fun cgExpr (env, PT (Var (x, pos)), t, cs) =
      (case lookup (#lvar env, x) of
           SOME (tyS, _) => (CTerm (Var (x, (pos, t))), CEqc (getTEnv env, instTyS tyS, t, pos) :: cs)
         | NONE => (case lookup (#gvar env, x) of
                        SOME (ttS, _) => (CTerm (Var (x, (pos, t))), CEqc (getTEnv env, instTyS (TAst.trTySNM ttS), t, pos) :: cs)
                      | NONE => (errors := VarUndef (x, pos) :: !errors; (CTerm (Var (x, (pos, t))), cs))))
    | cgExpr (env, PT (Abs (x, e, pos)), t, cs) =
      let val (targ, tres) = (newUVar (), newUVar ())
          val (e', rcs) = cgExpr (env withLV (x, (CSMono targ, BVar)) :: #lvar env, e, tres, cs)
      in  (CTerm (Abs ((x, targ), e', (pos, t))), CEqc (getTEnv env, t, CTyp (TyArr (targ, tres)), pos) :: rcs)
      end
    | cgExpr (env, PT (App (e1, e2, pos)), t, cs) =
      let val targ = newUVar ()
          val (e1', cs') = cgExpr (env, e1, (CTyp (TyArr (targ, t))), cs)
          val (e2', rcs) = cgExpr (env, e2, targ, cs')
      in  (CTerm (App (e1', e2', (pos, t))), rcs)
      end
    | cgExpr (env, PT (Pair (e1, e2, pos)), t, cs) =
      let val (tl, tr) = (newUVar (), newUVar ())
          val (e1', cs') = cgExpr (env, e1, tl, cs)
          val (e2', rcs) = cgExpr (env, e2, tr, cs')
      in  (CTerm (Pair (e1', e2', (pos, t))), CEqc (getTEnv env, t, CTyp (TyProd (tl, tr)), pos) :: rcs)
      end
    | cgExpr (env, PT (Proj1 (e, pos)), t, cs) =
      let val tr = newUVar ()
          val (e', cs') = cgExpr (env, e, CTyp (TyProd (t, tr)), cs)
      in  (CTerm (Proj1 (e', (pos, t))), cs')
      end
    | cgExpr (env, PT (Proj2 (e, pos)), t, cs) =
      let val tl = newUVar ()
          val (e', cs') = cgExpr (env, e, CTyp (TyProd (tl, t)), cs)
      in  (CTerm (Proj1 (e', (pos, t))), cs')
      end
    | cgExpr (env, PT (IntLit (n, pos)), t, cs) =
      (CTerm (IntLit (n, (pos, t))), CEqc (getTEnv env, t, CTyp TyInt, pos) :: cs)
    | cgExpr (env, PT (BoolLit (b, pos)), t, cs) =
      (CTerm (BoolLit (b, (pos, t))), CEqc (getTEnv env, t, CTyp TyBool, pos) :: cs)
    | cgExpr (env, PT (Op (bop, pos)), t, cs) =
      (CTerm (Op (bop, (pos, t))), CEqc (getTEnv env, tcop bop, t, pos) :: cs)
    | cgExpr (env, PT (Let (ds, e, pos)), t, cs) =
      let val (envL, dsC, cs') = cgDecs (env, ds, cs)
          val (eC, csr) = cgExpr (envL, e, t, cs')
      in  (CTerm (Let (dsC, eC, (pos, t))), csr)
      end
    | cgExpr (env, PT (If (e1, e2, e3, pos)), t, cs) =
      let val (e1', cs1) = cgExpr (env, e1, CTyp TyBool, cs)
          val (e2', cs2) = cgExpr (env, e2, t, cs1)
          val (e3', cs3) = cgExpr (env, e3, t, cs2)
      in  (CTerm (If (e1', e2', e3', (pos, t))), cs3)
      end
    | cgExpr (env, PT (Case (e, alts, pos)), t, cs) =
      let val te = newUVar ()
          val (e', cs1) = cgExpr (env, e, te, cs)
          fun hAlt (((c, args), eb), (ralts, cs)) =
              let val tc = (case lookup (#lvar env, c) of
                                SOME (tS, Ctor) => instTyS tS
                              | SOME (_,  BVar) => raise Fatal (Other (c ^ " is not a constructor.\n", pos))
                              | NONE => (case lookup (#gvar env, c) of
                                             SOME (ttS, Ctor) => instTyS (TAst.trTySNM ttS)
                                           | SOME (_,   BVar) => raise Fatal (Other (c ^ " is not a constructor.\n", pos))
                                           | NONE => raise Fatal (VarUndef (c, pos))))
                  val (ft, bds)  = bindArgs (pos, args, tc)
                  val (eb', cs') = cgExpr (env withLV List.revAppend (map (fn (x, ts) => (x, (ts, BVar))) bds, #lvar env), eb, t, cs)
              in (((c, bds), eb') :: ralts , CEqc (getTEnv env, ft, te, pos) :: cs')
              end
          val (ralts, cs2) = foldl hAlt ([], cs1) alts
      in (CTerm (Case (e', rev ralts, (pos, t))), cs2)
      end
    | cgExpr (env, PAnn (e, pt, pos), t, cs) =
      let val at = kindCheck (#lty env @ map flip (#gty env), pos, pt, KTyp)
          val (e', cs') = cgExpr (env, e, t, cs)
      in  (e', CEqc (getTEnv env, t, at, pos) :: cs')
      end
    | cgExpr (env, PHole pos, t, cs) =
      (CHole (pos, (#lty env, #lvar env), t), cs)

  and cgDec (env, PD (Fun defs), cs) =
      let fun hArg (arg, (tas, tr)) =
              let val t = newUVar ()
              in  ((arg, t) :: tas, CTyp (TyArr (t, tr)))
              end
          fun aux (G, [], cs) = (G, [], cs)
            | aux (G, (x, args, e, pos) :: ds, cs) =
              let val tres = newUVar ()
                  val (tas, ty) = foldr hArg ([], tres) args
                  val (GR, ds', cs') = aux ((x, (CSMono ty, BVar)) :: G, ds, cs)
                  val (e', rcs) = cgExpr (env withLV List.revAppend (map (fn (x, t) => (x, (CSMono t, BVar))) tas, GR), e, tres, cs')
              in  (GR, (x, tas, e', (pos, CSMono ty)) :: ds', rcs)
              end
          val (GR, dsr, csr) = aux (#lvar env, defs, cs)
      in  (env withLV GR, CDec (Fun dsr), csr)
      end
    | cgDec (env, PD (PFun defs), cs) =
      let fun hArg (D, pos) ((x, pt), (asC, tr)) =
              let val t = kindCheck (D @ map flip (#gty env), pos, pt, KTyp)
              in  ((x, t) :: asC, (CTyp (TyArr (t, tr))))
              end
          fun aux (G, [], cs) = (G, [], cs)
            | aux (G, (x, targs, vargs, tres, e, pos) :: ds, cs) =
              let val targsC = map (fn x => (x, (newTVar (), KTyp))) targs
                  val DC = List.revAppend (targsC, #lty env)
                  val tresC = kindCheck (DC @ map flip (#gty env), pos, tres, KTyp)
                  val (vargsC, tyC) = foldr (hArg (DC, pos)) ([], tresC) vargs
                  val (GR, ds', cs') = aux ((x, (CSPoly (targsC, tyC), BVar)) :: G, ds, cs)
                  val (eC, rcs) = cgExpr (env withLT DC withLV List.revAppend (map (fn (x, t) => (x, (CSMono t, BVar))) vargsC, GR), e, tresC, cs')
              in  (GR, (x, targsC, vargsC, tresC, eC, (pos, CSPoly (targsC, tyC))) :: ds', rcs)
              end
          val (GR, dsr, csr) = aux (#lvar env, defs, cs)
      in  (env withLV GR, CDec (PFun dsr), csr)
      end
    | cgDec (env, PD (Data ds), cs) =
    let (* First, gather the names and kinds of datatypes, and generate tyvars for them *)
        val tyks = map (fn (tn, k, _, _) => (tn, (newTVar (), k))) ds
        val DR = List.revAppend (tyks, #lty env)
        (* Handle a constructor: generate tyvars for polymorphic values,
         * check that the kind works out, and add it to the environment. *)
        fun hCon tv D pos ((v, tns, ty), (cs, cts)) =
            let val tvs = map (fn tn => (tn, (newTVar (), KTyp))) tns
                val DC = List.revAppend (tvs, D)
                val tres = kindCheck (DC @ map flip (#gty env), pos, ty, KTyp)
                val _ = ctorCheck (DC, pos, tv, tres)
            in ((v, tvs, tres) :: cs, (v, CSPoly (tvs, tres)) :: cts)
            end
        (* Handle one (of possibly several mutually recursive) declaration:
         * get the tyvar associated with the type name earlier, handle the constructors
         * and generate the resulting environment. *)
        fun hDec D ((tn, k, cs, pos), (ds, G)) =
            let val tv = valOf (lookup (tyks, tn))
                val (rcs, rcts) = foldl (hCon (#1 tv) D pos) ([], []) cs
            in (((tn, tv), k, rev rcs, (pos, rev rcts)) :: ds, map (fn (x, y) => (x, (y, Ctor))) rcts @ G)
            end
        val (dsr, GR) = foldl (hDec DR) ([], #lvar env) ds
    in (env withLT DR withLV GR, CDec (Data (rev dsr)), cs)
    end

  and cgDecs (env, ds, cs) =
      let fun aux ([], env, rds, cs) = (env, rev rds, cs)
            | aux (d :: ds, env, rds, cs) =
              let val (env', d', cs') = cgDec (env, d, cs)
              in  aux (ds, env', d' :: rds, cs')
              end
      in  aux (ds, env, [], cs)
      end

  fun reset () = (uvcntr := 0; errors := [])
  fun restart () = (tvcntr := 0; reset ())

  fun genConstrExpr (E, e) =
      ((*reset (); *) cgExpr (mkEnv (E, ([], [])), e, newUVar (), []))

  fun genConstrDec (E, d) =
      let (*val _ = reset ()*)
          val (_, d, cs) = cgDec (mkEnv (E, ([], [])), d, [])
      in (d, cs)
      end

  fun genConstrDecs (E, ds) =
      let (*val _ = reset ()*)
          val (_, ds, cs) = cgDecs (mkEnv (E, ([], [])), ds, [])
      in (ds, cs)
      end

  local
      val revsub = ref [] : (TAst.tvar * cgTyp) list ref

      fun trInstTy t =
          let fun aux (TAst.TyMono k) =
                  (case lookup (!revsub, k) of
                       SOME t => t
                     | NONE => let val t = newUVar ()
                               in t before revsub := (k, t) :: !revsub
                               end)
                | aux (TAst.TyF (TyArr  (t1, t2))) = CTyp (TyArr  (aux t1, aux t2))
                | aux (TAst.TyF (TyProd (t1, t2))) = CTyp (TyProd (aux t1, aux t2))
                | aux (TAst.TyF (TyApp  (t1, t2))) = CTyp (TyApp  (aux t1, aux t2))
                | aux (TAst.TyF (TyVar tv)) = CTyp (TyVar tv)
                | aux (TAst.TyF TyBool)     = CTyp TyBool
                | aux (TAst.TyF TyInt)      = CTyp TyInt
          in aux t
          end

      fun trInstTyS (TAst.SPoly (bs, t)) = CSPoly (map flip bs, trInstTy t)
        | trInstTyS (TAst.SMono t)       = CSMono (trInstTy t)

  in
  fun genConstrFrom (E, (D, G), t, e) =
      let (* val _ = reset ()
          val DC = map flip D
          val GC = map (fn (x, (ts, d)) => (x, (trInstTyS ts, d))) G
          val tc = trInstTy t*)
      in cgExpr (mkEnv (E, (D, G)), e, t, [])
      end
  end

  fun getErrors () = !errors

end

structure CSolver =
struct

  exception NotImplemented
  exception TypeError

  structure UF = IUnionFind

  open CGAst

  datatype 'ed res
    = StructDiff of cgTyp * cgTyp * 'ed
    | Circular   of int   * cgTyp * 'ed

  local
      open Util
      open CGAst
      open DTFunctors
      fun pend x (pend, res) = (x :: pend, res)
      fun res  x (pend, res) = (pend, x :: res)
      val subst = ref [] : (int * cgTyp UF.set) list ref
      fun getSet n = (case lookup (!subst, n) of
                          SOME set => set
                        | NONE => let val set = UF.new (CTyUVar n)
                                  in  set before (subst := (n, set) :: !subst)
                                  end)
      fun reset () = subst := []
  in

  fun force (CTyUVar n) = UF.find (getSet n)
    | force t = t

  fun getSubst () =
      let open TAst
          fun flatten (CTyp (TyArr  (t1, t2))) =
              CTyp (TyArr  (flatten (force t1), flatten (force t2)))
            | flatten (CTyp (TyProd (t1, t2))) =
              CTyp (TyProd (flatten (force t1), flatten (force t2)))
            | flatten (CTyp (TyApp  (t1, t2))) =
              CTyp (TyApp  (flatten (force t1), flatten (force t2)))
            | flatten t = t
      in  map (fn (x, t) => (x, flatten (force (UF.find t)))) (!subst)
      end

  fun occursUVar (CTyUVar m, n) = m = n
    | occursUVar (CTyp (TyArr  (t1, t2)), n) =
      occursUVar (force t1, n) orelse occursUVar (force t2, n)
    | occursUVar (CTyp (TyProd (t1, t2)), n) =
      occursUVar (force t1, n) orelse occursUVar (force t2, n)
    | occursUVar (CTyp (TyApp  (t1, t2)), n) =
      occursUVar (force t1, n) orelse occursUVar (force t2, n)
    | occursUVar (t, n) = false

  fun pickCanon (CTyUVar _, t) = t
    | pickCanon (t, CTyUVar _) = t
    (* at least I think it shouldn't be called, since
       this case is handled outside the union-find *)
    | pickCanon (CTyp t1, CTyp t2) = raise Impossible

  local
      fun getPos (CEqc (_, _, _, pos)) = pos
  in
  fun fsimpl (TyArr (t1, t2),  TyArr (s1, s2),  D, c, pr) =
      pend (CEqc (D, t1, s1, getPos c), c) (pend (CEqc (D, t2, s2, getPos c), c) pr)
    | fsimpl (TyProd (t1, t2), TyProd (s1, s2), D, c, pr) =
      pend (CEqc (D, t1, s1, getPos c), c) (pend (CEqc (D, t2, s2, getPos c), c) pr)
    | fsimpl (TyApp (t1, t2), TyApp (s1, s2),   D, c, pr) =
      pend (CEqc (D, t1, s1, getPos c), c) (pend (CEqc (D, t2, s2, getPos c), c) pr)
    | fsimpl (TyInt,  TyInt,  D, c, pr) = pr
    | fsimpl (TyBool, TyBool, D, c, pr) = pr
    | fsimpl (t1 as TyVar n1, t2 as TyVar n2, D, c, pr) =
      if n1 = n2 then pr else res (StructDiff (CTyp t1, CTyp t2, c)) pr
    | fsimpl (t1, t2, D, c, pr) = res (StructDiff (CTyp t1, CTyp t2, c)) pr
  end

  fun csimpl (CTyUVar n, CTyUVar m, D, c, pr) =
      pr before UF.union pickCanon (getSet n) (getSet m)
    | csimpl (t1 as CTyUVar n, t2, D, c, pr) =
      if occursUVar (t2, n) then res (Circular (n, t2, c)) pr
      else (pr before UF.union pickCanon (getSet n) (UF.new t2))
    | csimpl (t1, t2 as CTyUVar n, D, c, pr) =
      if occursUVar (t1, n) then res (Circular (n, t1, c)) pr
      else (pr before UF.union pickCanon (UF.new t1) (getSet n))
    | csimpl (CTyp t1, CTyp t2, D, c, pr) =
      fsimpl (t1, t2, D, c, pr)

  fun simplify constrs =
      let fun aux ([], res) = res
            | aux ((CEqc (D, t1, t2, pos), r) :: pend, res) = aux (csimpl (force t1, force t2, D, r, (pend, res)))
      in (reset (); aux (constrs, []))
      end

  end

end

structure TypeChecker =
struct

  open CGAst
  open TAst
  open DTFunctors
  open Util

  fun substC (s, CTyp (TyArr  (t1, t2))) = CTyp (TyArr  (substC (s, t1), substC (s, t2)))
    | substC (s, CTyp (TyProd (t1, t2))) = CTyp (TyProd (substC (s, t1), substC (s, t2)))
    | substC (s, CTyp (TyApp  (t1, t2))) = CTyp (TyApp  (substC (s, t1), substC (s, t2)))
    | substC (s, t as CTyp _) = t
    | substC (s, t as CTyUVar n) = (case lookup (s, n) of
                                       SOME tr => tr
                                     | NONE => t)

  fun substSC (s, CSMono t) = CSMono (substC (s, t))
    | substSC (s, CSPoly (b, t)) = CSPoly (b, substC (s, t))

  local
      val monocntr = ref 0
      val monoSub = ref [] : (int * int) list ref
      fun newMono () = let val n = !monocntr in n before monocntr := n + 1 end
      fun flip (x, (y, z)) = (y, (x, z))
  in

  fun mkMono (CTyp (TyArr  (t1, t2))) =
      TyF (TyArr  (mkMono t1, mkMono t2))
    | mkMono (CTyp (TyProd (t1, t2))) =
      TyF (TyProd (mkMono t1, mkMono t2))
    | mkMono (CTyp (TyApp  (t1, t2))) =
      TyF (TyApp  (mkMono t1, mkMono t2))
    | mkMono (CTyp TyInt)  = TyF TyInt
    | mkMono (CTyp TyBool) = TyF TyBool
    | mkMono (CTyp (TyVar a)) = TyF (TyVar a)
    | mkMono (CTyUVar n) =
      (case lookup (!monoSub, n) of
           SOME k => TyMono k
         | NONE => let val k = newMono ()
                   in TyMono k before monoSub := (n, k) :: !monoSub
                   end)

  fun subst (s, CTyp (TyArr  (t1, t2))) =
      TyF (TyArr  (subst (s, t1), subst (s, t2)))
    | subst (s, CTyp (TyProd (t1, t2))) = 
      TyF (TyProd (subst (s, t1), subst (s, t2)))
    | subst (s, CTyp (TyApp (t1, t2))) = 
      TyF (TyApp (subst (s, t1), subst (s, t2)))
    | subst (s, CTyp TyInt)  = TyF TyInt
    | subst (s, CTyp TyBool) = TyF TyBool
    | subst (s, CTyp (TyVar a)) = TyF (TyVar a)
    | subst (s, t as CTyUVar n) =
      (case lookup (s, n) of
           SOME tr => mkMono tr
         | NONE => mkMono t)

  fun substS (s, CSPoly (tvs, ty)) = SPoly (map flip tvs, subst (s, ty))
    | substS (s, CSMono ty) = SMono (subst (s, ty))

  fun trExpr (env, sub, CTerm (Var (x, (pos, ty)))) =
      TmF (Var (x, (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Abs ((x, targ), e, (pos, ty)))) =
      TmF (Abs ((x, subst (sub, targ)), trExpr (env, sub, e), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (App (e1, e2, (pos, ty)))) =
      TmF (App (trExpr (env, sub, e1), trExpr (env, sub, e2), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Pair (e1, e2, (pos, ty)))) =
      TmF (Pair (trExpr (env, sub, e1), trExpr (env, sub, e2), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Proj1 (e, (pos, ty)))) =
      TmF (Proj1 (trExpr (env, sub, e), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Proj2 (e, (pos, ty)))) =
      TmF (Proj2 (trExpr (env, sub, e), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (IntLit  (n, (pos, ty)))) =
      TmF (IntLit  (n, (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (BoolLit (n, (pos, ty)))) =
      TmF (BoolLit (n, (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Op (bop, (pos, ty)))) =
      TmF (Op (bop, (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Let (ds, e, (pos, ty)))) =
      TmF (Let (trDecs (env, sub, ds), trExpr (env, sub, e), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (If (e1, e2, e3, (pos, ty)))) =
      TmF (If (trExpr (env, sub, e1), trExpr (env, sub, e2), trExpr (env, sub, e3), (pos, subst (sub, ty))))
    | trExpr (env, sub, CTerm (Case (e, alts, (pos, ty)))) =
      TmF (Case (trExpr (env, sub, e), map (fn a => trAlt (env, sub, a)) alts, (pos, subst (sub, ty))))
    | trExpr (env, sub, CHole (pos, (D, G), t)) =
      THole (ref (Open (env, ((D, map (fn (x, (t, b)) => (x, (substSC (sub, t), b))) G), substC (sub, t)),
                        (pos, subst (sub, t)))))

  and trAlt (env, sub, ((c, bds), expr)) =
      ((c, map (fn (v, ts) => (v, substS (sub, ts))) bds), trExpr (env, sub, expr))

  and trDec (env, sub, CDec (Fun  ds)) =
      DF (Fun (map (fn (x, args, e, (pos, tyS)) =>
                       (x, map (fn (x, ty) => (x, subst (sub, ty))) args,
                        trExpr (env, sub, e), (pos, substS (sub, tyS)))) ds))
    | trDec (env, sub, CDec (PFun ds)) =
      DF (PFun (map (fn (x, targs, args, ty, e, (pos, tyS)) =>
                        (x, map flip targs, map (fn (x, ty) => (x, subst (sub, ty))) args,
                         subst (sub, ty), trExpr (env, sub, e), (pos, substS (sub, tyS)))) ds))
    | trDec (env, sub, CDec (Data ds)) =
      let fun hCtor (x, tvs, ty)  = (x, map flip tvs, subst (sub, ty))
          fun hCTyp (x, tyS)      = (x, substS (sub, tyS))
          fun hData (tv, k, cs, (p, cts)) = (flip tv, k, map hCtor cs, (p, map hCTyp cts))
      in DF (Data (map hData ds))
      end

  and trDecs (env, sub, ds) = map (fn d => trDec (env, sub, d)) ds

  end      

  local
      fun merge ([], xs) = xs
        | merge (xs, []) = xs
        | merge (x :: xs, y :: ys) = if x <= y then x :: merge (xs, y :: ys) else y :: merge (x :: xs, ys)
  in

  fun getMonos (TyF (TyArr  (t1, t2))) = merge (getMonos t1, getMonos t2)
    | getMonos (TyF (TyProd (t1, t2))) = merge (getMonos t1, getMonos t2)
    | getMonos (TyF (TyApp  (t1, t2))) = merge (getMonos t1, getMonos t2)
    | getMonos (TyF t) = []
    | getMonos (TyMono n) = [n]

  end

  fun monErrs (DF d) =
      let fun fout xs = List.filter (fn (ms, _, _) => not (null ms)) xs
          fun gMS (SPoly (xs, ty)) = getMonos ty
            | gMS (SMono ty) = getMonos ty
          fun gMon (Fun ds) = List.map (fn (_, _, _, (pos, tyS)) => (gMS tyS, tyS, pos)) ds
            | gMon (PFun ds) = List.map (fn (_, _, _, _, _, (pos, tyS)) => (gMS tyS, tyS, pos)) ds
            | gMon (Data _) = []
      in fout (gMon d)
      end

  datatype error = EVarUndefined  of var * pos
                 | ETVarUndefined of tname * pos
                 | ECircularDep   of cgTContext * int * cgTyp * cgTyp * cgTyp * pos
                 | EStructDiff    of cgTContext * cgTyp * cgTyp * cgTyp * cgTyp * pos
                 | EEscapedMonos  of int list * tyS * pos
                 | EOther         of string * pos

  fun reportMS xs = Sum.INL (map EEscapedMonos xs)

  fun reportErrors (cgErrs, tyErrs, subst) =
      let open ConstrGen
          open CSolver
          fun docg (VarUndef  (x, pos)) = EVarUndefined  (x, pos)
            | docg (TVarUndef (a, pos)) = ETVarUndefined (a, pos)
            | docg (Other     (s, pos)) = EOther         (s, pos)
          fun dotc s (StructDiff (t1, t2, CEqc (D, st1, st2, pos))) =
              EStructDiff (D, substC (s, t1), substC (s, t2), substC (s, st1), substC (s, st2), pos)
            | dotc s (Circular (n, t, CEqc (D, st1, st2, pos))) =
              ECircularDep (D, n, t, substC (s, st1), substC (s, st2), pos)
      in Sum.INL (map docg cgErrs @ map (dotc subst) tyErrs)
      end

  fun tcExpr (E, e) =
      let val (e', cs) = ConstrGen.genConstrExpr (E, e)
          val cgErrs   = ConstrGen.getErrors ()
          val residual = CSolver.simplify (map (fn x => (x, x)) cs)
          val sub      = CSolver.getSubst ()
      in if null cgErrs andalso null residual
         then let val e'' = trExpr (E, sub, e')
                  val (pos, ty) = TAst.annE e''
                  val ms = getMonos ty
              in if null ms then Sum.INR e''
                 else reportMS [(ms, SMono ty, pos)]
              end
         else reportErrors (cgErrs, residual, sub)
      end handle ConstrGen.Fatal err => reportErrors ([err], [], [])

  fun tcDec (E, d) =
      let val (d', cs) = ConstrGen.genConstrDec (E, d)
          val cgErrs   = ConstrGen.getErrors ()
          val residual = CSolver.simplify (map (fn x => (x, x)) cs)
          val sub      = CSolver.getSubst ()
      in if null cgErrs andalso null residual
         then let val d''  = trDec (E, sub, d')
                  val errs = monErrs d''
              in if null errs then Sum.INR d''
                 else reportMS errs
              end
         else reportErrors (cgErrs, residual, sub)
      end handle ConstrGen.Fatal err => reportErrors ([err], [], [])

  fun tcDecs (E, ds) =
      let open Sum
          fun hD (d, INL err) = INL err
            | hD (d, INR (ds, E)) =
              (case tcDec (E, d) of
                   INL err => INL err
                 | INR d'  => INR (d' :: ds, extWith (E, d')))
      in foldl hD (INR ([], E)) ds
      end handle ConstrGen.Fatal err => reportErrors ([err], [], [])

  fun refineExpr (E, env, t, e) =
      let val (e', cs) = ConstrGen.genConstrFrom (E, env, t, e)
          val cgErrs   = ConstrGen.getErrors ()
          val residual = CSolver.simplify (map (fn x => (x, x)) cs)
          val sub      = CSolver.getSubst ()
      in if null cgErrs andalso null residual
         then let val e'' = trExpr (E, sub, e')
                  val (pos, ty) = TAst.annE e''
                  val ms = getMonos ty
              in if null ms then Sum.INR (e'', sub)
                 else reportMS [(ms, SMono ty, pos)]
              end
         else reportErrors (cgErrs, residual, sub)
      end handle ConstrGen.Fatal err => reportErrors ([err], [], [])
      
end
