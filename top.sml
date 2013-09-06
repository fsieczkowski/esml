structure Top =
struct

      val holes = ref [] : TAst.hole ref list ref
      val env   = ref ([], []) : TAst.env ref

  local

      fun eval e = e
      open TypeChecker
      fun ppty t = TAst.ppty (#1 (!env), t)
      fun pptys s = TAst.pptys (#1 (!env), s)
      fun showVal e = "-exp-:" ^ (ppty o #2 o TAst.annE) e ^ "\n"
      fun extData ((tv, tn), k, cs, _) = (tv, (tn, DData (k, map (fn (x, _, _) => x) cs)))
      fun showDec (D, TAst.DF (DTFunctors.Fun ds)) =
          concat (map (fn (x, _, _, (_, ts)) => "val " ^ x ^ " : " ^ TAst.pptys (D, ts) ^ "\n") ds)
        | showDec (D, TAst.DF (DTFunctors.PFun ds)) =
          concat (map (fn (x, _, _, _, _, (_, ts)) => "val " ^ x ^ " : " ^ TAst.pptys (D, ts) ^ "\n") ds)
        | showDec (D, TAst.DF (DTFunctors.Data ds)) =
          let fun pptargs [] = ""
                | pptargs ts = "[" ^ String.concatWith " " (map (fn (_, tn) => tn) ts) ^ "] "
              val D' = List.revAppend (map extData ds, D)
              fun ppcons (x, tvs, ty) = x ^ " : " ^ pptargs tvs ^ TAst.ppty (List.revAppend (map (fn (x, t) => (x, (t, DPoly))) tvs, D'), ty)
              fun ppdec ((_, tn), k, cs, _) =
                  "datatype " ^ tn ^ " : " ^ ppknd k ^ " = " ^ String.concatWith " | " (map ppcons cs) ^ "\n"
          in concat (map ppdec ds)
          end
      fun showErr (EVarUndefined (v, pos))  =
          Pos.toString pos ^ " Error: unbound variable: " ^ v ^ "\n"
        | showErr (ETVarUndefined (a, pos)) =
          Pos.toString pos ^ " Error: unbound type variable: " ^ a ^ "\n"
        | showErr (EEscapedMonos (ns, ts, pos)) =
          Pos.toString pos ^ " Type error: free monomorphic type variables.\nIn type: " ^ pptys ts ^ "\n"
        | showErr (EStructDiff (D, t1, t2, st1, st2, pos)) =
          Pos.toString pos ^ " Type error: incompatible types.\nCannot match: "
          ^ CGAst.ppty D t1 ^ " with " ^ CGAst.ppty D t2 ^ " arising from the following equation.\nExpected: "
          ^ CGAst.ppty D st1 ^ "\nActual: " ^ CGAst.ppty D st2 ^ "\n"
        | showErr (ECircularDep (D, n, t, st1, st2, pos)) =
          Pos.toString pos ^ " Type error: circular dependency.\nType: "
          ^ CGAst.ppuvar n ^ " occurs in " ^ CGAst.ppty D t ^ " arising from the following equation.\nExpected: "
          ^ CGAst.ppty D st1 ^ "\nActual: " ^ CGAst.ppty D st2 ^ "\n"
        | showErr (EOther (s, pos)) = Pos.toString pos ^ " " ^ s
      open Sum
  in

  exception Err

  fun appDec (d as DF (Data ds), D) = List.revAppend (List.map extData ds, D) before print (showDec (D, d))
    | appDec (d, D) = D before print (showDec (D, d))

  fun getHolesE (THole hl) = (case !hl of
                                  Open _ => holes := hl :: !holes
                                | Closed e => getHolesE e)
    | getHolesE (TmF (Abs (_, e, _))) = getHolesE e
    | getHolesE (TmF (App (e1, e2, _)))  = (getHolesE e1; getHolesE e2)
    | getHolesE (TmF (Pair (e1, e2, _))) = (getHolesE e1; getHolesE e2)
    | getHolesE (TmF (Proj1 (e, _))) = getHolesE e
    | getHolesE (TmF (Proj2 (e, _))) = getHolesE e
    | getHolesE (TmF (If (e1, e2, e3, _))) = (getHolesE e1; getHolesE e2; getHolesE e3)
    | getHolesE (TmF (Let (ds, e, _))) = (app getHolesD ds; getHolesE e)
    | getHolesE (TmF (Case (e, alts, _))) = (getHolesE e; app (getHolesE o #2) alts)
    | getHolesE (TmF _) = ()

  and getHolesD (DF (Fun ds))  = app (fn (_, _, e, _) => getHolesE e) ds
    | getHolesD (DF (PFun ds)) = app (fn (_, _, _, _, e, _) => getHolesE e) ds
    | getHolesD (DF (Data _)) = ()


  fun runPExp e =
      (case TypeChecker.tcExpr (!env, e) of
           INL errs => app (print o showErr) errs
         | INR exp =>
           (print o showVal o eval) exp)

  fun parseExp s =
      (case Parser.parseExp s of
           INL err => raise Err before print err
         | INR exp => exp)

  fun runExp s = runPExp (parseExp s)

  fun runPDec d =
      (case TypeChecker.tcDec (!env, d) of
           INL errs => app (print o showErr) errs
         | INR d'   => (getHolesD d';
                        appDec (d', (#1 (!env)));
                        env := extWith (!env, d')))

  fun runReplExp s =
      (case Parser.parseRepl s of
           INL err => print err
         | INR (INL e) => runPExp e
         | INR (INR d) => runPDec d)

  fun parseDecs s =
      (case Parser.parseDecList s of
           INL err => (print err; NONE)
         | INR exp => SOME exp)

  fun runDecs s =
      (case Parser.parseDecList s of
           INL err => print err
         | INR ds =>
           (case TypeChecker.tcDecs (!env, ds) of
                INL errs => app (print o showErr) errs
              | INR (ds', E') => (app getHolesD ds';
                                  foldl appDec (#1 (!env)) (rev ds');
                                  env := E')))

  fun runFile f =
      (case Parser.parseFile f of
           INL err => print err
         | INR ds => (case TypeChecker.tcDecs (!env, ds) of
                          INL errs => app (print o showErr) errs
                        | INR (ds', E') => (app getHolesD ds';
                                            foldl appDec (#1 (!env)) (rev ds');
                                            env := E')))

  fun getHolesPos () =
      let fun pphp (Open (_, _, (pos, _))) =
              "(" ^ Int.toString (Coord.line (Pos.left pos) + Coord.abs (Pos.left pos) - 1) ^ " . " ^
              Int.toString (Coord.line (Pos.right pos) + Coord.abs (Pos.right pos) - 1) ^ ")"
      in "(" ^ String.concatWith " " (List.map (pphp o !) (!holes)) ^ ")"
      end

  fun showHoles () =
      let fun pph (hr, (s, n)) =
              (case !hr of
                   Open ((DG, _), ((D, G), t), _) => (s ^ Int.toString n ^ " : " ^ CGAst.ppty (D @ List.map flip DG) t ^ "\n", n + 1)
                 | Closed t => raise Util.Impossible)
      in (print o #1 o foldl pph ("", 0)) (!holes)
      end

  fun showHole n =
      let val (env, ((D, G), t)) = (case (! (List.nth (!holes, n))) of
                                        Open (env, tys, _) => (env, tys)
                                      | Closed t => raise Util.Impossible)
          val tc = String.concatWith "\n" (List.map #1 (rev D))
          val DD = D @ List.map flip (#1 env)
          val vc = String.concat (List.map (fn (v, (ts, _)) => v ^ " : " ^ CGAst.pptys (DD, ts) ^ "\n") (rev G))
          val sep = "====================\n"
          val ty = CGAst.ppty DD t
      in print (tc ^ "\n" ^ vc ^ sep ^ ty ^ "\n")
      end

  fun subHoles (sub, []) = []
    | subHoles (sub, h :: hs) =
      let val substG = List.map (fn (x, (t, b)) => (x, (TypeChecker.substSC (sub, t), b)))
          fun substT t = TypeChecker.substC (sub, t)
      in case !h of
             Open (env, ((D, G), t), pt) => subHoles (sub, hs) before
                                            h := Open (env, ((D, substG G), substT t), pt)
           | Closed t => raise Impossible
      end

  fun refineHole (n, s) =
      let val (prev, h :: post) = Util.takeDrop (n, !holes)
          val Open (env, ((D, G), t), _) = !h
      in case Parser.parseExp s of
             INL err => raise Err before print err
           | INR e =>
             (case TypeChecker.refineExpr (env, (D, G), t, e) of
                  INL errs => raise Err before app (print o showErr) errs
                | INR (e', sub) =>
                  (holes := [];
                   getHolesE e';
                   print ("Refining successful, " ^ Int.toString (length (!holes)) ^ " new holes.\n");
                   h := Closed e';
                   subHoles (sub, prev); subHoles (sub, post);
                   length (!holes) before holes := prev @ !holes @ post))
      end
          
  fun applyHole (n, s) =
      let val (prev, h :: post) = Util.takeDrop (n, !holes)
          val Open (env, ((D, G), t), _) = !h
          fun countArrs ts =
              let open CGAst
                  open DTFunctors
                  fun aux (CTyp (TyArr (ta, t)), n, ts) = aux (t, n + 1, ta :: ts)
                    | aux (t, n, ts) = (t, n, rev ts)
              in aux (ts, 0, [])
              end
          fun countArrsS (CSPoly (_, t)) = countArrs t
            | countArrsS (CSMono t) = countArrs t
          val e = (case Parser.parseExp s of
                       INL err => raise Err before print err
                     | INR e => e)
          val te = ConstrGen.newUVar ()
          val (e', sub) = (case TypeChecker.refineExpr (env, (D, G), te, e) of
                               INL errs => raise Err before app (print o showErr) errs
                             | INR es => es)
          val te' = TypeChecker.substC (sub, te)
          val (tretA, narrA, targsA) = countArrs te'
          val (tretH, narrH, targsH) = countArrs t
          val emptyPos = Pos.pos (Coord.init "-") (Coord.init "-")
          val _ = if narrA < narrH then raise Err before print "Types don't match" else ()
          val (hargsA, margsA) = Util.takeDrop (narrA - narrH, targsA)
          val cs = CEqc (D @ List.map flip (#1 env), tretH, tretA, emptyPos) ::
                   ListPair.mapEq (fn (tH, tA) => CEqc (D @ List.map flip (#1 env), tH, tA, emptyPos)) (targsH, margsA)
          val residual = CSolver.simplify (List.map (fn x => (x, x)) cs)
          val sub      = CSolver.getSubst ()
          val _ = if null residual then ()
                  else (raise Err before app (print o showErr) (outL (TypeChecker.reportErrors ([], residual, sub))))
          fun appNHoles (e, []) = (e, #2 (TAst.annE e))
            | appNHoles (e, t :: ts) =
              let val rt = TypeChecker.subst (sub, t)
                  val ct = TypeChecker.substC (sub, t)
                  val (ne, TyF (TyArr (_, retT))) = appNHoles (e, ts)
              in  (TmF (App (ne, THole (ref (Open (env, ((D, G), ct), (emptyPos, rt)))), (emptyPos, retT))), retT)
              end
          val (nexp, _) = appNHoles (e', hargsA)
      in (holes := [];
          getHolesE nexp;
          print ("Application successful, " ^ Int.toString (length (!holes)) ^ " new holes.\n");
          h := Closed nexp;
          subHoles (sub, prev); subHoles (sub, post);
          length (!holes) before holes := prev @ !holes @ post)
      end

  fun clear () = (holes := []; env := ([], []); ConstrGen.restart ())

  fun numHoles () = length (!holes)

  local 

      open DTFunctors
      open TAst
      val vcntr = ref 0
      val dummyPos = Pos.pos (Coord.init "-") (Coord.init "-")
      fun newVar () = let val n = !vcntr in "var" ^ Int.toString n before vcntr := n + 1 end
      fun splitT (TyF (TyApp (t1, t2)), acc) = splitT (t1, t2 :: acc)
        | splitT (TyF (TyVar x), acc) = (x, acc)
        | splitT _ = raise Err before print "Expression's type is not a datatype"
      fun stripArrs (TyF (TyArr (t1, t2)), acc) = stripArrs (t2, t1 :: acc)
        | stripArrs (t, acc) = (t, acc)
      fun subInst (sub, bds) (t as (TyF (TyVar v))) =
          if List.exists (fn (tv, _) => v = tv) bds then
              case lookup (sub, t) of
                  SOME t => trTypNM t
                | NONE   => ConstrGen.newUVar ()
          else CTyp (TyVar v)
        | subInst sb (TyF (TyArr  (t1, t2))) = CTyp (TyArr  (subInst sb t1, subInst sb t2))
        | subInst sb (TyF (TyProd (t1, t2))) = CTyp (TyProd (subInst sb t1, subInst sb t2))
        | subInst sb (TyF (TyApp  (t1, t2))) = CTyp (TyApp  (subInst sb t1, subInst sb t2))
        | subInst sb (TyF TyInt)  = CTyp TyInt
        | subInst sb (TyF TyBool) = CTyp TyBool
        | subInst sb _ = raise Impossible

  in
  (* Fixme: lookup should go through D/G as well as env *)
  fun buildCaseE (retT, e, env : TAst.env, (D, G)) =
      let fun mkHole aG t = Open (env, ((D, aG @ G), trTypNM t), (dummyPos, t))
          val (_, t) = TAst.annE e
          val (v, ts) = splitT (t, [])
          val cs = case lookup (List.map flip D @ #1 env, v) of
                       SOME (_, DData (_, cs))  => cs
                     | _ => raise Err before print "Expression's type is not a datatype"
          fun doCon c =
              let val ((ft, ats), bs) = (case #1 (valOf (lookup (#2 env, c))) of
                                             SPoly (bs, t) => (stripArrs (t, []), bs)
                                           | SMono t => (stripArrs (t, []), []))
                  val (v', targs) = splitT (ft, [])
                  val _ = if v' <> v then raise Impossible else ()
                  val tsub = ListPair.zipEq (targs, ts)
                  val rG = List.map (fn t => (newVar (), CSMono (subInst (tsub, bs) t))) ats
              in  ((c, List.map (fn (x, ts) => (x, substS ([], ts))) (rev rG)),
                   THole (ref (mkHole (List.map (fn (x, t) => (x, (t, BVar))) rG) retT)))
              end
      in  TmF (Case (e, List.map doCon cs, (dummyPos, retT)))
      end
  end

  fun refineCase (n, s) =
      let val (prev, h :: post) = Util.takeDrop (n, !holes)
          val Open (env, ((D, G), t), (pos, rt)) = !h
      in case Parser.parseExp s of
             INL err => raise Err before print err
           | INR e =>
             (case TypeChecker.refineExpr (env, (D, G), ConstrGen.newUVar (), e) of
                  INL errs => raise Err before app (print o showErr) errs
                | INR (e', sub) =>
                  let val re = buildCaseE (rt, e', env, (D, G))
                  in (holes := [];
                      getHolesE re;
                      print ("Refining successful, " ^ Int.toString (length (!holes)) ^ " new holes.\n");
                      h := Closed re;
                      subHoles (sub, prev); subHoles (sub, post);
                      length (!holes) before holes := prev @ !holes @ post)
                  end)

      end

  end


end
