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
          
  fun applyHole (n, id) =
      let val (prev, h :: post) = Util.takeDrop (n, !holes)
          val Open (env, ((D, G), t), _) = !h
          fun countArrs ts =
              let open CGAst
                  open DTFunctors
                  fun aux (CTyp (TyArr (_, t)), acc) = aux (t, acc + 1)
                    | aux (_, acc) = acc
              in aux (ts, 0)
              end
          fun countArrsS (CSPoly (_, t)) = countArrs t
            | countArrsS (CSMono t) = countArrs t
          val narr = (case lookup (G, id) of
                          SOME (ts, _) => countArrsS ts
                        | NONE => (case lookup (#2 env, id) of
                                       SOME (ts, _) => countArrsS (TAst.trTySNM ts)
                                     | NONE => raise Err before print ("Undeclared identifier " ^ id ^ "\n")))
          val nart = countArrs t
          val emptyPos = Pos.pos (Coord.init "-") (Coord.init "-")
          fun appNHoles (e, n) =
              let open PAst
                  open DTFunctors
              in if n = 0 then e else appNHoles (PT (App (e, PHole emptyPos, emptyPos)), n - 1)
              end
          val nexp = appNHoles (PAst.PT (DTFunctors.Var (id, emptyPos)), Int.max(0, narr - nart))
          val (nexp', sub) = (case TypeChecker.refineExpr (env, (D, G), t, nexp) of
                                  INL errs => raise Err before app (print o showErr) errs
                                | INR e => e)
      in (holes := [];
          getHolesE nexp';
          print ("Application successful, " ^ Int.toString (length (!holes)) ^ " new holes.\n");
          h := Closed nexp';
          subHoles (sub, prev); subHoles (sub, post);
          length (!holes) before holes := prev @ !holes @ post)
      end

  fun clear () = (holes := []; env := ([], []); ConstrGen.restart ())

  fun numHoles () = length (!holes)

  end

end
