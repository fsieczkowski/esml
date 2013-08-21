structure Top =
struct

  local
      fun eval e = e
      open TypeChecker
      fun ppty t = TAst.ppty ([], t)
      fun pptys s = TAst.pptys ([], s)
      fun showVal e = "-exp-:" ^ (ppty o #2 o TAst.annE) e ^ "\n"
      fun showDec (D, TAst.DF (DTFunctors.Fun ds)) =
          concat (map (fn (x, _, _, (_, ts)) => "val " ^ x ^ " : " ^ TAst.pptys (D, ts) ^ "\n") ds)
        | showDec (D, TAst.DF (DTFunctors.PFun ds)) =
          concat (map (fn (x, _, _, _, _, (_, ts)) => "val " ^ x ^ " : " ^ TAst.pptys (D, ts) ^ "\n") ds)
        | showDec (D, TAst.DF (DTFunctors.Data ds)) =
          let fun pptargs [] = ""
                | pptargs ts = "[" ^ String.concatWith " " (map (fn (_, (tn, _)) => tn) ts) ^ "] "
              val D' = List.revAppend (map #1 ds, D)
              fun ppcons (x, tvs, ty) = x ^ " : " ^ pptargs tvs ^ TAst.ppty (List.revAppend (tvs, D'), ty)
              fun ppdec ((_, (tn, _)), k, cs, _) =
                  "datatype " ^ tn ^ " : " ^ ppknd k ^ " = " ^ String.concatWith " | " (map ppcons cs) ^ "\n"
          in concat (map ppdec ds)
          end
      fun showErr (EVarUndefined (v, pos))  =
          Pos.toString pos ^ " Error: unbound variable: " ^ v ^ "\n"
        | showErr (ETVarUndefined (a, pos)) =
          Pos.toString pos ^ " Error: unbound type variable: " ^ a ^ "\n"
        | showErr (EEscapedMonos (ns, ts, pos)) =
          Pos.toString pos ^ " Type error: free monomorphic type variables.\nIn type: " ^ pptys ts ^ "\n"
        | showErr (EStructDiff (t1, t2, st1, st2, pos)) =
          Pos.toString pos ^ " Type error: incompatible types.\nCannot match: "
          ^ CGAst.ppty [] t1 ^ " with " ^ CGAst.ppty [] t2 ^ " arising from the following equation.\nExpected: "
          ^ CGAst.ppty [] st1 ^ "\nActual: " ^ CGAst.ppty [] st2 ^ "\n"
        | showErr (ECircularDep (n, t, st1, st2, pos)) =
          Pos.toString pos ^ " Type error: circular dependency.\nType: "
          ^ CGAst.ppuvar n ^ " occurs in " ^ CGAst.ppty [] t ^ " arising from the following equation.\nExpected: "
          ^ CGAst.ppty [] st1 ^ "\nActual: " ^ CGAst.ppty [] st2 ^ "\n"
      open Sum
  in

  fun appDec (d as DF (Data ds), D) = List.revAppend (List.map #1 ds, D) before print (showDec (D, d))
    | appDec (d, D) = D before print (showDec (D, d))

  val holes = ref [] : TAst.hole ref list ref

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

  fun runExp s =
      (case Parser.parseExp s of
           INL err => print err
         | INR exp =>
           (case TypeChecker.tcExpr exp of
                INL errs => app (print o showErr) errs
              | INR exp =>
                (print o showVal o eval) exp))

  fun parseExp s =
      (case Parser.parseExp s of
           INL err => (print err; NONE)
         | INR exp => SOME exp)

  fun parseDecs s =
      (case Parser.parseDecList s of
           INL err => (print err; NONE)
         | INR exp => SOME exp)

  fun runDecs s =
      (case Parser.parseDecList s of
           INL err => print err
         | INR ds =>
           (case TypeChecker.tcDecs ds of
                INL errs => app (print o showErr) errs
              | INR ds' => (app getHolesD ds';
                            foldl appDec [] ds'; ())))

  fun runFile f =
      (holes := [];
       case Parser.parseFile f of
           INL err => print err
         | INR ds => (case TypeChecker.tcDecs ds of
                          INL errs => app (print o showErr) errs
                        | INR ds' => (app getHolesD ds';
                                      foldl appDec [] ds'; ())))

  fun showHoles () =
      let fun pph (hr, (s, n)) =
              (case !hr of
                   Open (_, (D, _, t), _) => (s ^ Int.toString n ^ " : " ^ TAst.ppty (D, t) ^ "\n", n + 1)
                 | Closed t => raise Util.Impossible)
      in (print o #1 o foldl pph ("", 0)) (!holes)
      end

  fun showHole n =
      let val (D, G, t) = (case (! (List.nth (!holes, n))) of
                               Open (_, tys, _) => tys
                             | Closed t => raise Util.Impossible)
          val tc = String.concatWith "\n" (List.map (#1 o #2) (rev D))
          val vc = String.concat (List.map (fn (v, (ts, _)) => v ^ " : " ^ TAst.pptys (D, ts) ^ "\n") (rev G))
          val sep = "====================\n"
          val ty = TAst.ppty (D, t)
      in print (tc ^ "\n" ^ vc ^ sep ^ ty ^ "\n")
      end

  fun refineHole (n, s) =
      let exception Err
          val e = (case Parser.parseExp s of
                       INL err => raise Err before print err
                     | INR e => e)
          val (prev, h :: post) = Util.takeDrop (n, !holes)
          val Open (pos, (D, G, t), _) = !h
          val e' = (case TypeChecker.refineExpr ((D, G), t, e) of
                        INL errs => raise Err before app (print o showErr) errs
                      | INR e => e)
      in (holes := [];
          getHolesE e';
          print ("Refining successful, " ^ Int.toString (length (!holes)) ^ " new holes.\n");
          h := Closed e';
          holes := prev @ !holes @ post)
      end

  end

  fun clear () = holes := []

end
