structure Reserved :> MINI_LANGUAGE_DEF =
struct

  val reservedNames = ["val", "fun", "type", "rec", "let", "in", "end", "fn", "and",
                       "signature", "sig", "structure", "struct", "datatype",
                       "case", "of", "int", "bool", "if", "then", "else", "fst", "snd"]
  val reservedOpNames = ["=>", ":", "=", "->", "|", "*", "#"]

end

structure Parser =
struct

  structure LD = MLStyle (Reserved)
  structure TP = TokenParser (LD)
  open Sum
  open PAst

  open ParserCombinators
  open CharParser
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  fun notIn lst x = List.all (fn y => y <> x) lst

  local
      fun flat3' ((x, y), z) = (x, y, z)
      fun flat4' ((x, y, z), t) = (x, y, z, t)
      fun flat5' ((w, x, y, z), t) = (w, x, y, z, t)
      fun flat6' ((u, w, x, y, z), t) = (u, w, x, y, z, t)
      fun mergePos (t1, t2) = (t1, t2, Pos.union (annE t1) (annE t2))

      structure F = DTFunctors
      val Var   = PT o F.Var
      val Abs   = PT o F.Abs
      val App   = PT o F.App
      val Case  = PT o F.Case
      val Pair  = PT o F.Pair
      val Proj1 = PT o F.Proj1
      val Proj2 = PT o F.Proj2
      val IntL  = PT o F.IntLit
      val BoolL = PT o F.BoolLit
      val Op    = PT o F.Op
      val Let   = PT o F.Let
      val If    = PT o F.If
      val Fun   = PD o F.Fun
      val PFun  = PD o F.PFun
      val Data  = PD o F.Data
      val TArr  = PTyp o F.TyArr
      val TProd = PTyp o F.TyProd
      val TApp  = PTyp o F.TyApp
      val TInt  = PTyp F.TyInt
      val TBool = PTyp F.TyBool
      val TVar  = PTyp o F.TyVar

      val KTyp  = F.KTyp
      val KArr  = F.KArr

      val idops = [("div", F.Div), ("mod", F.Mod), ("not", F.Not), ("andalso", F.And), ("orelse", F.Or)]
      val opops = [("+", F.Add), ("-", F.Sub), ("*", F.Mul), ("~", F.Neg), ("=", F.Eq), ("<", F.Lt),
                   (">", F.Gt), ("<=", F.LEq), (">=", F.GEq)]
      val idvals = [("true", true), ("false", false)]

      val resids = List.map #1 idvals @ List.map #1 idops @ LD.reservedNames
      val resops = List.map #1 opops  @ LD.reservedOpNames
  in
      open TP


  val ident = try (identifier suchthat (notIn resids))
  val opid  = try (operator suchthat (notIn resops))

  (* types *)
  val tyVar = ident wth TVar

  fun tyArr  () = chainr1 ($tyProd) (reservedOp "->" return TArr)
  and tyProd () = chainl1 ($tyApp)  (reservedOp "*"  return TProd)
  and tyApp  () = chainl1 ($tyAt)   (succeed TApp)
  and tyAt   () = tyVar <|> reserved "int" return TInt
                        <|> reserved "bool" return TBool
                        <|> parens  ($tyArr)
  val parseTyp = $tyArr

  val tyann = reservedOp ":" >> parseTyp

  val idop  = !! (identifier when (fn s => Util.lookup (idops, s))) wth Op
  val idval = !! (identifier when (fn s => Util.lookup (idvals, s))) wth BoolL
  val opop  = !! (operator   when (fn s => Util.lookup (opops, s))) wth Op
           <|> !! (reservedOp "*") wth (fn (_, pos) => Op (F.Mul, pos))
           <|> !! (reservedOp "=") wth (fn (_, pos) => Op (F.Eq, pos))

(*      let fun handleI (s, pos) =
              (case (Util.lookup (idops, s), Util.lookup (idexps, s)) of
                   (SOME bop, _) => Op (bop, pos)
                 | (_, SOME f)   => f pos
                 | (NONE, NONE)  => Var (s, pos))
      in !! identifier wth handleI
      end

  val oper =
      let fun handleO (s, pos) =
              (case Util.lookup (opops, s) of
                   SOME bop => Op (bop, pos)
                 | NONE     => Var (s, pos))
      in !! operator wth handleO
         <|> !! (reservedOp "*") wth (fn (_, pos) => Op (F.Mul, pos))
         <|> !! (reservedOp "=") wth (fn (_, pos) => Op (F.Eq, pos))
      end*)

  val arg  = ident
  val targ = parens (arg && tyann)

  val var  = !! (ident <|> opid) wth Var
  val rop  = try (idop <|> opop)

  val hole = !! (char #"#" >> braces (repeat (noneOf [#"}"]))) wth PHole o #2

  fun atKnd () = reservedOp "*" return KTyp <|> parens ($arKnd)
  and arKnd () = chainl1 ($atKnd) (reservedOp "->" return KArr)

  val kindAnn = reservedOp ":" >> $arKnd

  val ctor = ident << reservedOp ":" && (opt (squares (repeat1 ident)) wth Util.maybe (fn x => x) [])
                   && parseTyp wth flat3

  val data = reserved "datatype" >>
             separate1 (!! (ident && kindAnn << reservedOp "=" && separate ctor (reservedOp "|") wth flat3) wth flat4')
               (reserved "and") wth Data

  val pattern = ident && repeat ident

  fun expf ()   =  !! (reserved "fn" >> arg && reservedOp "=>" >> $expf)
                   wth Abs o flat3'
               <|> !! (reserved "let" >> repeat ($decf) && reserved "in" >> $expf << reserved "end")
                   wth Let o flat3'
               <|> !! (reserved "if" >> $expf && reserved "then" >> $expf
                       && reserved "else" >> $expf wth flat3)
                   wth If o flat4'
               <|> !! (reserved "case" >> $expf && reserved "of" >> separate1 ($alt) (reservedOp "|") << reserved "end")
                   wth Case o flat3'
               <|> $annExp
  and annExp () = !! ($appExp && opt tyann) wth (fn ((e, SOME t), p) => PAnn (e, t, p)
                                                  | ((e, NONE), _) => e)
  and appExp () = chainl1 ($atExp) (succeed (App o mergePos))
  and atExp  () =  var <|> !! TP.integer wth IntL <|> try idval <|> rop <|> hole
               <|> !! (reserved "fst" >> $atExp) wth Proj1
               <|> !! (reserved "snd" >> $atExp) wth Proj2
               <|> !! (parens ($expf && opt (comma >> $expf))) wth
               (fn ((e1, oe2), pos) => case oe2 of
                                           NONE => e1
                                         | SOME e2 => Pair (e1, e2, pos))

  and alt () = pattern && reservedOp "=>" >> $expf

  and valrec () = separate1 (!! ((ident <|> opid) && reservedOp "=" >> $expf)
                                wth (fn ((v, e), p) => (v, [], e, p)))
                            (reserved "and")
  and fundef () =  !! ((ident <|> opid) && repeat1 arg && reservedOp "=" >> $expf wth flat3) wth flat4'
  and pfundef () = !! ((ident <|> opid) && squares (repeat ident)
                       && repeat targ && tyann && reservedOp "=" >> $expf wth flat5) wth flat6'

  and valp   () =  reserved "rec" >> $valrec
               <|> !! ((ident <|> opid) && reservedOp "=" >> $expf) wth (fn ((v, e), p) => [(v, [], e, p)])

  and decf   () =  reserved "val" >> $valp wth Fun
               <|> reserved "fun" >>
                     (try (separate1 ($fundef) (reserved "and") wth Fun)
                      <|> (separate1 ($pfundef) (reserved "and") wth PFun))
               <|> data

(*

  (* function arguments *)
  val tyann = TP.reservedOp ":" >> typeP
  val kindann = TP.reservedOp ":" >> kind

  val plainId = ident wth #1

  val args = TP.braces (plainId && tyann) wth Impl
         <|> TP.parens (plainId && opt tyann) wth Expl
         <|> plainId wth (fn x => Expl (x, NONE))

  (* datatypes (just insides, w/o the constructor) *)
  val data = TP.reserved "datatype" >> plainId && kindann << TP.reservedOp "="
          && separate (plainId && tyann) (TP.reservedOp "|") wth flat3

  (* sig declarations *)
  val tdec = !! (TP.reserved "val"  >> plainId && tyann) wth DValDec o flat3'
         <|> !! (TP.reserved "type" >> plainId &&
                (kindann wth Sum.INL <|> TP.reservedOp "=" >> typeP wth Sum.INR))
               wth (fn ((i, Sum.INL k), p) => DTyDec (i, k, p)
                     | ((i, Sum.INR t), p) => DTyDef (i, t, p))
         <|> !! data wth DData o flat4'
         ?? "declaration"

  (* patterns (for now very simple) *)
  val pat = plainId && repeat plainId
  fun mergePosE (e1, e2) = (e1, e2, Pos.union (posE e1) (posE e2))

  fun dec () = !! (TP.reserved "val" >> (opt (TP.reserved "rec") wth Option.isSome) &&
                   plainId && TP.reservedOp "=" >> $bExp)
                 wth (fn ((true,  (i, e)), pos) => ValRecBind (i, e, pos)
                       | ((false, (i, e)), pos) => ValBind (i, e, pos))
            <|> !! (TP.reserved "structure" >> plainId && TP.reservedOp "=" >> $bExp)
                wth (fn ((i, d), pos) => StructDec (i, d, pos))
            <|> !! (TP.reserved "type" >> plainId && TP.reservedOp "=" >> typeP)
                wth (fn ((i, t), pos) => TyDef (i, t, pos))
            <|> !! data wth Data o flat4'
            <|> !! (TP.reserved "fun" >> plainId && repeat1 args && TP.reservedOp "=" >> $bExp)
                wth (fn ((i, (ars, e)), pos) =>
                        ValRecBind (i, List.foldr (fn (a, e) => Fn (a, e, pos)) e ars, pos))
            <|> !! (TP.reserved "signature" >> plainId && repeat (TP.parens (plainId && TP.reservedOp ":" >> kind))
                && TP.reservedOp "=" >> TP.reserved "sig" >> !! (repeat tdec) << TP.reserved "end")
                wth (fn ((i, (ps, dp)), pos) => SigDec (i, ps, TySig dp, pos))

  and bExp () = !! (TP.reserved "fn" >> args && TP.reservedOp "=>" >> $bExp)
                wth Fn o flat3'
            <|> !! (TP.reserved "let" >> repeat1 ($dec) && TP.reserved "in" >> $bExp << TP.reserved "end")
                wth Let o flat3'
            <|> !! (TP.reserved "case" >> $bExp << TP.reserved "of" &&
                separate (pat && TP.reservedOp "=>" >> $bExp) (TP.reservedOp "|") << TP.reserved "end")
                wth Case o flat3'
            <|> $anExp
  and anExp () = !! ($apExp && opt tyann) wth (fn ((e, SOME t), p) => Ann (e, t, p)
                                                | ((e, NONE), _) => e)
  and apExp () = chainl1 ($atExp) (succeed (App o mergePosE))
  and atExp () = idOrLongName wth expOfIol <|> !! TP.integer wth VInt
                  <|> !! (TP.reserved "struct" >> repeat1 ($dec) << TP.reserved "end")
             wth Struct <|> TP.parens ($bExp)
*)

  val exp = whiteSpace >> $expf
  val dec = whiteSpace >> $decf
  val declist = TP.whiteSpace >> repeat dec

  val parseString = CharParser.parseString
  fun debugParse s = outR o parseString s
  val parseExp = CharParser.parseString (exp << eos)
  val parseDec = CharParser.parseString (dec << eos)
  val parseDecList = CharParser.parseString (declist << eos)

  fun parseFile fileName =
      let fun isEol s = (case Stream.front s of Stream.Cons (#"\n", _) => true | _ => false)
          val is = Stream.fromTextInstream (TextIO.openIn fileName)
          val cs = CoordinatedStream.coordinate isEol (Coord.init fileName) is
      in CharParser.parseChars (declist << eos) cs
      end

  end

end
