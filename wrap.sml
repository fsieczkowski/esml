structure Repl =
struct

  datatype comm = ShowAll | ShowOne of int | Focus of int | Unfocus | Clear | Malformed | Holes |
                  Load of string | Refine of int * string | Apply of int * string | Run of string |
                  Case of int * string


  val nh = ref 0
  val fh = ref NONE : int option ref

  val _ = Readline.using_history ()

  fun guardsz n f = if n < !nh then f () else print ("(error \"Error: No such hole.\")\n")
  fun guard n = guardsz n (fn () => ())
  fun focused () = isSome (!fh)

  fun exec ShowAll     = print ("(ok \"" ^ Top.showHoles () ^ "\")\n")
    | exec (ShowOne n) = guardsz n (fn () => print ("(ok \"" ^ Top.showHole n ^ "\")\n"))
    | exec (Focus   n) = guardsz n (fn () => fh := SOME n)
    | exec Unfocus     = if focused () then fh := NONE else print ("(error \"Error: No focused hole.\")\n")
    | exec Clear       = (Top.clear (); nh := Top.numHoles ())
    | exec Malformed   = print ("(error \"Error: Malformed command.\")\n")
    | exec Holes       = print (Top.getHolesPos () ^ "\n")
    | exec (Load    s) = (Top.clear (); Top.runFile s; nh := Top.numHoles ())
    | exec (Refine ns) =
      (let val _ = guard (#1 ns)
           val hc = Top.refineHole ns
           val _ = (nh := !nh + hc - 1; fh := NONE)
       in print ("(ok \"\")\n")
       end handle Top.Err s => print ("(error \"" ^ s ^ "\")\n"))
    | exec (Apply  ns) =
      (let val _ = guard (#1 ns)
           val (hc, re) = Top.applyHole ns
           val _ = (nh := !nh + hc - 1; fh := NONE)
       in print ("(ok \"(" ^ TAst.ppexp [] 2 re ^ ")\")\n")
       end handle Top.Err s => print ("(error \"" ^ s ^ "\")\n"))
    | exec (Case   ns) =
      (let val _ = guard (#1 ns)
           val (hc, re) = Top.refineCase ns
           val _ = (nh := !nh + hc - 1; fh := NONE)
       in print ("(ok \"(" ^ TAst.ppexp [] 2 re ^ ")\")\n")
       end handle Top.Err s => print ("(error \"" ^ s ^ "\")\n"))
    | exec (Run s)     = (Top.runReplExp s; nh := Top.numHoles ())

  fun parseInput s =
      let open Sum
          open ParserCombinators
          open CharParser
          infixr 4 << >>
          infixr 3 &&
          infix  2 -- ##
          infix  2 wth suchthat return guard when
          infixr 1 || <|> ??

          val rest    = repeat anyChar wth String.implode
          val str     = char #"\"" >> repeat (noneOf [#"\""]) << char #"\"" wth String.implode
          val number  = repeat1 digit wth (valOf o Int.fromString o String.implode)
          val numFoc  = (number << spaces <|> (if focused () then succeed (valOf (!fh))
                                               else fail "Expected a number."))
          val showall = try (string ":showAll" return ShowAll)
          val showOne = try (string ":show") >> spaces >> numFoc << spaces wth ShowOne
          val focus   = try (string ":focus") >> spaces >> number wth Focus
          val unfocus = try (string ":unfocus" return Unfocus)
          val holes   = try (string ":holes" return Holes)
          val clear   = try (string ":clear" return Clear)
          val load    = try (string ":load") >> spaces >> str wth Load
          val pmatch  = try (string ":case") >> spaces >> numFoc && rest wth Case
          val refine  = try (string ":refine") >> spaces >> numFoc && rest wth Refine
          val apply   = try (string ":apply") >> spaces >> numFoc && rest wth Apply
          val expr    = rest wth Run
          val all     = showall <|> showOne <|> focus <|> unfocus <|> holes <|> clear <|> load <|> refine <|> apply <|> pmatch <|> expr
      in case parseString (all << spaces << eos) s of
             INL errs => Malformed
           | INR cmd  => cmd
      end

  fun header () =
      (case (!fh) of
           NONE => "-" ^ Int.toString (!nh) ^ "-> "
         | SOME k => "** @" ^ Int.toString k ^ " / " ^ Int.toString (!nh) ^ " *> ")

  fun repl () =
      (case Readline.readline (header ()) of
           NONE => print "\n"
         | SOME s =>
           let val cmd = parseInput s
           in (if cmd <> Malformed then Readline.add_history s else ());
              exec cmd;
              repl ()
           end)


end

val _ = Repl.repl ()
