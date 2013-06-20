structure Util =
struct

  exception Impossible

  fun lookup ([], x) = NONE
    | lookup ((k, v) :: M, x) = if k = x then SOME v
                                else lookup (M, x)

  fun maybe s n (SOME v) = s v
    | maybe s n NONE = n

  fun takeDrop (n, xs) =
      let fun aux (0, xs, ys) = (rev ys, xs)
            | aux (n, x :: xs, ys) = aux (n - 1, xs, x :: ys)
            | aux _ = raise Subscript
      in aux (n, xs, [])
      end

end
