structure Def =
struct
  datatype term =
            Var of int
          | Abs of term
          | App of term * term

  fun shift c d (Var n)   = if n < c then Var n else Var (n + d)
    | shift c d (Abs t)   = Abs (shift (c + 1) d t)
    | shift c d (App (n, m)) = App ((shift c d n), (shift c d m))

  fun subst j s (Var n)      = if n = j then s else (Var n)
    | subst j s (Abs t)      = Abs (subst (j + 1) (shift 0 1 s) t)
    | subst j s (App (n, m)) = App (subst j s n, subst j s m)

  fun optfun f x g = case (f x) of
                        SOME y => SOME (g y)
                      | NONE => NONE

  fun beta t = case t of
                    (App (Abs n, m)) => 
                      (case m of
                            Abs _ => SOME (shift 0 ~1 (subst 0 (shift 0 1 m) n))
                          | _ => optfun beta m (fn x => App (n, x)))
                  | (App (n, m)) => optfun beta n (fn x => App (x, m))
                  | _ => NONE
end
