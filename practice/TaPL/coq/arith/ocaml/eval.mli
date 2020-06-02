
type bool =
| True
| False

type term =
| Tru
| Fls
| If of term * term * term
| O
| Succ of term
| Pred of term
| Iszero of term

val isnumericval : term -> bool

type optiont =
| Some of term
| Value of term
| None

val eval1 : term -> optiont

val bstep : term -> optiont
