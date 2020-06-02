
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

(** val isnumericval : term -> bool **)

let rec isnumericval = function
| O -> True
| Succ t1 -> isnumericval t1
| _ -> False

type optiont =
| Some of term
| Value of term
| None

(** val eval1 : term -> optiont **)

let rec eval1 t = match t with
| If (t1, t2, t3) ->
  (match t1 with
   | Tru -> Some t2
   | Fls -> Some t3
   | _ -> (match eval1 t1 with
           | Some t1' -> Some (If (t1', t2, t3))
           | _ -> None))
| Succ t1 ->
  (match isnumericval t1 with
   | True -> Value t
   | False -> (match eval1 t1 with
               | Some t1' -> Some (Succ t1')
               | _ -> None))
| Pred t1 ->
  (match t1 with
   | O -> Some O
   | Succ t1' ->
     (match isnumericval t1' with
      | True -> Some t1'
      | False -> (match eval1 t1' with
                  | Some t1'' -> Some (Pred (Succ t1''))
                  | _ -> None))
   | _ -> (match eval1 t1 with
           | Some t1' -> Some (Pred t1')
           | _ -> None))
| Iszero t1 ->
  (match t1 with
   | O -> Some Tru
   | Succ t1' ->
     (match isnumericval t1' with
      | True -> Some t1'
      | False -> (match eval1 t1' with
                  | Some t1'' -> Some (Pred (Succ t1''))
                  | _ -> None))
   | _ -> (match eval1 t1 with
           | Some t1' -> Some (Pred t1')
           | _ -> None))
| _ -> Value t

(** val bstep : term -> optiont **)

let rec bstep t = match t with
| If (t1, t2, t3) ->
  (match bstep t1 with
   | Value t0 -> (match t0 with
                  | Tru -> bstep t2
                  | Fls -> bstep t3
                  | _ -> None)
   | _ -> None)
| Succ t1 -> (match bstep t1 with
              | Value t0 -> (match t0 with
                             | O -> Value (Succ t1)
                             | _ -> None)
              | _ -> None)
| Pred t1 ->
  (match bstep t1 with
   | Value t0 -> (match t0 with
                  | O -> Value O
                  | Succ t1' -> Value t1'
                  | _ -> None)
   | _ -> None)
| Iszero t1 ->
  (match bstep t1 with
   | Value t0 -> (match t0 with
                  | O -> Value Tru
                  | Succ _ -> Value Fls
                  | _ -> None)
   | _ -> None)
| _ -> Value t
