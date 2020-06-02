Require Coq.extraction.Extraction.
Extraction Language OCaml.

Inductive term : Type :=
| tru
| fls
| If (t1 t2 t3: term)
| O
| succ (t1: term)
| pred (t1: term)
| iszero (t1: term).


Fixpoint isnumericval (t: term): bool :=
  match t with
  | O => true
  | succ t1 => isnumericval t1
  | _ => false
  end.

Fixpoint isval (t: term) : bool :=
  match t with
  | tru => true
  | fls => true
  | _ => isnumericval t
  end.

Inductive optiont : Type :=
| Some (t: term)
| value (t: term)
| None.

Fixpoint eval1 (t: term) : optiont :=
  match t with
  | If t1 t2 t3 =>
    match t1 with
    | tru => Some t2
    | fls => Some t3
    | _ => match (eval1 t1) with
           | Some t1' => Some (If t1' t2 t3)
           | _ => None
           end
    end
  | succ t1 =>
    if isnumericval t1 then
      value t else
      match (eval1 t1) with
      | Some t1' => Some (succ t1')
      | _ => None
      end
  | pred t1 =>
    match t1 with
    | O => Some O
    | succ t1' =>
      if isnumericval t1' then
        Some t1' else
        match (eval1 t1') with
        | Some t1'' => Some (pred (succ t1''))
        | _ => None
        end
    | _ => match (eval1 t1) with
           | Some t1' => Some (pred t1')
           | _ => None
           end
    end
  | iszero t1 =>
    match t1 with
    | O => Some tru
    | succ t1' =>
      if isnumericval t1' then
        Some t1' else
        match (eval1 t1') with
        | Some t1'' => Some (pred (succ t1''))
        | _ => None
        end
    | _ => match (eval1 t1) with
           | Some t1' => Some (pred t1')
           | _ => None
           end
    end
  | _ => value t
  end.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Theorem eval1value : forall t1,
    eval1 t1 = value t1 <-> isval t1 = true.
Proof.
  split; intros.
  -
    induction t1; try reflexivity.
    + inversion H.
      destruct t1_1; try solve_by_invert.
      induction (eval1 (If t1_1_1 t1_1_2 t1_1_3)); try solve_by_invert.
      destruct (eval1 (succ t1_1)); try solve_by_invert.
      destruct (eval1 (pred t1_1)); try solve_by_invert.
      destruct (eval1 (iszero t1_1)); try solve_by_invert.
    + inversion H.
      simpl.
      destruct (isnumericval t1)eqn:IH; auto.
      destruct (eval1 t1); inversion H1.
    + inversion H.
      destruct t1; try solve_by_invert.
      destruct (eval1 (If t1_1 t1_2 t1_3)); try solve_by_invert.
      destruct (isnumericval t1). inversion H1.
      destruct (eval1  t1); inversion H1.
      destruct (eval1 (pred t1)); inversion H1.
      destruct (eval1 (iszero t1)); inversion H1.
    + inversion H.
      destruct t1; try solve_by_invert.
      destruct (eval1 (If t1_1 t1_2 t1_3)); try solve_by_invert.
      destruct (isnumericval t1). inversion H1.
      destruct (eval1  t1); inversion H1.
      destruct (eval1 (pred t1)); inversion H1.
      destruct (eval1 (iszero t1)); inversion H1.
  -
    induction t1; try reflexivity; try solve_by_invert.
    + simpl. inversion H. rewrite H1. reflexivity.
Qed.

Fixpoint bstep (t: term) : optiont :=
  match t with
  | tru => value t
  | fls => value t
  | O => value t
  | If t1 t2 t3 =>
    match (bstep t1) with
    | value tru => bstep t2
    | value fls => bstep t3
    | _ => None
    end
  | succ t1 =>
    match (bstep t1) with
    | value O => value (succ t1)
    | _ => None
    end
  | pred t1 =>
    match (bstep t1) with
    | value (succ t1') => value t1'
    | value O => value O
    | _ => None
    end
  | iszero t1 =>
    match (bstep t1) with
    | value O => value tru
    | value (succ _) => value fls
    | _ => None
    end
  end.

Extraction "ocaml/eval.ml" eval1 bstep.
