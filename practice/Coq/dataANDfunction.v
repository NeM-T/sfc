Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(* ------------------------------ *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb  x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
(* ----------------------------- *)

Check true.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Module NatPlayground.
  (* With this definition, 0 is represented by O, 1 by S O, 2 by S (S O), and so on. *)
  Inductive nat : Type :=
    | O
    | S (n : nat).

End NatPlayground.

Module NatPlayground2.

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint exp (base power : nat) : nat :=
    match power with
      | O => S O
      | S p => mult base (exp base p)
    end.
  Compute (exp 2 4).

  Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S p => mult (S p) (factorial p)
    end.

  Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.
  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.

  Notation "x + y" := (plus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x - y" := (minus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x * y" := (mult x y)
                         (at level 40, left associativity)
                         : nat_scope.

  Check ((0 + 1) + 1).

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.



  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.

  Notation "x =< y" := (leb x y)
                         (at level 70): nat_scope.
  Notation "x =? y" := (eqb x y) 
                         (at level 70) : nat_scope.

  Example test_leb1: (2 =< 2) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb2: (2 =< 4) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb3: (4 =< 2) = false.
  Proof. simpl. reflexivity. Qed.



  Fixpoint ltb (n m : nat) : bool :=
    match n with 
    | O =>    match m with
              | O => false
              | S _ => true
              end
    | S n' => match m with
              | O => false
              | S m' => ltb n' m'
              end
    end.

  Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

  Example test_ltb1: (2 <? 2) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb2: (2 <? 4) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb3: (4 <? 2) = false.
  Proof. simpl. reflexivity. Qed.


End NatPlayground2.

