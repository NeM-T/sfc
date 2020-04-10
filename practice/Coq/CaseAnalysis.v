
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

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.


Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.


Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] c H.
  apply H. discriminate H.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [| n] .
  - reflexivity.
  - reflexivity.
Qed.



(* ------------------------------- *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  reflexivity.
Qed.

From Coq Require Export String.



Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.


Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. 
  intros b c.
  destruct b eqn:Eb.
     - destruct c eqn:Ec.
     reflexivity.
     discriminate.
     - destruct c eqn:Ec.
     discriminate.
     reflexivity.
Qed.


Theorem andb_eq_orb' :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. 
  intros a b H.
  destruct a.
  rewrite <- (andb_true_elim2 true b).
  reflexivity.
  apply H. 
  apply H.
Qed.



Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B m' => A ( B m')
  | A m' => B m'
  end.

Example test_inc1: (incr Z) = B Z.
Proof. simpl. reflexivity. Qed.
Example test_inc2: (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_inc3: (incr (A (B (B Z)))) = B (B (B Z)).
Proof. simpl. reflexivity. Qed.


(*
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B Z => S O
  | A m' => S (  )
  | B m' => 
  end.
*)

