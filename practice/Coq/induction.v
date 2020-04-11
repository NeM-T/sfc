From LF Require Export CaseAnalysis.
From LF Require Export dataANDfunction.
From LF Require Export rewrite.



Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.


Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.  induction n as [| n' IHn].
  - reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


Theorem neg_twice : forall b :bool,
  negb( negb ( b)) = b.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.  induction n as [| n' IHn].
  - reflexivity.
  - rewrite IHn. simpl.
    rewrite -> (neg_twice (evenb n')).
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. 
Qed.

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



Theorem eq_succ : forall n m : nat,
  (eqb n m) = (eqb (S n) (S m)).
Proof.
  intros n m. simpl. reflexivity.
Qed.

Theorem true_eq : forall n : nat,
  (eqb n n) = true.
Proof.
  intros n. induction n as [| n' IHn].
  - 
    reflexivity.
  - rewrite <- (eq_succ n' n').
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. induction n as [| n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn.
    rewrite (plus_n_Sm m (n' + p)).
    reflexivity.
Qed.

Theorem succ_time : forall n m: nat,
   m + m * n = m * S n.
Proof.
  intros n m. induction m as [| m' IH].
  - reflexivity.
  - simpl. rewrite plus_swap. rewrite IH. 
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. induction n as [| n IH].
  - simpl. 
    assert (H: m *0 = 0).
    {induction m as [| m' IHm].
      - reflexivity.
      - simpl. rewrite IHm. reflexivity. }
    rewrite H. reflexivity.
  - simpl. rewrite IH.
    rewrite succ_time. reflexivity.
Qed.


Theorem eqb_refl : forall n : nat,
  true = (eqb n n). 
Proof.
  intros n. induction n.
  reflexivity. rewrite <- eq_succ.
  rewrite IHn. reflexivity.
Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => S( S O) * bin_to_nat m'
  | B m' => S O + S(S O) * bin_to_nat m'
  end.

Compute (bin_to_nat (A(B(B Z)))).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B m' => A ( incr m')
  | A m' => B m'
  end.

Theorem bin_to_nat_pres_incr : forall n : bin ,
  S (bin_to_nat n) = bin_to_nat (incr n).
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. 
    rewrite <- plus_n_O. rewrite plus_n_Sm. 
    rewrite plus_comm. rewrite plus_n_Sm.
    rewrite IHn.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr(nat_to_bin n')
  end.

Compute (nat_to_bin (S (S (S (S (S O)))))).

Theorem nat_bin_nat : forall n,
   bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn.
    rewrite bin_to_nat_pres_incr.
    rewrite -> IHn. reflexivity.
Qed.














