Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Require Import hoare.
Require Import imp.

Definition reduce_to_zero' : com :=
  (WHILE ~(X = 0) DO
    X ::= X - 1
  END)%imp.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  apply hoare_while.
  -
    
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st [HT Hbp]. unfold assn_sub. constructor.
  -
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse. Qed.


Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE 2 <= X DO
    X ::= X - 2
  END
    {{ fun st => st X = parity m }}.
Proof.
  unfold hoare_triple. intros. inversion H; subst. symmetry. apply parity_lt_2.
  unfold not. intros. simpl in H5. induction (st' X). inversion H0. induction n. inversion H0. inversion H2. inversion H5.
Abort.

