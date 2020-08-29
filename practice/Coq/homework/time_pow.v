Notation add := ((fun m n x y => m x (n x y))).
Notation time := ((fun m n x y => m (n x) y)).
Notation two := (fun s n => s (s n)).
Notation thr := (fun s n => s (s (s n))).
Compute (add two thr S O) (*=> 5*).
Compute (time two thr S O) (*=> 6*).

Fixpoint fn_walk n (s: nat -> nat) z :=
  match n with
  | O => z
  | S n' => s (fn_walk n' s z)
  end.

Definition fun_nat n :=
  (fun s z => fn_walk n s z).

Lemma fun_nat_correct : forall n,
    fun_nat n S O = n.
Proof.
  induction n; simpl; auto.
Qed.

Notation adds n1 n2 := (add (fun_nat n1) (fun_nat n2)).
Notation times n1 n2 := (time (fun_nat n1) (fun_nat n2)).

Lemma add_correct : forall n m,
    adds n m = fun_nat (n + m).
Proof.
  unfold fun_nat; induction n; simpl; intros; auto.
  rewrite <- IHn. reflexivity.
Qed.

Theorem time_correct : forall n1 n2,
    times n1 n2 = fun_nat (n1 * n2).
Proof.
  induction n1; simpl; auto; intros.
  rewrite <- add_correct. rewrite <- IHn1.
  reflexivity.
Qed.


Fixpoint walk {A: Type} n (s: A -> A) z :=
  match n with
  | O => z
  | S n' => s (walk n' s z)
  end.

Definition fun_nat2 {A: Type} n :=
  (fun (s: A -> A) z => walk n s z).

Notation power := ((fun m n x y => n m x y)).
Notation powers n1 n2 := (power (fun_nat2 n1)(fun_nat2 n2)).
Compute (power two thr S O).

Fixpoint pow n1 n2 :=
  match n2 with
  | 0 => 1
  | S n => n1 * (pow n1 n)
  end.
Compute (pow 3 2).
Compute (pow 2 3).

Lemma pow_m_sn : forall n m,
    pow m (S n) = m * (pow m n).
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma walk__ : forall n,
    walk n = fn_walk n.
Proof.
  induction n; simpl; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma fun_nat12 : forall n,
    fun_nat n = fun_nat2 n.
Proof.
  unfold fun_nat, fun_nat2.
  intros. rewrite walk__. reflexivity.
Qed.

Theorem power_correct: forall n2 n1,
    powers n1 n2 = fun_nat (pow n1 n2).
Proof.
  induction n2; simpl; intros; auto.
  rewrite IHn2. rewrite <- time_correct. rewrite <- fun_nat12. reflexivity.
Qed.

Theorem power2 : forall n2 n1,
    fun_nat2 (pow n1 n2) = ((fun_nat2 n2) (time (fun_nat n1)) (fun_nat 1)).
Proof.
  induction n2; intros; simpl; auto.
  rewrite <- IHn2. repeat rewrite <- fun_nat12. rewrite time_correct. reflexivity.
Qed.
