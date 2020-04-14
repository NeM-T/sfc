
Set Warnings "-notation-overridden,-parsing".
From LF Require Export poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. Qed.


Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros Hn H3. rewrite <- H3. rewrite Hn. reflexivity. reflexivity.
Qed.


(*symmetry : =項の 左辺と右辺の入れ替え。*)
Theorem silly3_firsttry : forall (n : nat),
     true = (n == 5) ->
     (S (S n)) == 7 = true.
Proof.
  intros n H1.   symmetry. simpl. apply H1.
Qed.

Theorem rev_doble : forall (l : list nat),
  rev (rev l) = l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l1 l2 H. rewrite H. rewrite rev_doble. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c;d].
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2. rewrite H2. apply H1. 
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.


Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.  injection H. intros Hnm. apply Hnm.
Qed.


Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2. injection H2. intros Hin. symmetry. apply H.
Qed.

Theorem eqb_0_l : forall n,
   0 == n = true -> n = 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  -
    intros H. reflexivity.
  -
    simpl.  intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
 
Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H. discriminate H. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) == (S m) = b ->
     n == m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (n == 5 = true -> (S (S n)) == 7 = true) ->
  true = (n == 5) ->
  true = ((S (S n)) == 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.


Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.

  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + simpl. discriminate eq.
    + apply f_equal.
      apply IHn'. injection eq as goal. apply goal. Qed.

Theorem succ_eq : forall n m,
  S n = S m -> n = m.
Proof.
  intros [] []. reflexivity. discriminate. discriminate.
  intros H. injection H as goal. rewrite goal. reflexivity.
Qed.

Theorem eqb_true : forall n m,
    n == m = true -> n = m.
Proof.
  intros n . induction n.
  - simpl. intros [].   reflexivity. discriminate.
  - intros m . destruct m.
    + discriminate.
    + simpl. intros H. apply IHn in H. rewrite H.
      reflexivity.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h t IH].
  - intros.
    rewrite <- H.
    reflexivity.
  - intros.
    rewrite <- H.
    simpl.
    apply IH.
    reflexivity.
Qed.

Definition square n := n * n.


Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n == 3 then false
  else if n == 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n == 3) eqn:E1.
    - reflexivity.
    - destruct (n == 5) eqn:E2.
      + reflexivity.
      + reflexivity. Qed.


Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem tail_eq: forall (X: Type) (h: X) (l1 l2: list X),
    l1 = l2 -> h :: l1 = h :: l2.
Proof.
  intros. apply f_equal. apply H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| h t IH].
   - intros. simpl in H. inversion H. reflexivity. 
   - intros l1 l2 H. inversion H. destruct h. 
     destruct (split t). inversion H1.     simpl.
     apply tail_eq. apply IH. reflexivity.
Qed.


Definition sillyfun1 (n : nat) : bool :=
  if n == 3 then true
  else if n == 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n == 3) eqn:Heqe3.
    - apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - destruct (n == 5) eqn:Heqe5.
        +
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + discriminate eq. Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f []. 
   destruct (f true) eqn:fT. 
     - rewrite fT. rewrite fT. reflexivity.
     -  destruct (f false) eqn: fF.
        + rewrite fT. reflexivity.
        + rewrite fF. reflexivity.
     - destruct (f false) eqn:fF.
       + destruct (f true ) eqn:fT. rewrite fT. reflexivity.
        rewrite fF. reflexivity.
       + rewrite fF. rewrite fF. reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n == m) = (m == n).
Proof.
  intros n. induction n.
    - intros. induction m. + reflexivity. + reflexivity.
    - induction m. + reflexivity. + simpl. rewrite IHn. reflexivity.
Qed.

Theorem eqb_trans : forall n m p,
  n == m = true ->
  m == p = true ->
  n == p = true.
Proof.
   intros.  apply eqb_true in H. apply eqb_true in H0. induction H0. induction H. apply true_eq.
Qed.



Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: t => if (test h) then forallb test t else false
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => false
  | h :: t => if (test h) then true else existsb test t
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
   negb (forallb (fun x => negb (test x)) l) .

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros. unfold existsb'. unfold existsb. induction l. - simpl. reflexivity.
  - simpl. destruct (test x). 
     + simpl. reflexivity.
     + simpl. rewrite IHl. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n m. rewrite <- double_plus. rewrite <- double_plus. Search double. apply double_injective.
Qed.

(*-------------------------------*)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros.
  generalize dependent lf.
  induction l as [| h t IH].
  - intros.
    simpl in H.
    inversion H.
  - intros.
    generalize dependent H.
    destruct lf as [| hf tf].
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.
        apply testH.
      * apply IH in H.
        apply H.
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.
        apply testH.
      * apply IH in H.
        apply H.
Qed.


