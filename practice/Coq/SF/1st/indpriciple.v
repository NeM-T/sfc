Set Warnings "-notation-overridden,-parsing".
From LF Require Export proofobject.

(*帰納法の定義*)
Check nat_ind. (*forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P na*)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind. (*これで帰納法できる*)
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof. intros. apply plus_comm. Qed.

(*自作の型にも_indができる*)
Inductive yesno : Type :=
  | yes
  | no.
Check yesno_ind.

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).
Check natlist_ind.


Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).
Check natlist1_ind.

Inductive byntree : Type :=
 | bempty
 | bleaf (yn : yesno)
 | nbranch (yn : yesno) (t1 t2 : byntree).
Check byntree_ind.

Inductive ExSet : Type :=
| con1 (b: bool)
| con2 (n: nat) (e: ExSet).
Check ExSet_ind.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
Check list_ind.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.

Inductive mytype (X: Type) : Type :=
| constr1 (x: X)
| constr2 (n: nat)
| constr3 (m: mytype X) (n: nat).
Check mytype_ind.


Inductive foo (X Y : Type) : Type :=
| bar (x: X)
| baz (y: Y)
| quux (f1: nat -> foo X Y) {n: nat}.
Check foo_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.
Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.
Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  -
    
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - reflexivity.
  -
    
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_co : forall n m,
    n + m = m + n.
Proof.
   intros n. apply nat_ind.
  - rewrite <- plus_n_O. reflexivity.
  - intros m H. simpl. rewrite <- plus_n_Sm. rewrite H. reflexivity.
Qed.

Theorem plus_asc : forall n m p ,
    n + (m + p) = (n + m) + p.
Proof.
 intros n m. apply nat_ind.
 - rewrite <- plus_n_O. rewrite <- plus_n_O. reflexivity.
 - intros p H. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite H.
   reflexivity.
Qed.


Check even_ind.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem ev_ev' : forall n, even n -> even' n.
Proof.
  apply even_ind.
  - 
    apply even'_0.
  -
    intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intros n. split.
  - apply even'_ind.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + intros m p H0 H1 H2 H3. apply (ev_sum m p H1 H3).
  - apply ev_ev'.
Qed.


Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m H H1. induction H1.
  - simpl in H. apply H.
  - simpl in H. inversion H. apply IHeven in H2. apply H2.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).
Check le_ind.
