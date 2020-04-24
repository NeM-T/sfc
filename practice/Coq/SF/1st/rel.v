Set Warnings "-notation-overridden,-parsing".
From LF Require Export indprop.
Definition relation (X: Type) := X -> X -> Prop.
Check le : nat -> nat -> Prop.
Check le : relation nat.

(*部分関数*)
Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.


Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Check total_relation : relation nat.

Theorem not_partial_total_relation :
  ~(partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros.
  assert (0 = 1) as Nonsense. {
    apply H with (x:= 0) (y1:= 0) (y2:= 1).
    - apply tot. - apply tot. }
  discriminate Nonsense.
Qed.

Inductive empty_relation : nat -> nat -> Prop := .

Theorem not_partial_empty_relation :
  partial_function empty_relation.
Proof.
  unfold partial_function. intros x y1 y2 H1 H2.
  inversion H1. Qed.


(*反射的関係*)
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

(*推移的関係*)
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo. apply Hnm. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.


Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hnm.
  - apply le_leftS in Hmo. apply Hmo.
  - apply IHHnm. apply le_leftS. apply Hmo.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_S. apply IHo'.
    Abort.


Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros. inversion H.
  - apply le_n.
  - apply le_Sn_le in H2. apply H2.
Qed.

Theorem not_le_Sn_n : forall n, ~(S n <= n).
Proof.
  unfold not. intros. induction n.
  - inversion H.
  - apply IHn. apply le_S_n in H. apply H.
Qed.


(*対称的関係*)
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros.
  assert (1 <= 0) as Nonsense. {
    apply H with (a:= 0) (b:= 1). apply le_S. apply le_n. }
  inversion Nonsense.
Qed.


(*反対称的関係*)
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  intros a b.
  generalize dependent a.
  induction b.
  intros a.
  intros H.
  intros H1.
  inversion H.
  reflexivity.

  intros a H1 H2.
  destruct a.
  inversion H2.

  apply Sn_le_Sm__n_le_m in H1.
  apply Sn_le_Sm__n_le_m in H2.
  apply IHb in H1.
  rewrite H1.
  reflexivity.

  apply H2.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt. intros. apply Sn_le_Sm__n_le_m. apply le_trans with m. apply H. apply H0.
Qed.

(*同値関係*)
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(*半順序関係*)
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(*全順序関係*)
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - apply le_reflexive.
    - split.
      + apply le_antisymmetric.
      + apply le_trans. Qed.

(*反射推移閉包
Rを含み反射性と推移性の両者を満たす最小の関係 *)
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.


Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  -
    intro H. induction H.
    + apply rt_refl.
    +
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  -
    intro H. induction H.
    + inversion H. apply le_S. apply le_n.
    + apply le_n.
    +
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

(*より使いやすい定義*)
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros. induction H. apply H0. apply rt1n_trans with (y0:= y). apply Hxy. apply IHclos_refl_trans_1n.
  apply H0.
Qed.

Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  
  intros. split.
  - intros. induction H. apply rt1n_trans with (y0 := y). apply H. apply rt1n_refl. apply rt1n_refl.
    apply rsc_trans with (y:= y).  apply IHclos_refl_trans1. apply IHclos_refl_trans2.
  - intros. induction H. apply rt_refl. apply rt_trans with (y0:= y).
    apply rt_step in Hxy. apply Hxy. apply IHclos_refl_trans_1n.
Qed.
