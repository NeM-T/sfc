(*2.2モーダスポネントの形式化*)
From mathcomp
     Require Import ssreflect.

Section ModusPonens.
  Variables X Y : Prop.

  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.

  Theorem MP : Y.
    apply XtoY_is_true.
    by [].
   Qed.

End ModusPonens.


(*2.3ヒルベルトの公理Sの形式化*)
Section HilbertSAxiom.
  Variable A B C : Prop.

  Theorem HS1 : (A -> (B -> C)) -> ( (A -> B) -> (A -> C)).
  Proof.
    move => AtoBtoC.
    move => AtoB.
    move => AisTrue.

    apply (MP B C).

    apply (MP A (B -> C)).
      by [].
      by [].

    apply: (MP A B).
      by [].
      by [].
  Qed.

End HilbertSAxiom.


From mathcomp
     Require Import ssrnat.
Section natNumber.

  Lemma add0n (n: nat) : 0 + n = n.
  Proof. by []. Qed.

  Lemma add3n21n (n: nat) : n + 3 = 2 + n + 1.
  Proof. rewrite addn1. rewrite add2n. rewrite addnC. reflexivity. Qed.

  Fixpoint sum n := if n is m.+1 then sum m + n else 0.

  Lemma sumGauss (n: nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim : n => [// | n IHn].
    rewrite mulnC.
    rewrite (_: sum (n.+1) = n.+1 + (sum n)); last first.
    rewrite /=. by rewrite addnC.
    rewrite mulnDr. rewrite mulnC in IHn.
    rewrite IHn.
    rewrite 2!addn1.
    rewrite [_ * n]mulnC.
    rewrite <- mulnDl. by [].
  Qed.

End natNumber.


Set Implicit Types Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defesive.

Section Logic.

  Lemma contrap : forall A B: Prop, (A -> B) -> (~B -> ~A).
  Proof.
    unfold not. intros. apply H in H1. apply H0 in H1. assumption.
  Qed.


  Variables A B C: Prop.

  Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    rewrite /iff. apply: conj.
    -case.
     +case=> ATrue CTrue. by apply: conj; [apply or_introl | ].
     +case=> BTrue CTrue. by apply: conj; [apply or_intror | ].
    -case=> AorB CTrue.
     case: AorB => [ATrue | BTrue].
     +by apply: or_introl.
     +by apply: or_intror.
  Qed.


  Lemma JDM (T: Type) (P: T -> Prop):
    ~(exists (x: T), P x) <-> forall x, ~(P x).
  Proof.
    apply conj => Hyp.
    - move => x0 HPx0.
      apply: Hyp. by apply: (ex_intro P x0).
    - by case.
  Qed.


  Hypothesis ExMidLaw : forall P: Prop, P \/ ~P.

  Lemma notnotEq (P: Prop) : ~ ~ P -> P.
  Proof.
    move=> HnotnotP.
    - case: (ExMidLaw (~P)).
      + by move /HnotnotP.
      + by case: (ExMidLaw P).
  Qed.

End Logic.

Hypothesis ExMidLaw : forall P: Prop, P \/ ~P.

Theorem Dom1 : forall A B,  not (A /\ B) <-> not A \/ not B.
Proof.
  split; intros.
  - destruct (ExMidLaw A); destruct (ExMidLaw B); try (left; assumption); try (right; assumption).
    + induction H. split; assumption.
  - intro H0. inversion H0. destruct H; apply H; assumption.
Qed.


Lemma notnoteq (P: Prop) : ~ ~ P -> P.
Proof.
  move=> HnotnotP.
  - case: (ExMidLaw (~P)).
    + by move /HnotnotP.
    + by case: (ExMidLaw P).
Qed.


Theorem Dom2: forall (T: Type) (P: T -> Prop), not (forall x, P x) <-> (exists x, not (P x) ).
Proof.
  split; intros.
  - apply notnoteq. intros H0. apply H. intro. apply notnoteq. intro. apply H0. exists x. assumption.
  - inversion H. intros H1. specialize (H1 x). apply H0; assumption.
Qed.

