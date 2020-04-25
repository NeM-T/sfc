Section SetTheory.

Require Import Ensembles. (*集合論のライブラリ*)
Require Import Classical.

(*集合の定義
Variable U : Type.
Definition Ensemble := U -> Prop.*)

(*要素関係
Definition In (A:Ensemble) (x:U) : Prop := A x.*)

(*
集合の包含関係の定義である．
Definition Included (B C:Ensemble) : Prop := forall x:U, In B x -> In C x.*)

(*全体集合と空集合の定義である．*)
(*Inductive Full set : Ensemble := Full intro : forall x:U, In Full set x.
Inductive Empty set : Ensemble :=.*)
(*Definitionだと以下
Definition Full set : Ensemble := fun x:U=>True.
Definition Empty set : Ensemble := fun x:U=>False.*)

(*集合に関する演算の和集合 (union)∪，共通部分 (intersection)

Inductive Union (B C:Ensemble) : Ensemble :=
| Union introl : forall x:U, In B x -> In (Union B C) x
| Union intror : forall x:U, In C x -> In (Union B C) x.

Inductive Intersection (B C:Ensemble) : Ensemble :=
Intersection intro : forall x:U,
  In B x -> In C x -> In (Intersection B C) x.*)


Ltac ok:= trivial; contradiction.
Ltac hairihou := apply NNPP; intro.

Variable U : Type.
Notation Shugo := (Ensemble U).
Notation "x ∈ A":=(In U A x)(at level 55,no associativity).
Notation "A ⊆ B":=(Included U A B)(at level 54, no associativity).
Notation "A ∩ B":=(Intersection U A B)(at level 53, right associativity).
Notation "A ∪ B" :=(Union U A B)(at level 53, right associativity).
Notation Ω:=(Full_set U).
Notation ø :=(Empty_set U).

Lemma in_or_not : forall A, forall x,
      (x ∈ A) \/ ~(x ∈ A).
Proof. intros; apply classic. Qed.

Lemma bubun_transitive : forall A B C,
    (A ⊆ B) /\ (B ⊆ C) -> A ⊆ C.
Proof. unfold Included. intros. destruct H as [H H1]. apply H1. apply H. ok. Qed.

Ltac bubun := unfold Included; intros.

Lemma empty_bubun : forall A, ø ⊆ A. 
Proof. bubun.  destruct H. Qed.

Lemma bubun_full : forall A, A ⊆ Ω.
Proof. bubun. apply Full_intro. Qed.

Ltac seteq := apply Extensionality_Ensembles; unfold Same_set; split.

Lemma Union_aa : forall A, A ∪ A = A.
Proof. intros. seteq. bubun.
       inversion H. apply H0. apply H0.
       bubun. apply Union_introl. apply H.
Qed.

Lemma Union_comm : forall A B, A ∪ B = B ∪ A.
Proof. intros. seteq; bubun;
       destruct H; try (apply Union_intror; apply H); try (apply Union_introl; apply H).
Qed.

Lemma Union_3 : forall A B C, A ∪ ( B ∪ C ) = (A ∪ B) ∪ C.
Proof. intros. seteq; bubun. induction H. repeat (apply Union_introl). apply H. induction H. apply Union_introl.
       apply Union_intror. apply H. apply Union_intror. apply H.
       induction H. induction H. apply Union_introl. apply H. apply Union_intror. apply Union_introl. apply H.
       repeat (apply Union_intror). apply H.
Qed.

Lemma bubun_AB_A : forall A B, A ⊆ (A ∪ B).
Proof. intros. bubun. apply Union_introl. apply H. Qed.

Lemma bubun_AB_B : forall A B, B ⊆ (A ∪ B).
Proof. intros. bubun. apply Union_intror. apply H. Qed.

Lemma bubun_3 : forall A B C, A ⊆ C -> B ⊆ C -> A ∪ B ⊆ C.
Proof. bubun. inversion H1. apply H. apply H2. apply H0. apply H2. Qed.

Lemma and_AA : forall A, A ∩ A = A.
Proof. intros. seteq. bubun. inversion H. apply H0. bubun. split; apply H. Qed.

Lemma and_comm : forall A B, A ∩ B = B ∩ A.
Proof. intros. seteq; bubun; inversion H; split; assumption. Qed.

Lemma and_3 : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. intros. seteq. bubun. inversion H as [H0  H1]; inversion H2. repeat (split); assumption.
       bubun. destruct H. destruct H. repeat (split); assumption. Qed.

Lemma and_ABA : forall A B, A ∩ B ⊆ A.
Proof. intros. bubun. inversion H. apply H0. Qed.

Lemma and_ABB : forall A B, A ∩ B ⊆ B.
Proof. intros. bubun. inversion H. apply H1. Qed.

Lemma and_CAB : forall A B C, C ⊆ A -> C ⊆ B -> C ⊆ A ∩ B.
Proof. intros. split. apply H in H1. assumption. apply H0 in H1. assumption. Qed.

Lemma and_In_iff : forall A B, A ⊆ B <-> A ∩ B = A.
Proof. intros. split. bubun. seteq. bubun. inversion H0. apply H1. bubun. split. apply H0. apply H. apply H0.
       intros. bubun. rewrite <- H in H0. inversion H0. apply H2. Qed.

(*Ensembles では，Disjoint は次のように定義されている．

Inductive Disjoint (B C:Ensemble) : Prop :=
  Disjoint intro : (forall x:U, ˜In (Intersection B C) x) -> Disjoint B C.

 B ∩ C に元がないときに，Disjoint B C と定義している．*)

Lemma Kuu :forall A B, Disjoint U A B <-> (A ∩ B) = ø.
Proof.
  split. intros. seteq. bubun. destruct H. specialize (H x). ok. apply empty_bubun.
  intros. apply Disjoint_intro. intros. unfold not. intros. rewrite H in H0. inversion H0.
Qed.
