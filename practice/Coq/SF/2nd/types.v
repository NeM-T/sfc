Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
Require Import maps.
Require Import imp.
Require Import smallstep.

Hint Constructors multi.


(*
    t ::= tru 
        | fls 
        | test t then t else t 
        | zro 
        | scc t 
        | prd t 
        | iszro t
 *)
Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

(*
                   -------------------------------                  (ST_TestTru) 
                   test tru then t1 else t2 --> t1 
 
                   -------------------------------                  (ST_TestFls) 
                   test fls then t1 else t2 --> t2 
 
                               t1 --> t1' 
            ----------------------------------------------------       (ST_Test) 
            test t1 then t2 else t3 --> test t1' then t2 else t3 
 
                             t1 --> t1' 
                         ------------------                             (ST_Scc) 
                         scc t1 --> scc t1' 
 
                           ---------------                           (ST_PrdZro) 
                           prd zro --> zro 
 
                         numeric value v1 
                        -------------------                          (ST_PrdScc) 
                        prd (scc v1) --> v1 
 
                              t1 --> t1' 
                         ------------------                             (ST_Prd) 
                         prd t1 --> prd t1' 
 
                          -----------------                        (ST_IszroZro) 
                          iszro zro --> tru 
 
                         numeric value v1 
                      ----------------------                       (ST_IszroScc) 
                      iszro (scc v1) --> fls 
 
                            t1 --> t1' 
                       ----------------------                         (ST_Iszro) 
                       iszro t1 --> iszro t1' 
 *)


Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall t1,
      nvalue t1 ->
      (prd (scc t1)) --> t1
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall t1,
       nvalue t1 ->
      (iszro (scc t1)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  unfold stuck, step_normal_form. exists (scc tru). split. intros H. inversion H. inversion H0. inversion H2.
  intros H. inversion H. inversion H0. inversion H0. inversion H2.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  induction t; intros; intros H1.
  inversion H1; inversion H0.
  inversion H1; inversion H0.
  inversion H; inversion H0.
  inversion H1; inversion H0.
  induction IHt;
    inversion H1; inversion H0; inversion H; subst. inversion H5. inversion H5; subst. unfold value. right; assumption. exists t1'. apply H3. exists t1'. apply H3.
  inversion H. inversion H0. inversion H0.
  inversion H. inversion H0. inversion H0.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.

  unfold deterministic.
  intros. generalize dependent y2.
  induction H; intros y2 H1; inversion H1; subst; try reflexivity; try solve_by_invert. 
  try (apply IHstep in H5; rewrite H5; reflexivity). 
  try apply IHstep in H2; rewrite H2; reflexivity.

  inversion H2. induction (value_is_nf  t1). unfold value. right. assumption. exists t1'0; assumption.
  inversion H. induction (value_is_nf y2 ). unfold value. right; assumption. exists t1'0; assumption.

  apply IHstep in H2. rewrite H2. reflexivity.
  inversion H1.

  inversion H1. induction (value_is_nf t1). unfold value. right; assumption. inversion H7. exists t1'2; assumption.
  inversion H; subst. induction (value_is_nf t0). unfold value; right; assumption. exists t1'0; assumption.
  inversion H1. apply IHstep in H2. rewrite H2. reflexivity.
Qed.



(*型付け*)
Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.



(*
                           ---------------                     (T_Tru) 
                           |- tru \in Bool 
 
                          ---------------                      (T_Fls) 
                          |- fls \in Bool 
 
             |- t1 \in Bool    |- t2 \in T    |- t3 \in T 
             --------------------------------------------     (T_Test) 
                    |- test t1 then t2 else t3 \in T 
 
                             --------------                    (T_Zro) 
                             |- zro \in Nat 
 
                            |- t1 \in Nat 
                          -----------------                    (T_Scc) 
                          |- scc t1 \in Nat 
 
                            |- t1 \in Nat 
                          -----------------                    (T_Prd) 
                          |- prd t1 \in Nat 
 
                            |- t1 \in Nat 
                        --------------------                 (T_IsZro) 
                        |- iszro t1 \in Bool 
 *)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
    - apply T_Fls.
    - apply T_Zro.
    - apply T_Scc.
       + apply T_Zro.
Qed.

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2. Qed.

Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof.
  intros. inversion H. assumption.
Qed.


Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.


(*
進行
　　もし項に型がつくなら、項は値であるか、または1ステップは進める
 *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with auto.
  intros t T HT.
  induction HT.
  - left. unfold value. left. apply bv_tru.
  - left. unfold value. left. apply bv_fls.
  -
    right. inversion IHHT1; clear IHHT1.
    +
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2. apply ST_TestTru.
      exists t3. apply ST_TestFls.
    +
      inversion H as [t1' H1].
      exists (test t1' t2 t3). apply ST_Test. assumption.
  - left. unfold value. right. apply nv_zro.
  - inversion IHHT.
    + left. inversion H. inversion H0; subst; inversion HT. right. apply nv_scc; assumption.
    + right. inversion H. exists (scc x). apply ST_Scc; assumption.
  - inversion IHHT.
    + inversion H. inversion H0; subst; inversion HT.
      inversion H0. right. exists zro. apply ST_PrdZro. right. exists t. apply ST_PrdScc; assumption.
    + inversion H. right. exists (prd x). apply ST_Prd; assumption.
  - inversion IHHT.
    + inversion H. inversion H0; subst; inversion HT. inversion H0.
      right. exists tru. apply ST_IszroZro. right. exists fls. apply ST_IszroScc; assumption.
    + inversion H. right. exists (iszro x). apply ST_Iszro; assumption.
Qed.


(*
型保存
　　型のついた項を一段階簡約すると、簡約結果もまた型のつく項である*)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;

         intros t' HE;

         try solve_by_invert.
    - inversion HE; subst; clear HE.
      + assumption.
      + assumption.
      + apply T_Test; try assumption.
        apply IHHT1; assumption.
    - inversion HE; subst. apply T_Scc. apply IHHT; assumption.
    - inversion HE; subst; try assumption.
      + inversion HT. assumption. 
      + apply T_Prd. apply IHHT; assumption.
    - inversion HE; subst.
      + apply T_Tru.
      + apply T_Fls.
      + apply T_Iszro. apply IHHT; assumption.
Qed.


(*進行と型保存を合わせると、型のついた項は決して行き詰まらないことを示せます。*)
Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed.

