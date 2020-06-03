
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.



Module ArithC.

Inductive t : Type :=
| true
| false
| If (t1 t2 t3: t)
| O (*オーです*)
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t).

Fixpoint Const_num (T: t) : nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => Const_num t1
  | pred t1 => Const_num t1
  | iszero t1 => Const_num t1
  | If t1 t2 t3 => (Const_num t1) + (Const_num t2) + (Const_num t3)
  end.

Fixpoint size (T: t) : nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => 1 + (size t1)
  | pred t1 => 1 + (size t1)
  | iszero t1 => 1 + (size t1)
  | If t1 t2 t3 => 1 +  (size t1) + (size t2) + (size t3)
  end.

Lemma l3_3: forall T,
    Const_num T <= size T.
Proof.
  induction T; auto.
  - (*If*)
    simpl. induction IHT1. induction IHT2. induction IHT3; auto.
    rewrite plus_n_Sm in IHIHT3; apply le_S; assumption.
    apply le_S. rewrite <- plus_n_Sm. rewrite plus_Sn_m. assumption.
    apply le_S; assumption.
  - (*succ*)
    simpl. inversion IHT; auto.
  - (*pred*)
    simpl. inversion IHT; auto.
  - (*iszero*)
    simpl. inversion IHT; auto.
Qed.

Fixpoint depth (T: t): nat :=
  match T with
  | true => 1
  | false => 1
  | O => 1
  | succ t1 => 1 + depth t1
  | pred t1 => 1 + depth t1
  | iszero t1 => 1 + depth t1
  | If t1 t2 t3 => (Nat.max (depth t1) (Nat.max (depth t2) (depth t3) ))
  end.

End ArithC.

Module ArithBool.

Inductive t : Type :=
| true
| false
| If (t1 t2 t3: t).

Inductive value : t -> Prop :=
| v_true : value true
| v_false: value false.


Reserved Notation " t '-->' t' " (at level 40).

Inductive step : t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If true t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If false t2 t3 --> t3
| E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3

  where " t '-->' t' " := (step t t').


Theorem T3_5_4 : forall t t' t'', (*決定性*)
    t --> t' -> t --> t'' -> t' = t''.
Proof.
  intros. generalize dependent t''.
  induction H; intros.
  - (*E_Iftrue*)
    inversion H0; subst; auto. inversion H4.
  - (*E_IfFalse*)
    inversion H0; subst; auto. inversion H4.
  - (*E_If*)
    inversion H0; subst. inversion H. inversion H.
    apply IHstep in H5; subst; auto.
Qed.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma L_origin : forall t t' t'',
    t -->* t' -> t' -->* t'' -> t -->* t''.
Proof.
  intros. generalize dependent t''. induction H; intros; try assumption.
  eapply multi_step. apply H. apply IHmulti in H1. assumption.
Qed.


Theorem T3_5_11 : forall t u u',
    t -->* u -> t -->* u' -> value u -> value u' -> u = u'.
Proof.
  intros. generalize dependent u'. induction H; intros.
  induction H0; auto. destruct H1; inversion H.

  destruct H2. destruct H3; inversion H.
  eapply T3_5_4 with (t'' := y0) in H; auto.
  subst. 
  apply IHmulti; auto.
Qed.

Theorem T3_5_12 : forall t1,
    exists t', value t' /\ t1 -->* t'.
Proof.
  induction t1.
  exists true; split. apply v_true. apply multi_refl.
  exists false; split. apply v_false. apply multi_refl.
  inversion IHt1_1; inversion IHt1_2; inversion IHt1_3;
  clear IHt1_3; clear IHt1_2; clear IHt1_1.
  inversion H. inversion H0. inversion H1.
  induction H3.
  destruct H2.
  exists x0. split; auto. eapply multi_step. apply E_IfTrue. assumption.
  exists x1. split; auto. eapply multi_step. apply E_IfFalse. assumption.

  destruct IHmulti; auto.
  exists x2. inversion H9; split; auto.
  eapply multi_step. apply E_If. apply H3. assumption.
Qed.

End ArithBool.

Module ArithNat.


Inductive t: Type :=
| true
| false
| If (t1 t2 t3: t)
| O
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t).


Inductive NatValue: t -> Prop :=
| nv_O : NatValue O
| nv_S : forall nv1, NatValue nv1 -> NatValue (succ nv1).

Inductive value: t -> Prop :=
| v_tru : value true
| v_fls : value false
| v_nat : forall t1, NatValue t1 -> value t1.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step: t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If true t2 t3 --> t2
| E_IfFalse : forall t2 t3,
    If false t2 t3 --> t3
| E_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3
| E_Succ : forall t1 t1',
    t1 --> t1' -> succ t1 --> succ t1'
| E_PredZero :
    pred O --> O
| E_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) --> nv1
| E_Pred : forall t1 t1',
    t1 --> t1' -> pred t1 --> pred t1'
| E_IsZeroZero :
    iszero O --> true
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> false
| E_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

  where " t '-->' t' " := (step t t').


Lemma nv_notstep : forall nv1,
    NatValue nv1 -> not (exists t1, nv1 --> t1).
Proof.
  intros. induction H; intro H1.
  inversion H1. inversion H.
  inversion H1. inversion H0; subst.
  induction IHNatValue.
  exists t1'; assumption.
Qed.

Theorem T3_5_14 : forall t1 t1' t1'',
    t1 --> t1' -> t1 --> t1'' -> t1' = t1''.
Proof.
  intros. generalize dependent t1''.
  induction H; intros.
  - (*E_IfTtur*)
    inversion  H0; subst; auto. inversion H4.
  - (*E_IfFalse*)

    inversion H0; subst; auto. inversion H4.
  - (*E_If*)
    inversion H0; subst. inversion H. inversion H.
    apply IHstep in H5; subst; auto.
  - (*E_Succ*)
    inversion H0. apply IHstep in H2; subst; auto.
  - (*E_PredZero*)
    inversion H0; subst; auto. inversion H1.
  - (*E_PredSucc*)
    inversion H0; auto.
    apply nv_notstep in H. inversion H2. induction H. exists t1'0. assumption.
  - (*E_Pred*)
    inversion H0; subst. inversion H.
    inversion H. apply nv_notstep in H2. induction H2. exists t1'0; auto. 
    apply IHstep in H2. subst; auto.
  - (*E_IsZeroZero*)
    inversion H0; subst; auto. inversion H1.
  - (*E_IsZeroSucc*)
    inversion H0; subst; auto.
    inversion H2; subst. apply nv_notstep in H. induction H. exists t1'0; auto.
  - (*E_Iszero*)
    inversion H0; subst.
    inversion H.
    apply nv_notstep in H2. induction H2. inversion H. exists t1'0; auto.
    apply IHstep in H2. subst; auto.
Qed.


Reserved Notation " t '==>' t' " (at level 40).

Inductive bigstep : t -> t -> Prop :=
| B_Value : forall t1,
    value t1 -> t1 ==> t1
| B_IfTrue : forall t1 t2 v2 t3,
    t1 ==> true -> t2 ==> v2 -> value v2 -> If t1 t2 t3 ==> v2
| B_IfFalse : forall t1 t2 t3 v3,
    t1 ==> false -> t3 ==> v3 -> value v3 -> If t1 t2 t3 ==> v3
| B_Succ : forall t1 nv1,
    t1 ==> nv1 -> NatValue nv1 -> succ t1 ==> succ nv1
| B_PredZero : forall t1,
    t1 ==> O -> pred t1 ==> O
| B_PredSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> NatValue nv1 -> pred t1 ==> nv1
| B_IsZeroZero : forall t1,
    t1 ==> O -> iszero t1 ==> true
| B_IsZeroSucc : forall t1 nv1,
    t1 ==> (succ nv1) -> iszero t1 ==> false

  where " t '==>' t' " := (bigstep t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma bigstepvalue: forall t1 v,
    t1 ==> v -> value v.
Proof.
  intros. induction H; auto.
  apply v_nat. apply nv_S; auto.
  inversion IHbigstep. inversion H1. apply v_nat; auto.
  apply v_tru. apply v_fls.
Qed.

Lemma bigsteptrans: forall t1 t1' t2,
    t1 --> t1' -> t1' ==> t2 -> t1 ==> t2.
Proof.
  intros. generalize dependent t2; induction H; intros.
  - (*E_IfTrue*)
    apply B_IfTrue; auto. apply B_Value; apply v_tru.
    eapply bigstepvalue; auto. apply H0.
  - (*E_IfFalse*)
    apply B_IfFalse; auto. apply B_Value; apply v_fls.
    eapply bigstepvalue; eauto.
  - (*E_If*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_IfTrue; auto.
    apply B_IfFalse; auto.
  - (*E_Succ*)
    inversion H0; subst. inversion H1. inversion H2. apply B_Succ; auto.
    apply IHstep. apply B_Value; auto. apply v_nat; auto.
    apply B_Succ; auto.
  - (*E_PredZero*)
    inversion H0; subst. apply B_PredZero; auto.
  - (*E_PredSucc*)
    inversion H; subst.
    inversion H0. apply B_PredSucc; auto. apply B_Value. apply v_nat; apply nv_S; apply nv_O.
    inversion H0; subst. apply B_PredSucc. apply B_Value. apply v_nat; apply nv_S. apply H. auto.
    apply B_PredSucc. apply B_Succ; auto. apply nv_S; auto. apply nv_S; auto.
  - (*E_Pred*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_PredZero. apply IHstep; auto.
    apply B_PredSucc; auto. 
  - (*E_IsZeroZero*)
    inversion H0. apply B_IsZeroZero. apply B_Value. apply v_nat. apply nv_O.
  - (*E_IsZeroSucc*)
    inversion H0. apply B_IsZeroSucc with (nv1:= nv1). apply B_Value. apply v_nat; apply nv_S; auto.
  - (*E_IsZero*)
    inversion H0; subst. inversion H1. inversion H2.
    apply B_IsZeroZero; auto.
    apply B_IsZeroSucc with (nv1:= nv1); auto.
Qed.


Theorem T3_5_18 : forall t1 v,
    (t1 -->* v) -> value v -> t1 ==> v.
Proof.
  intros. induction H.
  apply B_Value; auto.
  pose proof (IHmulti H0).
  eapply bigsteptrans. apply H. apply H2.
Qed.

End ArithNat.

Module ArithNatBad.

Inductive t: Type :=
| tru
| fls
| If (t1 t2 t3: t)
| O
| succ (t1: t)
| pred (t1: t)
| iszero (t1: t)
| wrong.


Inductive NatValue: t -> Prop :=
| nv_O : NatValue O
| nv_S : forall nv1, NatValue nv1 -> NatValue (succ nv1).

Inductive value: t -> Prop :=
| v_tru : value tru
| v_fls : value fls
| v_nat : forall t1, NatValue t1 -> value t1.

Inductive BadNat : t -> Prop :=
| bn_tru : BadNat tru
| bn_fls : BadNat fls
| bn_wrong : BadNat wrong.

Inductive BadBool : t -> Prop :=
| bb_nat : forall t1, NatValue t1 -> BadBool t1
| bb_wrong : BadBool wrong.

Reserved Notation " t '-->' t' " (at level 40).
Inductive estep: t -> t -> Prop :=
| Ee_IfTrue : forall t2 t3,
    If tru t2 t3 --> t2
| Ee_IfFalse : forall t2 t3,
    If fls t2 t3 --> t3
| Ee_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    If t1 t2 t3 --> If t1' t2 t3
| Ee_Succ : forall t1 t1',
    t1 --> t1' -> succ t1 --> succ t1'
| Ee_PredZero :
    pred O --> O
| Ee_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) --> nv1
| Ee_Pred : forall t1 t1',
    t1 --> t1' -> pred t1 --> pred t1'
| Ee_IsZeroZero :
    iszero O --> tru
| Ee_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) --> fls
| Ee_IsZero : forall t1 t1',
    t1 --> t1' -> iszero t1 --> iszero t1'

(*行き詰まり処理*)
| Ee_IfWrong : forall t1 t2 t3,
    BadBool t1 -> If t1 t2 t3 --> wrong
| E_SuccWrong : forall t1,
    BadNat t1 -> succ t1 --> wrong
| Ee_PredWrong : forall t1,
    BadNat t1 -> pred t1 --> wrong
| Ee_IsZeroWrong : forall t1,
    BadNat t1 -> iszero t1 --> wrong

  where " t '-->' t' " := (estep t t').

Reserved Notation " t '-->o' t' " (at level 40).
Inductive step: t -> t -> Prop :=
| E_IfTrue : forall t2 t3,
    If tru t2 t3 -->o t2
| E_IfFalse : forall t2 t3,
    If fls t2 t3 -->o t3
| E_If : forall t1 t1' t2 t3,
    t1 -->o t1' ->
    If t1 t2 t3 -->o If t1' t2 t3
| E_Succ : forall t1 t1',
    t1 -->o t1' -> succ t1 -->o succ t1'
| E_PredZero :
    pred O -->o O
| E_PredSucc : forall nv1,
    NatValue nv1 -> pred (succ nv1) -->o nv1
| E_Pred : forall t1 t1',
    t1 -->o t1' -> pred t1 -->o pred t1'
| E_IsZeroZero :
    iszero O -->o tru
| E_IsZeroSucc : forall nv1,
    NatValue nv1 -> iszero (succ nv1) -->o fls
| E_IsZero : forall t1 t1',
    t1 -->o t1' -> iszero t1 -->o iszero t1'

  where " t '-->o' t' " := (step t t').

Definition stop (t1: t) :=
  not (value t1) /\ not (exists t1', t1 -->o t1').

Lemma existstop:
  exists t1, stop t1.
Proof.
  exists (iszero tru).
  split.
  intro H; inversion H. inversion H0.
  intro H. inversion H. inversion H0. inversion H2.
Qed.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Fixpoint Good (t1: t) : bool :=
  match t1 with
  | wrong => false
  | If t1' t2 t3 => andb (Good t1') (andb (Good t2) (Good t3))
  | succ t1' => Good t1'
  | pred t1' => Good t1'
  | iszero t1' => Good t1'
  | _ => true
  end.

Lemma nv_notstep : forall nv1,
    NatValue nv1 -> not (exists t1, nv1 --> t1).
Proof.
  intros. induction H; intro H1.
  inversion H1. inversion H.
  inversion H1. inversion H0; subst.
  induction IHNatValue.
  exists t1'; assumption.
  inversion H3; subst; solve_by_invert.
Qed.

Lemma NatValuesucc: forall nv,
    NatValue nv -> not (exists t1', succ nv --> t1').
Proof.
  intros. induction H.
  intro H. inversion H. inversion H0; try solve_by_invert.
  intro HH. inversion HH. inversion H0; subst.
  induction IHNatValue. exists t1'; auto.
  inversion H2.
Qed.

Lemma A3: forall t1 t1' t1'',
     t1 --> t1' -> t1 --> t1'' -> t1' = t1''.
Proof.
  intros. generalize dependent t1''; induction H; intros.
  -
    inversion H0; subst; auto; try solve_by_invert. inversion H4. inversion H.
  -
    inversion H0; subst; auto; try solve_by_inverts 2.
  -
    inversion H0; subst; try solve_by_invert.
    apply IHestep in H5; subst; auto.
    inversion H5; subst. induction (nv_notstep t1); auto. exists t1'; auto.
    inversion H.
  -
    inversion H0; subst. rewrite IHestep with (t1'':=t1'0); auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; auto; try solve_by_invert.
  -
    inversion H0; subst; auto.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    inversion H2.
  -
    inversion H0;subst. inversion H.
    induction (NatValuesucc t1''); auto. exists t1'; auto. 
    apply IHestep in H2; subst; auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; auto; try solve_by_invert.
  -
    inversion H0; subst; auto.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    inversion H2.
  -
    inversion H0; subst; auto; try solve_by_invert.
    induction (NatValuesucc nv1); auto. exists t1'; auto.
    apply IHestep in H2; subst; auto.
    inversion H2; subst; try solve_by_invert.
  -
    inversion H0; subst; try solve_by_inverts 2; auto.
    inversion H; subst; try solve_by_invert.
    induction (nv_notstep t1); auto. exists t1'; auto.
  -
    inversion H; subst.
    inversion H0; subst; try solve_by_invert; auto.
    inversion H0; subst; try solve_by_invert; auto.
    inversion H0; subst; auto. inversion H2.
  -
    inversion H0; subst; try solve_by_invert; auto.
    inversion H; subst; try solve_by_invert.
  -
    inversion H0; subst; try solve_by_invert; auto.
    inversion H; subst; try solve_by_invert.
Qed.


Lemma IfStopWrong: forall t1 t2 t3,
    stop (If t1 t2 t3) -> not (exists t1', t1 -->o t1').
Proof.
  intros.
  induction t1.
  - (*tur*)
    inversion H. induction H1. exists t2; apply E_IfTrue.
  - (*fls*)
    inversion H. induction H1; exists t3; apply E_IfFalse.
  - (*If*)
    intros HH.
    inversion HH.
    inversion H.
    inversion H0; subst;
    induction H2; eexists; eapply E_If; apply H0.
  -
    intro HH; inversion HH. inversion H0.
  -
    intro HH; inversion HH. inversion H0.
    inversion H. induction H5.
    eexists. eapply E_If. eapply E_Succ. apply H2.
  -
    intros HH; inversion HH. inversion H. inversion H0; subst;
    induction H2; subst; eexists; eapply E_If; eassumption.
  -
    intros HH; inversion HH; inversion H. inversion H0; subst;
    induction H2; eexists; eapply E_If; eassumption.
  -
    intros HH; inversion HH; inversion H. inversion H0; subst;
    induction H2; eexists; eapply E_If; eassumption.
Qed.

Notation multiestep := (multi estep).
Notation "t1 '-->*' t2" := (multiestep t1 t2) (at level 40).

Notation multistep := (multi step).
Notation "t1 '-->o*' t2" := (multistep t1 t2) (at level 40).


Lemma Iftrans : forall t1 t2 t3 t1',
    t1 -->* t1' -> If t1 t2 t3 -->* If t1' t2 t3.
Proof.
  intros. induction H.
  apply multi_refl. eapply multi_step. apply Ee_If. eassumption.
  assumption.
Qed.


Lemma multitrans: forall t1 t2 t3,
    t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros. generalize dependent t3. induction H; intros.
  assumption.
  eapply multi_step. apply H. apply IHmulti. assumption.
Qed.


Fixpoint NVBool (t1: t) : bool :=
  match t1 with
  | O => true
  | succ t1' => NVBool t1'
  | _ => false
  end.

Lemma NVB_nv : forall t1,
    NVBool t1 = true <-> NatValue t1.
Proof.
  split; intros.
  -
    induction t1; try solve_by_invert.
    apply nv_O. apply nv_S. apply IHt1. inversion H; auto.
  -
    induction H; subst; auto.
Qed.

Lemma stepe : forall t1 t1',
    t1 -->o t1' -> t1 --> t1'.
Proof.
  intros. induction H.
  -
    apply Ee_IfTrue.
  -
    apply Ee_IfFalse.
  -
    apply Ee_If; auto.
  -
    apply Ee_Succ; auto.
  -
    apply Ee_PredZero.
  -
    apply Ee_PredSucc; auto.
  -
    apply Ee_Pred; auto.
  -
    apply Ee_IsZeroZero.
  -
    apply Ee_IsZeroSucc; auto.
  -
    apply Ee_IsZero; auto.
Qed.

Lemma A4If : forall t1 t2 t3,
    (Good (If t1 t2 t3)) = true -> stop (If t1 t2 t3) -> (If t1 t2 t3) -->* wrong.
Proof.
  intros. generalize dependent t3. generalize dependent t2. generalize dependent t1.
  induction t1; intros.
  -
    inversion H0. induction H2. exists t2; apply E_IfTrue.
  -
    inversion H0. induction H2. exists t3; apply E_IfFalse.
  -
    destruct (Good (If t1_1 t1_2 t1_3)) eqn:IHH.

    assert (stop (If t1_1 t1_2 t1_3)).
    split; intro HH. inversion HH. inversion H1.
    inversion HH. inversion H0. apply H3. exists (If x t2 t3). apply E_If; auto.

    apply IHt1_1 in H1; auto.
    apply Iftrans with (t2:= t2) (t3:= t3) in H1.

    assert (If wrong t2 t3 -->* wrong).
    eapply multi_step. apply Ee_IfWrong. apply bb_wrong.
    apply multi_refl.
    apply multitrans with (t3:= wrong) in H1; auto.

    inversion H. apply andb_prop in H2. inversion H2. inversion H1. apply andb_prop in H5.
    inversion H5. apply andb_prop in H6. inversion H6;  inversion IHH; subst.
    rewrite H4 in H10. rewrite H7 in H10. rewrite H8 in H10. inversion H10.
  -
    eapply multi_step. apply Ee_IfWrong. apply bb_nat. apply nv_O. apply multi_refl.
  -
    generalize H0; intro H1.
    apply IfStopWrong in H0.
    destruct (Good (If t1 t2 t3)) eqn:IHH.
    apply IHt1 in IHH.
    inversion IHH; subst.

    inversion H2; subst.
    eapply multi_step. apply Ee_If. apply E_SuccWrong. apply bn_tru.
    eapply multi_step. apply Ee_IfWrong. apply bb_wrong. apply multi_refl.

    eapply multi_step. apply Ee_If. apply E_SuccWrong. apply bn_fls.
    eapply multi_step. apply Ee_IfWrong. apply bb_wrong. apply multi_refl.

    induction H0. exists (succ t1'). apply E_Succ; auto. admit.

    inversion H8; subst.
    eapply multi_step. apply Ee_IfWrong. apply bb_nat; apply nv_S; auto. apply multi_refl.
    eapply multi_step. apply Ee_If; apply E_SuccWrong. apply bn_wrong. eapply multi_step. apply Ee_IfWrong.
    apply bb_wrong. apply multi_refl.

    split; intro HH; inversion HH; try solve_by_invert.
    inversion H1. admit.

    admit.
  -
Abort.



Lemma A4: forall t1,
    (Good t1) = true -> stop t1 -> t1 --> wrong.
Proof.
  induction t1; intros.
  -
    admit.
  -
    admit.
  -
    admit.
  -
Abort.


Lemma NVstep: forall nv,
    NatValue nv -> not (exists t1', succ nv -->o t1').
Proof.
  intros. induction H.
  intro H. inversion H. inversion H0; try solve_by_invert.
  intro HH. inversion HH. inversion H0; subst.
  induction IHNatValue. exists t1'; auto.
Qed.

Lemma A5: forall t1 t2,
    Good t1 = true -> Good t2 = false ->
    t1 --> t2 -> stop t1.
Proof.
  intros. induction H1; try solve_by_invert.
  -
    try (inversion H; apply andb_prop in H2; inversion H2; rewrite H1 in H0; discriminate H0).
  -
    inversion H. apply andb_prop in H2. inversion H2. rewrite H3 in H0; discriminate.
  -
    split; intros HH. inversion HH. inversion H2.
    inversion H0. inversion H. apply andb_prop in H4. inversion H4. rewrite H5 in H3.
    destruct (Good t1') eqn:IHH. discriminate.
    inversion HH. inversion H6; subst; try solve_by_invert.
    destruct IHestep; auto. induction H8. exists t1'0; auto.
  -
    split; intro HH. inversion HH; subst. inversion H2; induction (nv_notstep t1); auto. exists t1'; auto.
    inversion HH. inversion H2; subst. destruct IHestep; auto. induction H5. exists t1'0; auto.
  -
    inversion H. rewrite H3 in H0. inversion H0. 
  -
    inversion H. destruct IHestep; auto.
    split; intro HH. inversion HH. inversion H5.
    inversion HH. inversion H5; subst; try solve_by_invert.
    induction H2. apply v_nat; apply nv_S; auto.
    induction H4. exists t1'0; auto.
  -
    inversion H; inversion H0. destruct IHestep; auto.
    split; intro HH. inversion HH. inversion H6.
    inversion HH. inversion H6; subst; try solve_by_invert.
    induction H2. apply v_nat; apply nv_S; auto.
    induction H5. exists t1'0; auto.
  -
    inversion H1; subst; try solve_by_inverts 2.
    split; intro HH; inversion HH. inversion H3.
    inversion H3; subst; try solve_by_invert.
    induction (NVstep t1); auto. exists (succ t1'). apply E_Succ; auto.
  -
    inversion H1; subst; try solve_by_invert;
    split; intro HH;
      inversion HH; inversion H2; subst; try solve_by_invert.
  -
    inversion H1; subst; try solve_by_invert;
      split; intro HH; inversion HH;  try solve_by_inverts 2.
  -
    inversion H1; subst; try solve_by_invert;
      split; intro HH; inversion HH;  try solve_by_inverts 2.
Qed.

End ArithNatBad.
