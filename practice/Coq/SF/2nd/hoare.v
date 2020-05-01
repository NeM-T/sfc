Set Warnings "-notation-overridden,-parsing".
Require Import maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import imp.


(*実行中のある特定の時点で成立している性質 つまり、プログラム実行時にその箇所に来た時の状態に関して成り立つ言明 -- についての表明*)
Definition Assertion := state -> Prop.

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.
End ExAssertions.


Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(*ホーアの三つ組
   もし c が表明 P を満たす状態から開始され、また、cがいつかは停止するならば、最終状態では、表明Qが成立する。
   表明Pはcの事前条件(precondition) Qはcの事後条件(postcondition)と呼ばれる。*)
Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H. Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption. Qed.

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sun_ex1 :
  {{ (fun st => st X <= 10 ) [X |-> 2 * X] }}
    X ::= 2 * X
  {{ fun st => st X <= 10 }}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sun_ex2 :
  {{ (fun st => 0 <= st  X /\ st X <= 5) [X |-> 3] }}
    X ::= 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  apply hoare_asgn. Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros a P. unfold hoare_triple. intros. 
  exists (st X). split.
  - assert (st = (X !-> st X; st') ).
    { inversion H; subst. rewrite t_update_shadow. rewrite t_update_same. reflexivity. }
    rewrite H1 in H0. apply H0.
  - inversion H; subst. rewrite t_update_shadow. rewrite t_update_same. unfold t_update. simpl. reflexivity.
Qed.


(*
{{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}}はできる。
 {{True}} X ::= 3 {{X = 3}}はできない。
  ↑をできるようにする推論規則をつくる。

                {{P'}} c {{Q}}
                  P <<->> P'
         ----------------------------- (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}

                     ｜
                     ∨

                {{P'}} c {{Q}}
                   P ->> P'
         ----------------------------- (hoare_consequence_pre)
                {{P}} c {{Q}}


                {{P}} c {{Q'}}
                  Q' ->> Q
         ----------------------------- (hoare_consequence_post)
                {{P}} c {{Q}}
*)


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.


Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X < 5) [X |-> X + 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption. Qed.

Example hoare_asgn_example1' :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity. Qed.




(*------eapply---------*)
(*eapply：Hの前提に現れるすべての変数をインスタンス化する方法が決まらない場合に失敗する代わりに、
  eapply Hは、これらの変数を実存変数（nnnと書かれている）に置き換えます。*)
Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.
Abort.

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(*------eapply---------*)



Example assn_sub_ex1' :
  {{(fun st => (st X) + 1 <= 5)}}
    (X ::= (APlus (AId X) (ANum 1)))
    {{fun st => st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assert_implies, assn_sub. intros. rewrite t_update_eq. assumption.
Qed.

Example assn_sub_ex2' :
  {{(fun st => (0 <= 3 /\ 3 <= 5))}}
    X ::= (ANum 3)
    {{fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assert_implies, assn_sub. intros. assumption.
Qed.



(*
      -------------------- (hoare_skip)
      {{ P }} SKIP {{ P }}
 *)


Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption. Qed.



(*
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------- (hoare_seq)
       {{ P }} c1;c2 {{ R }}

 *)
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.
(*
非形式的には、上の規則を利用した証明を表す良い方法は、c1とc2の間に中間表明Qを記述する"修飾付きプログラム"の様にすることです:
      {{ a = n }}
    X ::= a;;
      {{ X = n }} <--- 修飾 Q
    SKIP
      {{ X = n }}
 *)
Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  -
    apply hoare_skip.
  -
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  split; reflexivity.
Qed.

Definition swap_program : com :=
  (Z ::= AId X;; X ::= AId Y;; Y ::= AId Z).

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  unfold swap_program. eapply hoare_consequence_pre. eapply hoare_seq. eapply hoare_seq; apply hoare_asgn. apply hoare_asgn. 
  intros st H. eassumption.
Qed.

(*
              {{P /\ b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------ (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
 *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  -
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  -
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Example if_example :
    {{fun st => True}}
  TEST X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  -
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply eqb_eq in H.
    rewrite H. omega.
  -
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies. simpl.
    intros. apply le_plus_minus. inversion H. apply leb_complete in H1. apply H1.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies. simpl.
    intros. reflexivity.
Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity) : imp_scope.


Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ IF1 b THEN c FI ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ IF1 b THEN c FI]=> st

  where "st '=[' c ']=>' st'" := (ceval c st st').
Close Scope imp_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  (IF1 ~(Y = 0) THEN
    X ::= X + Y
  FI)%imp
  {{ fun st => st X = st Z }}.
Proof.
  unfold hoare_triple. intros. inversion H; subst.
  - (*~ Y = 0*)
    inversion H6; subst. unfold t_update. simpl. apply H0.
  - (*Y = 0*)
    inversion H5. apply negb_false_iff in H2. apply eqb_eq in H2. rewrite H2 in H0. rewrite add_0_r in H0. apply H0.
Qed.

End If1.


(*WHILEの推論規則*)
(*
               {{P /\ b}} c {{P}}
        ---------------------------------- (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}
 *)

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  -
    split. assumption. apply bexp_eval_false. assumption.
  -
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.


Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  -
    apply hoare_post_true. intros st. apply I.
  -
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  -
    intros st H. constructor. Qed.



Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).



Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_RepeatTrue : forall st st' e b,
      st =[ e ]=> st' ->
      beval st' b = true ->
      st =[ REPEAT e UNTIL b END]=> st'
  | E_RepeatFalse : forall st st' st0 e b,
      st =[ e ]=> st0 ->
      beval st b = false ->
      st0 =[REPEAT e UNTIL b END]=> st' ->
      st =[ REPEAT e UNTIL b END]=> st'
where "st '=[' c ']=>' st'" := (ceval st c st').


Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  unfold ex1_repeat. apply E_RepeatTrue. apply E_Seq with (X !-> 1).
  apply E_Ass. reflexivity. apply E_Ass. reflexivity.
  reflexivity.
Qed.

Definition ex2_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL Y = 3 END.

Theorem ex2_repeat_works :
  empty_st =[ ex2_repeat ]=> (Y !-> 3 ; X !-> 1; Y !-> 2; X !-> 1; Y !-> 1; X !-> 1).
Proof.
  unfold ex2_repeat.
  eapply E_RepeatFalse. apply E_Seq with (X !->1).
  apply E_Ass. reflexivity. apply E_Ass. reflexivity.
  reflexivity. simpl.
  eapply E_RepeatFalse. apply E_Seq with (X !->1; Y !-> 1; X !-> 1).
  apply E_Ass. reflexivity. apply E_Ass. reflexivity.
  reflexivity. simpl.
  apply E_RepeatTrue. apply E_Seq with (X !-> 1; Y !-> 2; X !->1; Y !-> 1; X !-> 1).
  apply E_Ass. reflexivity. apply E_Ass. reflexivity. reflexivity.
Qed.

End RepeatExercise.


(*Havocの推論規則*)
Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_Havoc : forall st X n,
      st =[ HAVOC X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.


(*Complete the Hoare rule for HAVOC commands below by defining havoc_pre and prove that the resulting rule is correct.*)
Definition havoc_pre (X : string) (Q : Assertion) : Assertion
  . Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
Admitted.

End Himp.



Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'ASSERT' b" :=
  (CAssert b) (at level 60).
Notation "'ASSUME' b" :=
  (CAssume b) (at level 60).

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

Inductive ceval : com -> state -> result -> Prop :=
  
  | E_Skip : forall st,
      st =[ SKIP ]=> RNormal st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st =[ c1 ;; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ;; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st =[ c ]=> RNormal st' ->
      st' =[ WHILE b DO c END ]=> r ->
      st =[ WHILE b DO c END ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ WHILE b DO c END ]=> RError
  
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ ASSERT b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ ASSERT b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ ASSUME b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r -> P st ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Theorem assert_assume_differ : exists P b Q,
       ({{P}} ASSUME b {{Q}})
  /\ ~ ({{P}} ASSERT b {{Q}}).
Proof.
  unfold hoare_triple.
Abort.


Theorem assert_implies_assume : forall P b Q,
     ({{P}} ASSERT b {{Q}})
  -> ({{P}} ASSUME b {{Q}}).
Proof.
  unfold hoare_triple. intros. specialize (H st r). apply H.
  inversion H0; subst. apply E_AssertTrue. assumption.
  assumption.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ']].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ]].
        inversion Heq; subst. assumption.
  -
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _]].
     inversion C.
Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  -
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  -
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  -
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  -
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  -
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _]]. inversion C.
     + split; assumption.
Qed.

Example assert_assume_example:
  {{fun st => True}}
  ASSUME (X = 1);;
  X ::= X + 1;;
  ASSERT (X = 2)
  {{fun st => True}}.
Proof.
  intros st r H T.
  (*remember ( ASSUME (X = 1);; X ::= X + 1;; ASSERT (X = 2) ) as H0.
  induction H; try (eexists; split; reflexivity). eexists. split.
  inversion HeqH0; subst. apply IHceval2. 
  *)

  induction H; try eassumption;  try( eexists; split; reflexivity). 
Abort.


End HoareAssertAssume.
