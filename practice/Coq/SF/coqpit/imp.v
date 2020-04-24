Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Add LoadPath "./".
Require Import maps.

Module AExp.

(*算術式とブール式の抽象構文
    a ::= nat 
        | a + a 
        | a - a 
        | a * a 
 
    b ::= true 
        | false 
        | a = a 
        | a <= a 
        | ~ b 
        | b && b 
 *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


(*算術式の評価*)
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(*ブール式の評価*)
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(*「0 + n」を評価前に最適化*)
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(*最適化後も評価が変わらない証明*)
Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  -
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  -
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

(*-----Tactical: タクティックを引数に取る-------*)

(*try：失敗時に何もしない。*)
Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity.   apply HP. Qed.

(*
「;」を使って
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
 これを簡単にする。*)
Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n;
  
  simpl;
  
  reflexivity.
Qed.

(*tryとの併用*)
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  -
    destruct a1 eqn:Ea1;
      
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    + destruct n eqn:En;
        simpl; rewrite IHa2; reflexivity. Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    
    try reflexivity.
  -
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(*repeat*)
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(*失敗しても影響しない。(0回リピートという解釈になる)*)
Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b. (*unfold optimize_0plus_b.*) induction b.
   reflexivity.
   reflexivity.
   simpl; repeat (rewrite -> optimize_0plus_sound); reflexivity.
   simpl; repeat (rewrite -> optimize_0plus_sound); reflexivity.
   simpl; rewrite IHb; reflexivity.
   simpl; rewrite IHb1; rewrite IHb2; reflexivity.
Qed.


(*タクティックを作る
以下抜粋
------------
Tactic Notation コマンドは、「略記法タクティック("shorthand tactics")」を定義する簡単な方法を提供します。 「略記法タクティック」は、呼ばれると、いろいろなタクティックを一度に適用します。

より洗練されたプログラミングのために、CoqはLtacと呼ばれる小さな組込みの言語と、証明の状態を調べたり変更したりするためのLtacのプリミティブを提供します。 その詳細はここで説明するにはちょっと複雑過ぎます（しかも、LtacはCoqの設計の一番美しくない部分だというのが共通見解です!）。 しかし、詳細はリファレンスマニュアルにありますし、Coqの標準ライブラリには、読者が参考にできるLtacの定義のたくさんの例があります。

Coqの内部構造のより深いレベルにアクセスする新しいタクティックを作ることができるOCaml API も存在します。 しかしこれは、普通のCoqユーザにとっては、苦労が報われることはほとんどありません。
------------- *)
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.


(*omega
------
omegaタクティックは「プレスバーガー算術」(Presburger arithmetic、「プレスブルガー算術」とも)と呼ばれる一階述語論理のサブセットの決定手続き(decision procedure)を実装します。 William Pugh が発明したOmegaアルゴリズム Pugh 1991 （Bib.v 参照）に基いています。

ゴールが以下の要素から構成された全称限量された論理式とします。以下の要素とは:
・数値定数、加算（+とS）、減算（-とpred）、定数の乗算（これがプレスバーガー算術である条件です）、
・等式（=と<>）および不等式（<=）、
・論理演算子/\, \/, ~, ->
です。 このとき、omegaを呼ぶと、ゴールを解くか、失敗によりそのゴールが偽であることを表すか、いずれかになります。 （ただしゴールが上記の形「ではない」場合にもomegaは失敗します。）
-------
 *)
Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.


Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End TooHardToRead.

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.


(*記法の定義の予約をすることで定義内でもその記法が使える。*)
Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 -
   intros H.
   induction H; simpl.
   +
     reflexivity.
   +
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   +
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   +
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 -
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   +
     apply E_ANum.
   +
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   +
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   +
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.


Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  -
    intros H; induction H; subst; reflexivity.
  -
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e '//' n" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
| E_BTrue : BTrue // true
| E_BFalse : BFalse // false
| E_BEq (a1 a2 : aexp) (n1 n2 : nat): (a1 \\ n1) -> (a2 \\ n2) -> (BEq a1 a2) // (beq_nat n1 n2)
| E_BLe (a1 a2 : aexp) (n1 n2 : nat) : (a1 \\ n1) -> (a2 \\ n2) -> (BLe a1 a2) // ( n1 <=? n2 )
| E_BNot (be: bexp) (b: bool) : (be // b) -> (BNot be) // (negb b)
| E_BAnd (be1 be2 : bexp) (b1 b2 : bool): (be1 // b1) -> (be2 // b2) -> (BAnd be1 be2) // (b1 && b2)
where "e '//' n" := (bevalR e n) : type_scope.


Lemma beval_iff_bevalR : forall b bv,
  (b // bv) <-> beval b = bv.
Proof.
  split.
  - intros H; induction H.
    reflexivity. reflexivity.
    simpl; rewrite aeval_iff_aevalR' in H; rewrite aeval_iff_aevalR' in H0; subst; reflexivity.
    simpl; rewrite aeval_iff_aevalR' in H; rewrite aeval_iff_aevalR' in H0; subst; reflexivity.
    simpl; subst; reflexivity. simpl. subst; reflexivity.
  - generalize dependent bv. induction b; simpl; intros; subst.
    + apply E_BTrue.
    + apply E_BFalse.
    + apply E_BEq. apply aeval_iff_aevalR'; reflexivity. apply aeval_iff_aevalR'; reflexivity.
 
    + apply E_BLe. apply aeval_iff_aevalR'; reflexivity. apply aeval_iff_aevalR'; reflexivity.
    + apply E_BNot. apply IHb. reflexivity.
    + apply E_BAnd. apply IHb1; reflexivity. apply IHb2; reflexivity.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Reserved Notation "e '\\' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (*任意の自然数をとる*)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (*変数*)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).


Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
(*------------
プログラム変数のこの慣習（X, Y, Z）は、大文字は型を表すのに使うという使用法と衝突します。 Impを構成していく章では多相性を多用はしないので、このことが混乱を招くことはないはずです。
 ------------*)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.

Set Printing Coercions.

Print example_bexp.
(*example_bexp = (bool_to_bexp true && (~ AId X <= ANum 4))%imp
     : bexp*)
Unset Printing Coercions.


Print example_bexp.
(*example_bexp = (true && (~ X <= 4))%imp
     : bexp*)


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))%imp
  = true.
Proof. reflexivity. Qed.


(*
 c ::= SKIP
      | x ::= a
      | c ;; c
      | TEST b THEN c ELSE c FI
      | WHILE b DO c END

階乗計算
     Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END 
*)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.


Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

Unset Printing Notations.
Print fact_in_coq.
(*
fact_in_coq = 
CSeq (CAss Z X)
  (CSeq (CAss Y (S O))
     (CWhile (BNot (BEq Z O))
        (CSeq (CAss Y (AMult Y Z))
           (CAss Z (AMinus Z (S O))))))
     : com
*)
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
(*
fact_in_coq = 
(Z ::= AId X;;
 Y ::= ANum 1;;
 WHILE ~ AId Z = ANum 0
 DO Y ::= AId Y * AId Z;; Z ::= AId Z - ANum 1 END)%imp
     : com
*)
Unset Printing Coercions.

(*Locate：Notationの確認方法*)
Locate "&&".
Locate ";;".
Locate "WHILE".



(*--------コマンドの評価------------*)

(*The following declaration is needed to be able to use the notations in match patterns.*)
Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st
  end.
Close Scope imp_scope.
(*終了しない場合のある定義なので受け付けない*)


(*TypeではなくPropにすることである形式に変換するには証明が必要となる -> 正しさが担保される*)
(*                           -----------------                            (E_Skip) 
                           st =[ SKIP ]=> st 
 
                           aeval st a1 = n 
                   --------------------------------                     (E_Ass) 
                   st =[ x := a1 ]=> (x !-> n ; st) 
 
                           st  =[ c1 ]=> st' 
                           st' =[ c2 ]=> st'' 
                         ---------------------                            (E_Seq) 
                         st =[ c1;;c2 ]=> st'' 
 
                          beval st b1 = true 
                           st =[ c1 ]=> st' 
                ---------------------------------------                (E_IfTrue) 
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st' 
 
                         beval st b1 = false 
                           st =[ c2 ]=> st' 
                ---------------------------------------               (E_IfFalse) 
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st' 
 
                         beval st b = false 
                    -----------------------------                  (E_WhileFalse) 
                    st =[ WHILE b DO c END ]=> st 
 
                          beval st b = true 
                           st =[ c ]=> st' 
                  st' =[ WHILE b DO c END ]=> st'' 
                  --------------------------------                  (E_WhileTrue) 
                  st  =[ WHILE b DO c END ]=> st''                                 *)

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

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

  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI


  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  -
    apply E_Ass. reflexivity.
  -
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with ( Y !-> 1 ; X !-> 0). apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity. 
Qed.

Definition pup_to_n : com :=
  Y ::= ANum 0;;
  WHILE ~ AId X = ANum 0
  DO Y ::= AId Y + AId X;; X ::= AId X - ANum 1 END.


Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n. apply E_Seq with (Y !-> 0 ; X !-> 2). apply E_Ass. reflexivity.
  apply E_WhileTrue with (X !-> 1; Y !-> 2 ; Y !-> 0; X !-> 2 ). reflexivity.
  apply E_Seq with ( Y !-> 2; Y !->0; X !-> 2). apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
  apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2). reflexivity.


  apply E_Seq with ( Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2). apply E_Ass; reflexivity.
  apply E_Ass; reflexivity.
  apply E_WhileFalse. reflexivity.
Qed.

(*状態の一意性*)
Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  -
    assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  -
      apply IHE1. assumption.
  -
      rewrite H in H5. discriminate H5.
  -
      rewrite H in H5. discriminate H5.
  -
      apply IHE1. assumption.
  -
    reflexivity.
  -
    rewrite H in H2. discriminate H2.
  -
    rewrite H in H4. discriminate H4.
  -
      assert (st' = st'0) as EQ1.
      { apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption. Qed.


Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

Theorem XtimesYinZ_spec : forall st nx ny st',
    st X = nx -> st Y = ny
        -> st =[ XtimesYinZ ]=> st' -> st' Z = nx * ny.
Proof.
  intros st x y st' Hx Hy Heval. inversion Heval. subst. clear Heval.
  apply t_update_eq. Qed.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  - (*E_WhileEnd*)
  subst. inversion H.
  - (*E_WhileLoop*)
    apply IHcontra2. subst.  reflexivity.
Qed.


Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END =>
      false
  end.
Close Scope imp_scope.

Inductive no_whilesR: com -> Prop :=
| no_skip : no_whilesR SKIP
| no_ass : forall x a, no_whilesR (x ::= a)
| no_seq : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ;; c2)
| no_if : forall b ct cf, no_whilesR ct -> no_whilesR cf -> no_whilesR (TEST b THEN ct ELSE cf FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros. induction c.
    + apply no_skip.
    + apply no_ass.
    + simpl in H. apply andb_true_iff in H. inversion H.
      apply no_seq; try(apply IHc1); try(apply IHc2); assumption. 
    + simpl in H. apply andb_true_iff in H. inversion H. apply no_if.
      * apply IHc1. assumption. * apply IHc2. assumption.
    + simpl in H. discriminate.
  - intros. induction c; try (reflexivity).
    + simpl. apply andb_true_iff. inversion H. split; try(apply IHc1);  try(apply IHc2); assumption.
    + simpl. inversion H. apply IHc1 in H2 ; apply IHc2 in H4. rewrite H2. rewrite H4. reflexivity.
    + inversion H.
Qed.


Theorem no_whiles_terminating : forall st c,
    no_whilesR c -> exists st', st =[c]=> st'.
Proof.
  intros. generalize dependent st. induction H. 
  - intros. exists st. apply E_Skip.
  - intros. exists(t_update st x (aeval st a)) . apply E_Ass. reflexivity.
  - intros.  destruct (IHno_whilesR1 st). destruct (IHno_whilesR2 x).
     exists (x0). apply E_Seq with c1 c2 st x x0 in H1.  apply H1. apply H2.
  - intros. remember (beval st b) as bv. destruct bv.
    + destruct (IHno_whilesR1 st). exists x. apply E_IfTrue. rewrite Heqbv. reflexivity. apply H1.
    + destruct (IHno_whilesR2 st). exists x. apply E_IfFalse. rewrite Heqbv. reflexivity. apply H1.
Qed.


(*発展問題*)
(*--------電卓スタック------------*)
Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.


Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) : list nat :=
  match prog with
  | [] => stack
  | h :: t => match h with
              | SPush n => s_execute st (n :: stack) t
              | SLoad x => s_execute st ((st x) :: stack) t
              | SPlus => match stack with
                         | n1 :: n2 :: ts => s_execute st ( (n1 + n2) :: ts ) t
                         | _ => []
                         end
              | SMinus => match stack with
                          | n1 :: n2 :: ts => s_execute st ( (n2 - n1) :: ts) t
                          | _ => []
                          end
              | SMult => match stack with
                         | n1 :: n2 :: ts => s_execute st ( (n1 * n2) :: ts) t
                         | _ => []
                         end
              end
  end.

  


Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.


Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2=> (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. induction e; intros; try (reflexivity).
  - simpl. Abort.






(*Andの場合先にboolを計算する*)
Fixpoint beval_short (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => match (beval st b1) with
                  | true => beval st b2
                  | false => false
                  end
  end.

Theorem beval_short_eq : forall (b: bexp) (st: state),
    beval st b = beval_short st b.
Proof.
  induction b; simpl; try(reflexivity). Qed.


Module BreakImp.

Inductive com : Type :=
  | CSkip
  | CBreak
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


Theorem break_ignore : forall c st st' s,
     st =[ BREAK;; c ]=> st' / s ->
     st = st'.
Proof.
  intros. inversion H. Qed.

Theorem while_continue : forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s ->
  s = SContinue.
Proof.
  intros. inversion H. Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  intros. inversion H0. Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros. inversion H. inversion H0. split. subst. reflexivity. reflexivity. Qed.

End BreakImp.
