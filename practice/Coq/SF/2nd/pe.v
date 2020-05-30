Require Import maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import smallstep.
Require Import imp.



(* --------定数畳み込みを一般化する-------- *)

(* 部分状態
      概念的には、（完全な具体的状態の型が string -> nat であるのに対して）部分状態は型 string -> option nat と考えることができます。
      しかしながら、部分状態の個別の変数の状態を参照/更新するだけでなく、 条件分岐の制御フローを扱うために、2つの部分状態を比較して、同じかどうか、あるいは違いはどこかを知りたいことがあるでしょう。
      2つの任意の関数をこのように比較することはできません。 このため、部分状態をより具体的な形、つまり string * nat 対のリストとして表現します。
 *)
Definition pe_state := list (string * nat).

Fixpoint pe_lookup (pe_st : pe_state) (V:string) : option nat :=
  match pe_st with
  | [] => None
  | (V',n')::pe_st => if eqb_string V V' then Some n'
                      else pe_lookup pe_st V
  end.

Definition empty_pe_state : pe_state := [].

(*
もしpe_stateを表現するlistがある識別子を含まないならば、pe_stateは識別子をNoneに写像しなければなりません。 この事実を証明する前に、まずstringの等価関係の推論に関する便利なタクティックを定義します。
   タクティック       compare V V' 
は eqb_string V V' がtrueかfalseかで場合分けする推論をすることを意味します。 V = V' の場合、このタクティックは全ての場所でVをV'に置換します。 *)

Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (eqb_stringP i j);
  [ subst j | ].

Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
  - inversion H.
  - simpl in H. simpl. compare V V'; auto. Qed.

Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => eqb a a' || inb eqb a l'
  end.

Lemma inbP : forall A : Type, forall eqb : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros A eqb beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H1 | H2]; congruence.
Qed.



(*--算術式--*)
Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with
             | Some n => ANum n
             | None => AId i
             end
  | APlus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

(* この部分評価器は定数を畳み込みしますが、可算の結合性の処理はしません。 *)

Example test_pe_aexp1:
  pe_aexp [(X,3)] (X + 1 + Y)%imp
  = (4 + Y)%imp.
Proof. reflexivity. Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] (X + 1 + Y)%imp
  = (X + 1 + 3)%imp.
Proof. reflexivity. Qed.

(*PEの正しさの定義*)
Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.

Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. unfold pe_consistent. intros st pe_st H a.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  -
    remember (pe_lookup pe_st x) as l. destruct l.
    + rewrite H with (n:=n) by apply Heql. reflexivity.
    + reflexivity.
Qed.

(*
しかしながらすぐに、部分評価器で代入を削除することも行いたくなるでしょう。 例えば、
    X ::= 3;; Y ::= X - Y;; X ::= 4
を簡単化するには、Xの代入を最後に遅らせることで、単に
    Y ::= 3 - Y;; X ::= 4
とできる。
*)

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.

Example test_pe_update:
  pe_update (Y !-> 1) [(X,3);(Z,2)]
  = (X !-> 3 ; Z !-> 2 ; Y !-> 1).
Proof. reflexivity. Qed.

(*
    X ::= 3;; Y ::= X - Y;; X ::= 4
を
    Y ::= X - Y;; X ::= 4
に変換することは、非効率であるだけではなく、間違っています。 出力式 3 - Y と X - Y は両方とも正しさの基準を満たすにもかかわらずです。
実のところ、単に pe_aexp pe_st a = a と定義したとしても、定理 pe_aexp_correct_weak は成立してしまいます。
かわりに強い意味での正しさを証明します。

pe_aexpの強い意味での正しさ
部分評価によって生成された式を評価したもの(aeval st (pe_aexp pe_st a))は、完全状態stの、部分状態pe_stによって特定された部分に依存しない
*)
Theorem pe_update_correct: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof. intros. induction pe_st as [| [V n] pe_st]. reflexivity.
  simpl in *. unfold t_update.
  compare V0 V; auto. rewrite <- eqb_string_refl; auto. rewrite false_eqb_string; auto. Qed.

(*
pe_consistentとpe_updateとは2つの方法で関係付けることができます。
1つ目は、状態を部分状態でオーバーライド(上書き)したものは、常にその部分状態と整合的な状態となるということです。
2つ目は、状態がもし部分状態と整合的ならば、その状態をその部分状態でオーバーライドしたものは、もとの状態と同じということです。
*)
Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof. intros st pe_st V n H. rewrite pe_update_correct.
  destruct (pe_lookup pe_st V); inversion H. reflexivity. Qed.

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof. intros st pe_st H V. rewrite pe_update_correct.
  remember (pe_lookup pe_st V) as l. destruct l; auto. Qed.

Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).
Proof.
  intros pe_st a st.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  rewrite pe_update_correct. destruct (pe_lookup pe_st x); reflexivity.
Qed.

(*--ブール式--*)

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1 =>
      match (pe_bexp pe_st b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example test_pe_bexp1:
  pe_bexp [(X,3)] (~(X <= 3))%imp
  = false.
Proof. reflexivity. Qed.

Example test_pe_bexp2: forall b:bexp,
  b = (~(X <= (X + 1)))%imp ->
  pe_bexp [] b = b.
Proof. intros b H. rewrite -> H. reflexivity. Qed.


Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
  intros pe_st b st.
  induction b; simpl;
    try reflexivity;
    try (remember (pe_aexp pe_st a1) as a1';
         remember (pe_aexp pe_st a2) as a2';
         assert (H1: aeval (pe_update st pe_st) a1 = aeval st a1');
         assert (H2: aeval (pe_update st pe_st) a2 = aeval st a2');
           try (subst; apply pe_aexp_correct);
         destruct a1'; destruct a2'; rewrite H1; rewrite H2;
         simpl; try destruct (n =? n0);
         try destruct (n <=? n0); reflexivity);
    try (destruct (pe_bexp pe_st b); rewrite IHb; reflexivity);
    try (destruct (pe_bexp pe_st b1);
         destruct (pe_bexp pe_st b2);
         rewrite IHb1; rewrite IHb2; reflexivity).
Qed.




(* --------ループ以外のコマンドの部分評価-------- *)


(*--代入--*)

Fixpoint pe_remove (pe_st:pe_state) (V:string) : pe_state :=
  match pe_st with
  | [] => []
  | (V',n')::pe_st => if eqb_string V V' then pe_remove pe_st V
                      else (V',n') :: pe_remove pe_st V
  end.

Theorem pe_remove_correct: forall pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0
  = if eqb_string V V0 then None else pe_lookup pe_st V0.
Proof. intros pe_st V V0. induction pe_st as [| [V' n'] pe_st].
  - destruct (eqb_string V V0); reflexivity.
  - simpl. compare V V'.
    + rewrite IHpe_st.
      destruct (eqb_stringP V V0). reflexivity.
      rewrite false_eqb_string; auto.
    + simpl. compare V0 V'.
      * rewrite false_eqb_string; auto.
      * rewrite IHpe_st. reflexivity.
Qed.

Definition pe_add (pe_st:pe_state) (V:string) (n:nat) : pe_state :=
  (V,n) :: pe_remove pe_st V.

Theorem pe_add_correct: forall pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0
  = if eqb_string V V0 then Some n else pe_lookup pe_st V0.
Proof. intros pe_st V n V0. unfold pe_add. simpl.
  compare V V0.
  - rewrite <- eqb_string_refl; auto.
  - rewrite pe_remove_correct.
    repeat rewrite false_eqb_string; auto.
Qed.

(* 以下の2つ定理は、 定義する部分評価器が動的代入と静的代入をそれぞれ正しく扱うことを示すのに使われます。 *)

Theorem pe_update_update_remove: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update (t_update st V n) (pe_remove pe_st V).
Proof. intros st pe_st V n. apply functional_extensionality.
  intros V0. unfold t_update. rewrite !pe_update_correct.
  rewrite pe_remove_correct. destruct (eqb_string V V0); reflexivity.
  Qed.

Theorem pe_update_update_add: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update st (pe_add pe_st V n).
Proof. intros st pe_st V n. apply functional_extensionality. intros V0.
  unfold t_update. rewrite !pe_update_correct. rewrite pe_add_correct.
  destruct (eqb_string V V0); reflexivity. Qed.

(*--条件分岐--*)
Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:string) : bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | Some x, Some y => negb (x =? y)
  | None, None => false
  | _, _ => true
  end.

Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:string),
  true = pe_disagree_at pe_st1 pe_st2 V ->
  In V (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2).
Proof. unfold pe_disagree_at. intros pe_st1 pe_st2 V H.
  apply in_app_iff.
  remember (pe_lookup pe_st1 V) as lookup1.
  destruct lookup1 as [n1|]. left. apply pe_domain with n1. auto.
  remember (pe_lookup pe_st2 V) as lookup2.
  destruct lookup2 as [n2|]. right. apply pe_domain with n2. auto.
  inversion H. Qed.

Fixpoint pe_unique (l : list string) : list string :=
  match l with
  | [] => []
  | x::l =>
      x :: filter (fun y => if eqb_string x y then false else true) (pe_unique l)
  end.

Theorem pe_unique_correct: forall l x,
  In x l <-> In x (pe_unique l).
Proof. intros l x. induction l as [| h t]. reflexivity.
  simpl in *. split.
  -
    intros. inversion H; clear H.
      left. assumption.
      destruct (eqb_stringP h x).
         left. assumption.
         right. apply filter_In. split.
           apply IHt. assumption.
           rewrite false_eqb_string; auto.
  -
    intros. inversion H; clear H.
       left. assumption.
       apply filter_In in H0. inversion H0. right. apply IHt. assumption.
Qed.

Definition pe_compare (pe_st1 pe_st2 : pe_state) : list string :=
  pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
    (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
  ~ In V (pe_compare pe_st1 pe_st2).
Proof. intros pe_st1 pe_st2 V.
  unfold pe_compare. rewrite <- pe_unique_correct. rewrite filter_In.
  split; intros Heq.
  -
    intro. destruct H. unfold pe_disagree_at in H0. rewrite Heq in H0.
    destruct (pe_lookup pe_st2 V).
    rewrite <- beq_nat_refl in H0. inversion H0.
    inversion H0.
  -
    assert (Hagree: pe_disagree_at pe_st1 pe_st2 V = false).
    {
      remember (pe_disagree_at pe_st1 pe_st2 V) as disagree.
      destruct disagree; [| reflexivity].
      apply pe_disagree_domain in Heqdisagree.
      exfalso. apply Heq. split. assumption. reflexivity. }
    unfold pe_disagree_at in Hagree.
    destruct (pe_lookup pe_st1 V) as [n1|];
    destruct (pe_lookup pe_st2 V) as [n2|];
      try reflexivity; try solve_by_invert.
    rewrite negb_false_iff in Hagree.
    apply eqb_eq in Hagree. subst. reflexivity. Qed.

Fixpoint pe_removes (pe_st:pe_state) (ids : list string) : pe_state :=
  match ids with
  | [] => pe_st
  | V::ids => pe_remove (pe_removes pe_st ids) V
  end.

Theorem pe_removes_correct: forall pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb eqb_string V ids then None else pe_lookup pe_st V.
Proof. intros pe_st ids V. induction ids as [| V' ids]. reflexivity.
  simpl. rewrite pe_remove_correct. rewrite IHids.
  compare V' V.
  - rewrite <- eqb_string_refl. reflexivity.
  - rewrite false_eqb_string; try congruence. reflexivity.
Qed.

Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
Proof.
  intros pe_st1 pe_st2 V. rewrite !pe_removes_correct.
  destruct (inbP _ _ eqb_stringP V (pe_compare pe_st1 pe_st2)).
  - reflexivity.
  - apply pe_compare_correct. auto. Qed.

Theorem pe_compare_update: forall pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
Proof. intros. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_compare_removes. reflexivity.
Qed.

Fixpoint assign (pe_st : pe_state) (ids : list string) : com :=
  match ids with
  | [] => SKIP
  | V::ids => match pe_lookup pe_st V with
              | Some n => (assign pe_st ids;; V ::= ANum n)
              | None => assign pe_st ids
              end
  end.

Definition assigned (pe_st:pe_state) (ids : list string) (st:state) : state :=
  fun V => if inb eqb_string V ids then
                match pe_lookup pe_st V with
                | Some n => n
                | None => st V
                end
           else st V.

Theorem assign_removes: forall pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids).
Proof. intros pe_st ids st. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_removes_correct. unfold assigned.
  destruct (inbP _ _ eqb_stringP V ids); destruct (pe_lookup pe_st V); reflexivity.
Qed.

Lemma ceval_extensionality: forall c st st1 st2,
  st =[ c ]=> st1 -> (forall V, st1 V = st2 V) -> st =[ c ]=> st2.
Proof. intros c st st1 st2 H Heq.
  apply functional_extensionality in Heq. rewrite <- Heq. apply H. Qed.

Theorem eval_assign: forall pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st.
Proof. intros pe_st ids st. induction ids as [| V ids]; simpl.
  - eapply ceval_extensionality. apply E_Skip. reflexivity.
  -
    remember (pe_lookup pe_st V) as lookup. destruct lookup.
    + eapply E_Seq. apply IHids. unfold assigned. simpl.
      eapply ceval_extensionality. apply E_Ass. simpl. reflexivity.
      intros V0. unfold t_update. compare V V0.
      * rewrite <- Heqlookup. rewrite <- eqb_string_refl. reflexivity.
      * rewrite false_eqb_string; simpl; congruence.
    + eapply ceval_extensionality. apply IHids.
      unfold assigned. intros V0. simpl. compare V V0.
      * rewrite <- Heqlookup.
        rewrite <- eqb_string_refl.
        destruct (inbP _ _ eqb_stringP V ids); reflexivity.
      * rewrite false_eqb_string; simpl; congruence.
Qed.


(*--部分評価関係--*)
Reserved Notation "c1 '/' st '\\' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
  | PE_Skip : forall pe_st,
      SKIP / pe_st \\ SKIP / pe_st
  | PE_AssStatic : forall pe_st a1 n1 l,
      pe_aexp pe_st a1 = ANum n1 ->
      (l ::= a1) / pe_st \\ SKIP / pe_add pe_st l n1
  | PE_AssDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n, a1' <> ANum n) ->
      (l ::= a1) / pe_st \\ (l ::= a1') / pe_remove pe_st l
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
      c1 / pe_st \\ c1' / pe_st' ->
      c2 / pe_st' \\ c2' / pe_st'' ->
      (c1 ;; c2) / pe_st \\ (c1' ;; c2') / pe_st''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c1' / pe_st'
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = BFalse ->
      c2 / pe_st \\ c2' / pe_st' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c2' / pe_st'
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 <> BTrue ->
      pe_bexp pe_st b1 <> BFalse ->
      c1 / pe_st \\ c1' / pe_st1 ->
      c2 / pe_st \\ c2' / pe_st2 ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2)
             ELSE c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

  where "c1 '/' st '\\' c1' '/' st'" := (pe_com c1 st c1' st').

Hint Constructors pe_com.
Hint Constructors ceval.

Example pe_example1:
  (X ::= 3 ;; Y ::= Z * (X + X))%imp
  / [] \\ (SKIP;; Y ::= Z * 6)%imp / [(X,3)].
Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_AssDynamic. reflexivity. intros n H. inversion H. Qed.

Example pe_example2:
  (X ::= 3 ;; TEST X <= 4 THEN X ::= 4 ELSE SKIP FI)%imp
  / [] \\ (SKIP;; SKIP)%imp / [(X,4)].
Proof. eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_IfTrue. reflexivity.
  eapply PE_AssStatic. reflexivity. Qed.

Example pe_example3:
  (X ::= 3;;
   TEST Y <= 4 THEN
     Y ::= 4;;
     TEST X = Y THEN Y ::= 999 ELSE SKIP FI
   ELSE SKIP FI)%imp / []
  \\ (SKIP;;
       TEST Y <= 4 THEN
         (SKIP;; SKIP);; (SKIP;; Y ::= 4)
       ELSE SKIP;; SKIP FI)%imp
      / [(X,3)].
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  eapply PE_If; intuition eauto; try solve_by_invert.
  econstructor. eapply PE_AssStatic. reflexivity.
  eapply PE_IfFalse. reflexivity. econstructor.
  reflexivity. reflexivity. Qed.

(*--部分評価の正しさ--*)
Reserved Notation "c' '/' pe_st' '/' st '\\' st''"
  (at level 40, pe_st' at level 39, st at level 39).

Inductive pe_ceval
  (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
  | pe_ceval_intro : forall st',
    st =[ c' ]=> st' ->
    pe_update st' pe_st' = st'' ->
    c' / pe_st' / st \\ st''
  where "c' '/' pe_st' '/' st '\\' st''" := (pe_ceval c' pe_st' st st'').

Hint Constructors pe_ceval.

Theorem pe_com_complete:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') ->
  (c' / pe_st' / st \\ st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe; intros st st'' Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. reflexivity.
  - econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    reflexivity.
  -
    edestruct IHHpe1. eassumption. subst.
    edestruct IHHpe2. eassumption.
    eauto.
  - inversion Heval; subst.
    + edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption.
    + edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption.
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (c' / pe_st' / st \\ st'') ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe;
    intros st st'' [st' Heval Heq];
    try (inversion Heval; []; subst); auto.
  - rewrite <- pe_update_update_add. apply E_Ass.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - rewrite <- pe_update_update_remove. apply E_Ass.
    rewrite <- pe_aexp_correct. reflexivity.
  - eapply E_Seq; eauto.
  - apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  - apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  -
    inversion Heval; subst; inversion H7;
      (eapply ceval_deterministic in H8; [| apply eval_assign]); subst.
    +
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
    +
      rewrite -> pe_compare_update.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
Qed.

(* メインの定理です。この言明化について David Menendez に感謝します! *)

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (c' / pe_st' / st \\ st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - apply pe_com_complete. apply H.
  - apply pe_com_sound. apply H.
Qed.



(* -----ループの部分評価-----  *)

Module Loop.

Reserved Notation "c1 '/' st '\\' c1' '/' st' '/' c''"
  (at level 40, st at level 39, c1' at level 39, st' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
  | PE_Skip : forall pe_st,
      SKIP / pe_st \\ SKIP / pe_st / SKIP
  | PE_AssStatic : forall pe_st a1 n1 l,
      pe_aexp pe_st a1 = ANum n1 ->
      (l ::= a1) / pe_st \\ SKIP / pe_add pe_st l n1 / SKIP
  | PE_AssDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n, a1' <> ANum n) ->
      (l ::= a1) / pe_st \\ (l ::= a1') / pe_remove pe_st l / SKIP
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      c2 / pe_st' \\ c2' / pe_st'' / c'' ->
      (c1 ;; c2) / pe_st \\ (c1' ;; c2') / pe_st'' / c''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c1' / pe_st' / c''
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = BFalse ->
      c2 / pe_st \\ c2' / pe_st' / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st \\ c2' / pe_st' / c''
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 <> BTrue ->
      pe_bexp pe_st b1 <> BFalse ->
      c1 / pe_st \\ c1' / pe_st1 / c'' ->
      c2 / pe_st \\ c2' / pe_st2 / c'' ->
      (TEST b1 THEN c1 ELSE c2 FI) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2)
             ELSE c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2) FI)
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)
            / c''
  | PE_WhileFalse : forall pe_st b1 c1,
      pe_bexp pe_st b1 = BFalse ->
      (WHILE b1 DO c1 END) / pe_st \\ SKIP / pe_st / SKIP
  | PE_WhileTrue : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st' \\ c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (WHILE b1 DO c1 END) / pe_st \\ (c1';;c2') / pe_st'' / c2''
  | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 <> BFalse ->
      pe_bexp pe_st b1 <> BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st' \\ c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (c2'' = SKIP%imp \/ c2'' = WHILE b1 DO c1 END%imp) ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (TEST pe_bexp pe_st b1
             THEN c1';; c2';; assign pe_st'' (pe_compare pe_st pe_st'')
             ELSE assign pe_st (pe_compare pe_st pe_st'') FI)%imp
            / pe_removes pe_st (pe_compare pe_st pe_st'')
            / c2''
  | PE_WhileFixedEnd : forall pe_st b1 c1,
      pe_bexp pe_st b1 <> BFalse ->
      (WHILE b1 DO c1 END) / pe_st \\ SKIP / pe_st / (WHILE b1 DO c1 END)
  | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st'
        \\ c2' / pe_st'' / (WHILE b1 DO c1 END) ->
      pe_compare pe_st pe_st'' = [] ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (WHILE BTrue DO SKIP END) / pe_st / SKIP
      
  | PE_WhileFixed : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 <> BFalse ->
      pe_bexp pe_st b1 <> BTrue ->
      c1 / pe_st \\ c1' / pe_st' / SKIP ->
      (WHILE b1 DO c1 END) / pe_st'
        \\ c2' / pe_st'' / (WHILE b1 DO c1 END) ->
      pe_compare pe_st pe_st'' = [] ->
      (WHILE b1 DO c1 END) / pe_st
        \\ (WHILE pe_bexp pe_st b1 DO c1';; c2' END) / pe_st / SKIP

  where "c1 '/' st '\\' c1' '/' st' '/' c''" := (pe_com c1 st c1' st' c'').

Hint Constructors pe_com.

Ltac step i :=
  (eapply i; intuition eauto; try solve_by_invert);
  repeat (try eapply PE_Seq;
          try (eapply PE_AssStatic; simpl; reflexivity);
          try (eapply PE_AssDynamic;
               [ simpl; reflexivity
               | intuition eauto; solve_by_invert])).

Definition square_loop: com :=
  (WHILE 1 <= X DO
    Y ::= Y * Y;;
    X ::= X - 1
  END)%imp.

Example pe_loop_example1:
  square_loop / []
  \\ (WHILE 1 <= X DO
         (Y ::= Y * Y;;
          X ::= X - 1);; SKIP
       END)%imp / [] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  step PE_WhileFixed. step PE_WhileFixedEnd. reflexivity.
  reflexivity. reflexivity. Qed.

Example pe_loop_example2:
  (X ::= 3;; square_loop)%imp / []
  \\ (SKIP;;
       (Y ::= Y * Y;; SKIP);;
       (Y ::= Y * Y;; SKIP);;
       (Y ::= Y * Y;; SKIP);;
       SKIP)%imp / [(X,0)] / SKIP%imp.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileFalse.
  inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.


Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%imp.

Example pe_loop_example3:
  (Z ::= 3;; subtract_slowly) / []
  \\ (SKIP;;
       TEST ~(X = 0) THEN
         (SKIP;; X ::= X - 1);;
         TEST ~(X = 0) THEN
           (SKIP;; X ::= X - 1);;
           TEST ~(X = 0) THEN
             (SKIP;; X ::= X - 1);;
             WHILE ~(X = 0) DO
               (SKIP;; X ::= X - 1);; SKIP
             END;;
             SKIP;; Z ::= 0
           ELSE SKIP;; Z ::= 1 FI;; SKIP
         ELSE SKIP;; Z ::= 2 FI;; SKIP
       ELSE SKIP;; Z ::= 3 FI)%imp / [] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_While.
  step PE_While.
  step PE_While.
  step PE_WhileFixed.
  step PE_WhileFixedEnd.
  reflexivity. inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.

Example pe_loop_example4:
  (X ::= 0;;
   WHILE X <= 2 DO
     X ::= 1 - X
   END)%imp / [] \\ (SKIP;; WHILE true DO SKIP END)%imp / [(X,0)] / SKIP.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ \\ c / st / SKIP).
  eapply PE_Seq. eapply PE_AssStatic. reflexivity.
  step PE_WhileFixedLoop.
  step PE_WhileTrue.
  step PE_WhileFixedEnd.
  inversion H. reflexivity. reflexivity. reflexivity. Qed.

(*---正当性---*)


Reserved Notation "c1 '/' st '\\' st' '#' n"
  (at level 40, st at level 39, st' at level 39).

Inductive ceval_count : com -> state -> state -> nat -> Prop :=
  | E'Skip : forall st,
      SKIP / st \\ st # 0
  | E'Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st \\ (t_update st l n) # 0
  | E'Seq : forall c1 c2 st st' st'' n1 n2,
      c1 / st \\ st' # n1 ->
      c2 / st' \\ st'' # n2 ->
      (c1 ;; c2) / st \\ st'' # (n1 + n2)
  | E'IfTrue : forall st st' b1 c1 c2 n,
      beval st b1 = true ->
      c1 / st \\ st' # n ->
      (TEST b1 THEN c1 ELSE c2 FI) / st \\ st' # n
  | E'IfFalse : forall st st' b1 c1 c2 n,
      beval st b1 = false ->
      c2 / st \\ st' # n ->
      (TEST b1 THEN c1 ELSE c2 FI) / st \\ st' # n
  | E'WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st # 0
  | E'WhileTrue : forall st st' st'' b1 c1 n1 n2,
      beval st b1 = true ->
      c1 / st \\ st' # n1 ->
      (WHILE b1 DO c1 END) / st' \\ st'' # n2 ->
      (WHILE b1 DO c1 END) / st \\ st'' # S (n1 + n2)

  where "c1 '/' st '\\' st' # n" := (ceval_count c1 st st' n).

Hint Constructors ceval_count.

Theorem ceval_count_complete: forall c st st',
  st =[ c ]=> st' -> exists n, c / st \\ st' # n.
Proof. intros c st st' Heval.
  induction Heval;
    try inversion IHHeval1;
    try inversion IHHeval2;
    try inversion IHHeval;
    eauto. Qed.

Theorem ceval_count_sound: forall c st st' n,
  c / st \\ st' # n -> st =[ c ]=> st'.
Proof. intros c st st' n Heval. induction Heval; eauto. Qed.

Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
Proof. intros pe_st1 pe_st2 H V.
  apply (pe_compare_correct pe_st1 pe_st2 V).
  rewrite H. intro. inversion H0. Qed.

Theorem pe_compare_nil_update: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall st, pe_update st pe_st1 = pe_update st pe_st2.
Proof. intros pe_st1 pe_st2 H st.
  apply functional_extensionality. intros V.
  rewrite !pe_update_correct.
  apply pe_compare_nil_lookup with (V:=V) in H.
  rewrite H. reflexivity. Qed.

Reserved Notation "c' '/' pe_st' '/' c'' '/' st '\\' st'' '#' n"
  (at level 40, pe_st' at level 39, c'' at level 39,
   st at level 39, st'' at level 39).

Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                         (st:state) (st'':state) (n:nat) : Prop :=
  | pe_ceval_count_intro : forall st' n',
    st =[ c' ]=> st' ->
    c'' / pe_update st' pe_st' \\ st'' # n' ->
    n' <= n ->
    c' / pe_st' / c'' / st \\ st'' # n
  where "c' '/' pe_st' '/' c'' '/' st '\\' st'' '#' n" :=
        (pe_ceval_count c' pe_st' c'' st st'' n).

Hint Constructors pe_ceval_count.

Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
  n' <= n ->
  c' / pe_st' / c'' / st \\ st'' # n' ->
  c' / pe_st' / c'' / st \\ st'' # n.
Proof. intros c' pe_st' c'' st st'' n n' Hle H. inversion H.
  econstructor; try eassumption. omega. Qed.

Theorem pe_com_complete:
  forall c pe_st pe_st' c' c'', c / pe_st \\ c' / pe_st' / c'' ->
  forall st st'' n,
  (c / pe_update st pe_st \\ st'' # n) ->
  (c' / pe_st' / c'' / st \\ st'' # n).
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe; intros st st'' n Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. apply E'Skip. auto.
  - econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    apply E'Skip. auto.
  -
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. omega.
  - inversion Heval; subst.
    + edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption. eassumption.
    + edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption. eassumption.
  -
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. omega.
  - inversion Heval; subst.
    + econstructor. apply E_IfFalse.
      rewrite <- pe_bexp_correct. assumption.
      apply eval_assign.
      rewrite <- assign_removes. inversion H2; subst; auto.
      auto.
    +
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      econstructor. apply E_IfTrue.
      rewrite <- pe_bexp_correct. assumption.
      repeat eapply E_Seq; eauto. apply eval_assign.
      rewrite -> pe_compare_update, <- assign_removes. eassumption.
      omega.
  - exfalso.
    generalize dependent (S (n1 + n2)). intros n.
    clear - H H0 IHHpe1 IHHpe2. generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + rewrite pe_bexp_correct, H in H7. inversion H7.
    +
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H0) in H7.
      apply H1 in H7; [| omega]. inversion H7.
  - generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + rewrite pe_bexp_correct in H8. eauto.
    + rewrite pe_bexp_correct in H5.
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1) in H8.
      apply H2 in H8; [| omega]. inversion H8.
      econstructor; [ eapply E_WhileTrue; eauto | eassumption | omega].
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c' c'', c / pe_st \\ c' / pe_st' / c'' ->
  forall st st'' n,
  (c' / pe_st' / c'' / st \\ st'' # n) ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe;
    intros st st'' n [st' n' Heval Heval' Hle];
    try (inversion Heval; []; subst);
    try (inversion Heval'; []; subst); eauto.
  - rewrite <- pe_update_update_add. apply E_Ass.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - rewrite <- pe_update_update_remove. apply E_Ass.
    rewrite <- pe_aexp_correct. reflexivity.
  - eapply E_Seq; eauto.
  - apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - inversion Heval; subst; inversion H7; subst; clear H7.
    +
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
    +
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe2. eauto.
  - apply E_WhileFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
  - eapply E_WhileTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe1. eauto. eapply IHHpe2. eauto.
  - inversion Heval; subst.
    +
      inversion H9. subst. clear H9.
      inversion H10. subst. clear H10.
      eapply ceval_deterministic in H11; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      eapply E_WhileTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
      eapply IHHpe2. eauto.
    + apply ceval_count_sound in Heval'.
      eapply ceval_deterministic in H9; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      inversion H2; subst.
      * inversion Heval'. subst. apply E_WhileFalse.
        rewrite -> pe_bexp_correct. assumption.
      * assumption.
  - eapply ceval_count_sound. apply Heval'.
  -
    apply loop_never_stops in Heval. inversion Heval.
  -
    clear - H1 IHHpe1 IHHpe2 Heval.
    remember (WHILE pe_bexp pe_st b1 DO c1';; c2' END)%imp as c'.
    induction Heval;
      inversion Heqc'; subst; clear Heqc'.
    + apply E_WhileFalse.
      rewrite pe_bexp_correct. assumption.
    +
      assert (IHHeval2' := IHHeval2 (refl_equal _)).
      apply ceval_count_complete in IHHeval2'. inversion IHHeval2'.
      clear IHHeval1 IHHeval2 IHHeval2'.
      inversion Heval1. subst.
      eapply E_WhileTrue. rewrite pe_bexp_correct. assumption. eauto.
      eapply IHHpe2. econstructor. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1). eassumption. apply le_n.
Qed.

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st \\ c' / pe_st' / SKIP ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (exists st', st =[ c' ]=> st' /\ pe_update st' pe_st' = st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - intros Heval.
    apply ceval_count_complete in Heval. inversion Heval as [n Heval'].
    apply pe_com_complete with (st:=st) (st'':=st'') (n:=n) in H.
    inversion H as [? ? ? Hskip ?]. inversion Hskip. subst. eauto.
    assumption.
  - intros [st' [Heval Heq]]. subst st''.
    eapply pe_com_sound in H. apply H.
    econstructor. apply Heval. apply E'Skip. apply le_n.
Qed.

End Loop.


(* -----フローチャートプログラムの部分評価----- *)
(* 命令型プログラムを部分評価する標準的アプローチは、 WHILEループを直接部分評価する代わりに、それをフローチャート(flowcharts) に変換することです。 言い換えると、言語にラベルとジャンプを追加すると、 部分評価がずいぶん簡単になることがわかります。 フローチャートを部分評価した結果は、残留フローチャートになります。 ラッキーな場合は、残留フローチャートのジャンプはWHILEループに戻すことができます。 ただし、これは一般にできるわけではありません。 ここではこのことは追求しません。 *)

Inductive block (Label:Type) : Type :=
  | Goto : Label -> block Label
  | If : bexp -> Label -> Label -> block Label
  | Assign : string -> aexp -> block Label -> block Label.

Arguments Goto {Label} _.
Arguments If {Label} _ _ _.
Arguments Assign {Label} _ _ _.

Inductive parity_label : Type :=
  | entry : parity_label
  | loop : parity_label
  | body : parity_label
  | done : parity_label.

Definition parity_body : block parity_label :=
  Assign Y (Y - 1)
   (Assign X (1 - X)
     (Goto loop)).


Fixpoint keval {L:Type} (st:state) (k : block L) : state * L :=
  match k with
  | Goto l => (st, l)
  | If b l1 l2 => (st, if beval st b then l1 else l2)
  | Assign i a k => keval (t_update st i (aeval st a)) k
  end.

Example keval_example:
  keval empty_st parity_body
  = ((X !-> 1 ; Y !-> 0), loop).
Proof. reflexivity. Qed.


Definition program (L:Type) : Type := L -> option (block L).

Definition parity : program parity_label := fun l =>
  match l with
  | entry => Some (Assign X 0 (Goto loop))
  | loop => Some (If (1 <= Y) body done)
  | body => Some parity_body
  | done => None
  end.

(* 基本ブロックとは異なり、プログラムは停止しないこともあります。 これからプログラムの評価は再帰関数ではなく帰納的関係pevalでモデル化します。 *)

Inductive peval {L:Type} (p : program L)
  : state -> L -> state -> L -> Prop :=
  | E_None: forall st l,
    p l = None ->
    peval p st l st l
  | E_Some: forall st l k st' l' st'' l'',
    p l = Some k ->
    keval st k = (st', l') ->
    peval p st' l' st'' l'' ->
    peval p st l st'' l''.

Example parity_eval: peval parity empty_st entry empty_st done.
Proof. erewrite f_equal with (f := fun st => peval _ _ _ st _).
  eapply E_Some. reflexivity. reflexivity.
  eapply E_Some. reflexivity. reflexivity.
  apply E_None. reflexivity.
  apply functional_extensionality. intros i. rewrite t_update_same; auto.
Qed.


(* --基本ブロックとフローチャートプログラムの部分評価-- *)
Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L)
  : block (pe_state * L) :=
  match k with
  | Goto l => Goto (pe_st, l)
  | If b l1 l2 =>
    match pe_bexp pe_st b with
    | BTrue => Goto (pe_st, l1)
    | BFalse => Goto (pe_st, l2)
    | b' => If b' (pe_st, l1) (pe_st, l2)
    end
  | Assign i a k =>
    match pe_aexp pe_st a with
    | ANum n => pe_block (pe_add pe_st i n) k
    | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
    end
  end.

Example pe_block_example:
  pe_block [(X,0)] parity_body
  = Assign Y (Y - 1) (Goto ([(X,1)], loop)).
Proof. reflexivity. Qed.

Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l').
Proof. intros. generalize dependent pe_st. generalize dependent st.
  induction k as [l | b l1 l2 | i a k];
    intros st pe_st H.
  - inversion H; reflexivity.
  -
    replace (keval st (pe_block pe_st (If b l1 l2)))
       with (keval st (If (pe_bexp pe_st b) (pe_st, l1) (pe_st, l2)))
       in H by (simpl; destruct (pe_bexp pe_st b); reflexivity).
    simpl in *. rewrite pe_bexp_correct.
    destruct (beval st (pe_bexp pe_st b)); inversion H; reflexivity.
  -
    simpl in *. rewrite pe_aexp_correct.
    destruct (pe_aexp pe_st a); simpl;
      try solve [rewrite pe_update_update_add; apply IHk; apply H];
      solve [rewrite pe_update_update_remove; apply IHk; apply H].
Qed.

Definition pe_program {L:Type} (p : program L)
  : program (pe_state * L) :=
  fun pe_l => match pe_l with | (pe_st, l) =>
                option_map (pe_block pe_st) (p l)
              end.

Inductive pe_peval {L:Type} (p : program L)
  (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
  | pe_peval_intro : forall st' pe_st',
    peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
    pe_update st' pe_st' = st'o ->
    pe_peval p st pe_st l st'o l'.

Theorem pe_program_correct:
  forall (L:Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' <->
  pe_peval p st pe_st l st'o l'.
Proof. intros.
  split.
  - intros Heval.
    remember (pe_update st pe_st) as sto.
    generalize dependent pe_st. generalize dependent st.
    induction Heval as
      [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];
      intros st pe_st Heqsto; subst sto.
    + eapply pe_peval_intro. apply E_None.
      simpl. rewrite Hlookup. reflexivity. reflexivity.
    +
      remember (keval st (pe_block pe_st k)) as x.
      destruct x as [st' [pe_st' l'_]].
      symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
      inversion Hkeval. subst st'o l'_. clear Hkeval.
      edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
      eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
      simpl. rewrite Hlookup. reflexivity.
  - intros [st' pe_st' Heval Heqst'o].
    remember (pe_st, l) as pe_st_l.
    remember (pe_st', l') as pe_st'_l'.
    generalize dependent pe_st. generalize dependent l.
    induction Heval as
      [ st [pe_st_ l_] Hlookup
      | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
        Hlookup Hkeval Heval ];
      intros l pe_st Heqpe_st_l;
      inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
    + apply E_None. simpl in Hlookup.
      destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
    +
      simpl in Hlookup. remember (p l) as k.
      destruct k as [k|]; inversion Hlookup; subst.
      eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
Qed.
