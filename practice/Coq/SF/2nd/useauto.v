From Coq Require Import Arith.Arith.

Require Import maps.
Require Import smallstep.
Require Import stlc.
Require Import libtactics.

Require imp.

From Coq Require Import Lists.List.
Import ListNotations.

(* タクティックautoは、intros、apply、assumption、reflexivityの列で証明できるゴールを証明することができます。  *)
Lemma solving_by_reflexivity :
  2 + 3 = 5.
Proof. auto. Qed.

(* applyを2回続けて呼ぶ必要がある証明
   ※eapplyは呼びません *)
Lemma solving_by_apply : forall (P Q : nat->Prop),
  (forall n, Q n -> P n) ->
  (forall n, Q n) ->
  P 2.
Proof. auto. Qed.

Lemma solving_by_eapply : forall (P Q : nat->Prop),
  (forall n m, Q m -> P n) ->
  Q 1 ->
  P 2.
Proof. auto. eauto. Qed.

Lemma solving_conj_goal : forall (P : nat->Prop) (F : Prop),
  (forall n, P n) ->
  F ->
  F /\ P 2.
Proof. auto. Qed.

(* 仮定が連言の場合、autoとeautoはこの連言を使うことができません
      ---> jautoを使おう*)
Lemma solving_conj_hyp : forall (F F' : Prop),
  F /\ F' ->
  F.
Proof.
  (*このふたつはなにもしない*)auto. eauto.
  jauto. Qed.

Lemma solving_conj_hyp' : forall (F F' : Prop),
  F /\ F' ->
  F.
Proof. intros. jauto_set. eauto. Qed.

Lemma solving_conj_more : forall (P Q R : nat->Prop) (F : Prop),
  (F /\ (forall n m, (Q m /\ R n) -> P n)) ->
  (F -> R 2) ->
  Q 1 ->
  P 2 /\ F.
Proof. jauto. Qed.

Lemma solving_conj_hyp_forall : forall (P Q : nat->Prop),
  (forall n, P n /\ Q n) ->
  P 2.
Proof.
  (*なにもしない*)auto. eauto. iauto. jauto.
  intros. destruct (H 2). auto.
Qed.

(* ほとんど同じである次のゴールは自動証明できるのです。 唯一の違いは、全称限量子が連言のそれぞれに別々に付けられていることです。 *)
Lemma solved_by_jauto : forall (P Q : nat->Prop) (F : Prop),
  (forall n, P n) /\ (forall n, Q n) ->
  P 2.
Proof. jauto. Qed.

(* タクティックautoとeautoはゴールに現れる選言を扱うことができます。 *)
Lemma solving_disj_goal : forall (F F' : Prop),
  F ->
  F \/ F'.
Proof. auto. Qed.

(* しかし、コンテキストに現れる選言についての推論を自動化できるのはiautoだけです。 例えば、iautoは 「F \/ F' ならば F' \/ F」を証明できます。 *)
Lemma solving_disj_hyp : forall (F F' : Prop),
  F \/ F' ->
  F' \/ F.
Proof. auto. eauto. jauto. iauto. Qed.

(* iautoは連言、選言、否定の複雑な組み合わせを扱うことができます *)
Lemma solving_tauto : forall (F1 F2 F3 : Prop),
  ((~F1 /\ F3) \/ (F2 /\ ~F3)) ->
  (F2 -> F1) ->
  (F2 -> F3) ->
  ~F2.
Proof. iauto. Qed.

Lemma solving_exists_goal : forall (f : nat->Prop),
  f 2 ->
  exists x, f x.
Proof.
  auto.   eauto. Qed.

Lemma solving_exists_hyp : forall (f g : nat->Prop),
  (forall x, f x -> g x) ->
  (exists a, f a) ->
  (exists a, g a).
Proof.
  (*なにもしない*)auto. eauto. iauto.
  jauto. Qed.

(*autoとeautoはnotを自動展開しない*)
Lemma negation_study_1 : forall (P : nat->Prop),
  P 0 ->
  (forall x, ~ P x) ->
  False.
Proof.
  intros P H0 HX.
  eauto.
  unfold not in *. eauto.
Qed.

(* iautoとjautoは前処理の中で unfold not in * を組織的に呼びます。 *)
Lemma negation_study_2 : forall (P : nat->Prop),
  P 0 ->
  (forall x, ~ P x) ->
  False.
Proof. jauto. Qed.


Lemma equality_by_auto : forall (f g : nat->Prop),
  (forall x, f x = g x) ->
  g 2 = f 2.
Proof. auto. Qed.

(* タクティックautoは次のようにはたらきます。 最初にreflexivityとassumptionを試してみます。 もしどちらかがゴールを解いたならば仕事は完了です。 そうでないときautoは、エラーにならずにゴールに適用できる仮定のうち、一番最後に導入されたものを適用することを試みます。 この適用によりサブゴールが生成されます。 このあと2つの場合があります。 もし生成されたサブゴールがすべてautoの再帰的呼び出しにより解かれた場合、それで終了です。 そうではなく、生成されたサブゴール中にautoが解けないものが1つでもある場合、やり直して、最後から2番目に導入された仮定を適用しようとします。 同様のやり方を、証明を発見するか、適用する仮定がなくなるかするまで続けます。 *)

(*以下のものは連言がおおすぎてautoで証明できない*)
Lemma search_depth_0 :
  True /\ True /\ True /\ True /\ True /\ True.
Proof.
  auto.
Abort.

(*auto n　で回数を指定できる*)
Lemma search_depth_4 : forall (P : nat->Prop),
   (P 0) ->
   (forall k, P (k-1) -> P k) ->
   (P 5).
Proof. auto. auto 6. Qed.

(*debug eauto でeautoのステップが見れる
  debug auto はない*)
Lemma working_of_auto_1 : forall (P : nat->Prop),
   (P 0) ->
   (forall k, P (k-1) -> P k) ->
   (forall k, P (k+1) -> P k) ->
   (P 2).
Proof. intros P H1 H2 H3. debug eauto. Qed.


(* ライブラリ "LibTactics" はタクティックを呼んだ後で自動証明を呼ぶ便利な機能を提供します。タクティック名に星印（*）をつければ良い *)

Ltac auto_star ::= try solve [ jauto ].



(* 自動化の証明例 *)


(* 決定性 *)
Module DeterministicImp.
  Import imp.

(* Imp言語の決定性補題のオリジナルの証明を振り返ってみましょう。 以下の通りです。 *)

(*以前の証明*)
Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  (induction E1); intros st2 E2; inversion E2; subst.
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
    rewrite H in H5. inversion H5.
  -
    rewrite H in H5. inversion H5.
  -
      apply IHE1. assumption.
  -
    reflexivity.
  -
    rewrite H in H2. inversion H2.
  -
    rewrite H in H4. inversion H4.
  -
    assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.


Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros. generalize dependent st2.
  induction H; intros; auto.
  -
    inversion* H0.
  -
    inverts* H0.
  -
    inversions* H1. apply IHceval1 in H4. rewrite <- H4 in H7. apply IHceval2 in H7.
    auto.
  -
    inversions H1. apply IHceval in H8; auto. rewrite H in H7. inversion H7.
  -
    inversions H1. rewrite H7 in H. inversion H. apply IHceval in H8; auto.
  -
    inversions H0; auto. rewrite H in H3; inversion H3.
  -
    inversions H2. rewrite H in H7; inversion H7.
    apply IHceval1 in H6. rewrite <- H6 in H9. apply IHceval2 in H9. auto.
Qed.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. gen st2.
  induction E1; intros; inverts E2; tryfalse; auto.
  - assert (st' = st'0). auto. subst. auto.
  - assert (st' = st'0). auto. subst. auto.
Qed.

(* きれいな証明記述を得るためには、assert (st' = st'0) の呼び出しを消去しなければなりません。 このようなタクティックの呼び出しは、きれいではありません。 なぜなら、自動命名された変数を参照しているからです。 こういうタクティックはとても脆弱なものになりやすいのです。 タクティック assert (st' = st'0) は帰納法の仮定から導出したい結論を主張するのに使われています。 そこで、この結論を明示的に述べる代わりに、帰納法の仮定を具体化する際に自動処理によって計算される具体化法を使うようにCoqに伝えてみましょう。 LibTactics.vに記述されたタクティックforwardsは、事実の具体化について的確に助けてくれます。 それでは、この例についてどのようにはたらくか見てみましょう。 *)

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. gen st2.
  induction E1; intros; inverts E2; tryfalse.
  - auto.
  - auto.
  - dup 4.

  + assert (st' = st'0). apply IHE1_1. apply H1.
skip.

  + forwards: IHE1_1. apply H1.
skip.

  + forwards: IHE1_1. eauto.
skip.

  + forwards*: IHE1_1.
skip.

Abort.

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. gen st2.
  induction E1; intros; inverts* E2; tryfalse.
  - forwards*: IHE1_1. subst*.
  - forwards*: IHE1_1. subst*.
Qed.

End DeterministicImp.

(* STLC の保存 *)

Set Warnings "-notation-overridden,-parsing".
Require Import stlcprop.
Module PreservationProgressStlc.
Import STLC.
Import STLCProp.

(*以前の証明*)
Theorem preservation : forall t t' T,
  has_type empty t T ->
  t --> t' ->
  has_type empty t' T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  (induction HT); intros t' HE; subst Gamma.
  -
    inversion HE.
  -
    inversion HE.
  -
    inversion HE; subst...
    +
      apply substitution_preserves_typing with T11...
      inversion HT1...
  -
    inversion HE.
  -
    inversion HE.
  -
    inversion HE; subst...
Qed.

Theorem preservation' : forall t t' T,
  has_type empty t T ->
  t --> t' ->
  has_type empty t' T.
Proof.
  remember (@empty ty) as Gamma.
  introv HT. generalize dependent t'.
  (induction HT); intros t' HE; subst Gamma; try solve_by_invert.
  -
    inverts* HE. apply* substitution_preserves_typing. inverts* HT1.
  -
    inverts* HE.
Qed.


(* 以前の前進定理の証明 *)
Theorem progress : forall t T,
  has_type empty t T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  (induction Ht); subst Gamma...
  -
    inversion H.
  -
    right. destruct IHHt1...
    +
      destruct IHHt2...
      *
        inversion H; subst; try solve_by_invert.
        exists ([x0:=t2]t)...
      *
       destruct H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      destruct H as [t1' Hstp]. exists (app t1' t2)...
  -
    right. destruct IHHt1...
    destruct t1; try solve_by_invert...
    inversion H. exists (test x0 t2 t3)...
Qed.


Theorem progress' : forall t T,
  has_type empty t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  (induction Ht); subst Gamma; iauto; try solve_by_invert.
  -
    destruct* IHHt1; destruct* IHHt2; destruct H; try solve_by_invert; iauto.
  -
    destruct* IHHt1. destruct H; try solve_by_invert; iauto.
Qed.

End PreservationProgressStlc.

Require Import smallstep.
Require Import Program.
Module Semantics.

Theorem multistep_eval_ind : forall t v,
  t -->* v -> forall n, C n = v -> t ==> n.
Proof.
  introv H H1.
  induction H; intros; subst.
  applys E_Const.
  apply* step__eval.
Qed.

Theorem multistep__eval' : forall t v,
  normal_form_of t v -> exists n, v = C n /\ t ==> n.
Proof.
  introv [H H0]; induction H.
  apply nf_is_value in H0. inversion H0; subst; exists n; iauto; split; auto. apply E_Const.
  apply IHmulti in H0; auto; inversion H0 as [n [H2 H3]]; eexists; split; try apply H2.
  apply* step__eval.
Qed.

End Semantics.

From Coq Require Import omega.Omega.
Require Import references.
Import STLCRef.
Require Import Program.
Module PreservationProgressReferences.
Hint Resolve store_weakening extends_refl.


(*補題を必要とするものの自動化は困難である*)
Lemma nth_eq_last' : forall (A : Type) (l : list A) (x d : A) (n : nat),
  n = length l -> nth n (l ++ x::nil) d = x.
Proof. intros. subst. apply nth_eq_last. Qed.

Lemma preservation_ref : forall (st:store) (ST : store_ty) T1,
  length ST = length st ->
  Ref T1 = Ref (store_Tlookup (length st) (ST ++ T1::nil)).
Proof.
  intros. dup.

  (*やりかた１*)
  unfold store_Tlookup. rewrite* nth_eq_last'.

  (*やりかた２*)
  fequal. symmetry. apply* nth_eq_last'.
Qed.



(* 保存の最適化された証明は次のようにまとめられます。 *)
Theorem preservation' : forall ST t t' T st st',
  has_type empty ST t T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
    (extends ST' ST /\
     has_type empty ST' t' T /\
     store_well_typed ST' st').
Proof.
  remember (@empty ty) as Gamma. introv Ht. gen t'.
  induction Ht; introv HST Hstep; subst Gamma; inverts Hstep; eauto.
  - exists ST. inverts Ht1. splits*. applys* substitution_preserves_typing.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
  - forwards*: IHHt.
  - forwards*: IHHt.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
  - forwards*: IHHt1.
  - exists (ST ++ T1::nil). inverts keep HST. splits.
    apply extends_app.
    applys_eq T_Loc 1.
      rewrite app_length. simpl. omega.
      unfold store_Tlookup. rewrite* nth_eq_last'.
    apply* store_well_typed_app.
  - forwards*: IHHt.
  - exists ST. splits*. lets [_ Hsty]: HST.
    applys_eq* Hsty 1. inverts* Ht.
  - forwards*: IHHt.
  - exists ST. splits*. applys* assign_pres_store_typing. inverts* Ht1.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
Qed.

Theorem progress : forall ST t T st,
  has_type empty ST t T ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
Proof.
  introv Ht HST. remember (@empty ty) as Gamma.
  induction Ht; subst Gamma; tryfalse; try solve [left*].
  - right. destruct* IHHt1 as [K|].
    inverts K; inverts Ht1.
     destruct* IHHt2.
  - right. destruct* IHHt as [K|].
    inverts K; try solve [inverts Ht]. eauto.
  - right. destruct* IHHt as [K|].
    inverts K; try solve [inverts Ht]. eauto.
  - right. destruct* IHHt1 as [K|].
    inverts K; try solve [inverts Ht1].
     destruct* IHHt2 as [M|].
      inverts M; try solve [inverts Ht2]. eauto.
  - right. destruct* IHHt1 as [K|].
    inverts K; try solve [inverts Ht1]. destruct* n.
  - right. destruct* IHHt.
  - right. destruct* IHHt as [K|].
    inverts K; inverts Ht as M.
      inverts HST as N. rewrite* N in M.
  - right. destruct* IHHt1 as [K|].
    destruct* IHHt2.
     inverts K; inverts Ht1 as M.
     inverts HST as N. rewrite* N in M.
Qed.

End PreservationProgressReferences.




Require sub.
Module SubtypingInversion.
Import sub.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  has_type empty (abs x S1 s2) (Arrow T1 T2) ->
     subtype T1 S1
  /\ has_type (update empty x S1) s2 T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...
Qed.

Lemma abs_arrow' : forall x S1 s2 T1 T2,
  has_type empty (abs x S1 s2) (Arrow T1 T2) ->
     subtype T1 S1
  /\ has_type (update empty x S1) s2 T2.
Proof.
  introv H;  apply abs_arrow in H; inverts* H.
Qed.

End SubtypingInversion.


(*eautoの適用順依存*)
Lemma order_matters_1 : forall (P : nat->Prop),
  (forall n m, P m -> m <> 0 -> P n) ->
  P 2 ->
  P 1.
Proof.
  eauto. Qed.

Lemma order_matters_2 : forall (P : nat->Prop),
  (forall n m, m <> 0 -> P m -> P n) ->
  P 5 ->
  P 1.
Proof.
  eauto.
  intros P H K.
  eapply H.
  eauto.
Abort.



(* 証明検索中で定義を展開する *)
(*
 中間的定義を使うことは通常、主張をより簡潔に、より読みやすくすることから、形式的開発では一般に奨励されます。 しかし定義は、証明を自動化することを少し難しくします。 問題は、証明探索メカニズムにとって、定義を展開しなければならないのがいつかが明らかではないことです。 ここで、証明探索を呼ぶ前にすべての定義を展開しておくという素朴な戦略は、大きな証明ではスケールしない（拡大適用できない）ため、それは避ける、ということに注意します。
 *)

Axiom P : nat -> Prop.

Definition myFact := forall x, x <= 3 -> P x.
Lemma demo_hint_unfold_goal_1 :
  (forall x, P x) ->
  myFact.
Proof.
  (*なにもしない*)auto.
  unfold myFact. auto. Qed.

(* myFactがゴールに現れたときに常にmyFactを展開してみるべきであるということを、Coqに伝えることができます。 *)
Hint Unfold myFact.

Lemma demo_hint_unfold_goal_2 :
  (forall x, P x) ->
  myFact.
Proof. auto. Qed.

(* しかしながら、Hint Unfold メカニズムがはたらくのは、ゴールに現れる定義の展開だけです。 一般に証明探索は、コンテキストの定義を展開しません。 例えば、True -> myFact の仮定のもとで、P 3が成立することを証明したいとします。 *)

Lemma demo_hint_unfold_context_1 :
  (True -> myFact) ->
  P 3.
Proof.
  intros.
  (**)auto.
  unfold myFact in *. auto. Qed.

(*直前で同じ証明をしたのでautoで証明できる*)
Lemma demo_hint_unfold_context_2 :
  myFact ->
  P 3.
Proof. auto. Qed.


(* 不合理なゴールの証明の自動化 *)
Parameter le_not_gt : forall x,
  (x <= 3) ->
  ~ (x > 3).

Parameter gt_not_le : forall x,
  (x > 3) ->
  ~ (x <= 3).

Parameter le_gt_false : forall x,
  (x <= 3) ->
  (x > 3) ->
  False.

Section DemoAbsurd1.
Hint Resolve le_not_gt.

Lemma demo_auto_absurd_1 :
  (exists x, x <= 3 /\ x > 3) ->
  False.
Proof.
  intros. jauto_set. eauto.   eapply le_not_gt. eauto. eauto.
Qed.

Hint Resolve le_gt_false.

Lemma demo_auto_absurd_2 :
  (exists x, x <= 3 /\ x > 3) ->
  False.
Proof.
  dup.

  intros. jauto_set. eauto.

  jauto.
Qed.

(* H1 -> H2 -> False という形の補題は H1 -> ~ H2 よりはるかに有効なヒント *)
(* しかし、Falseを結論部とする補題をヒントに追加するのは慎重に行うべきです。 理由は、ゴールFalseに到達するときはいつでも、証明探索メカニズムは、適切なヒントを適用する前に、結論部がFalseであるヒントをすべて適用してみる可能性がある *)
End DemoAbsurd1.

(* 結論部がFalseである補題をヒントに追加することは、ローカルにはとても効率的な解です。 しかし、このアプローチはグローバルなヒントにはスケールアップ（拡大適用）できません。 一番現実的な適用のためには、矛盾を導くのに使う補題に名前を付けるのが合理的です。 LibTactics で提供されているタクティック false H はこの目的に有用です。 このタクティックは、ゴールをFalseに置換し、eapply H を呼びます。 その振る舞いは以下で記述します。 3つの主張le_not_gt、gt_not_le、le_gt_falseのいずれでも使えることを見てください。 *)

Lemma demo_false : forall x,
  (x <= 3) ->
  (x > 3) ->
  4 = 5.
Proof.
  intros. dup 4.

  - false. eapply le_gt_false.
    + auto.     + skip.

  - false. eapply le_gt_false.
    + eauto.     + eauto.
  - false le_gt_false. eauto. eauto.

  - false le_not_gt. eauto. eauto.

Abort.

Parameter typ : Type.

Parameter subtype : typ -> typ -> Prop.

Parameter subtype_refl : forall T,
  subtype T T.

Parameter subtype_trans : forall S T U,
  subtype S T -> subtype T U -> subtype S U.

Hint Resolve subtype_refl.

Section HintsTransitivity.

Hint Resolve subtype_trans.

Lemma transitivity_bad_hint_1 : forall S T,
  subtype S T.
Proof.
  intros. eauto. Abort.

End HintsTransitivity.

