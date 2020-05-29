Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Arith.Arith.

Require Import maps.
Require Import imp.
Require Import types.
Require Import smallstep.
Require Import libtactics.

Require stlc.
Require equiv.
Require imp.
Require references.
Require smallstep.
Require hoare.
Require sub.


(* タクティックintrov *)
Module IntrovExamples.
  Import stlc.
  Import imp.
  Import STLC.

(*
introv : 仮定をintro
 *)
Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. Abort.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  introv. Abort.

Theorem ceval_deterministic': forall c st st1,
  (st =[ c ]=> st1) ->
  forall st2,
  (st =[ c ]=> st2) ->
  st1 = st2.
Proof.
  introv E1 E2. Abort.

Theorem exists_impl: forall X (P : X -> Prop) (Q : Prop) (R : Prop),
  (forall x, P x -> Q) ->
  ((exists x, P x) -> Q).
Proof.
  introv [x H2]. eauto.
Qed.

End IntrovExamples.


(* タクティックinverts *)
Module InvertsExamples.
  Import stlc.
  Import equiv.
  Import imp.
  Import STLC.

Theorem skip_left: forall c,
  cequiv (SKIP;; c) c.
Proof.
  introv. split; intros H.
  dup.   - inversion H. subst. inversion H2. subst. assumption.
  - inverts H. inverts H2. assumption.
Abort.

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. generalize dependent st2.
  induction E1; intros st2 E2.
  admit. admit.   dup.   - inversion E2. subst. admit.
  - inverts E2. admit.
Abort.

(* 。 inverts H as.では、生成される変数と仮定がコンテキストではなくゴールに置かれます。 この戦略により、 これらの変数と仮定にintrosやintrovを使って明示的に名前を付けることができるようになります。 *)
Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  introv E1 E2. generalize dependent st2.
  (induction E1); intros st2 E2;
    inverts E2 as.
  - reflexivity.
  -
    
     subst n.
    reflexivity.
  -
    
     intros st3 Red1 Red2.
    assert (st' = st3) as EQ1.
    { apply IHE1_1; assumption. }
    subst st3.
    apply IHE1_2. assumption.
  -
    
     intros.
    apply IHE1. assumption.
  -
     intros.
    rewrite H in H5. inversion H5.
Abort.

Example typing_nonexample_1 :
  ~ exists T,
      has_type empty
        (abs x Bool
            (abs y Bool
               (app (var x) (var y))))
        T.
Proof.
  dup 3.

  - intros C. destruct C.
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H1.

  - intros C. destruct C.
  inverts H as H1.
  inverts H1 as H2.
  inverts H2 as H3 H4.
  inverts H3 as H5.
  inverts H5.

  - intros C. destruct C.
  inverts H as H.
  inverts H as H.
  inverts H as H1 H2.
  inverts H1 as H1.
  inverts H1.
Qed.

End InvertsExamples.



(* n-引数論理演算のためのタクティック *)
(*
splits :n個の and を分解します
branch :n個の or を分解します
*)
Module NaryExamples.
  Import references.
  Import smallstep.
  Import STLCRef.

Lemma demo_splits : forall n m,
  n > 0 /\ n < m /\ m < n+10 /\ m <> 3.
Proof.
  intros. splits.
Abort.

Lemma demo_branch : forall n m,
  n < m \/ n = m \/ m < n.
Proof.
  intros.
  destruct (lt_eq_lt_dec n m) as [[H1|H2]|H3].
  - branch 1. apply H1.
  - branch 2. apply H2.
  - branch 3. apply H3.
Qed.

End NaryExamples.



(* 等式を扱うタクティック *)
(*
asserts_rewrite : 書き換えのための等式を導入します
cuts_rewrite : サブゴールが交換される以外は同じです
substs : subst タクティックを改良します
fequals : f_equal タクティックを改良します
applys_eq : 仮定 P x z を使って、等式 y = z をサブゴールとして自動生成することで、 P x y を証明します
*)
Module EqualityExamples.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.
  intros n m.
  assert (H: 0 + n = n). reflexivity. rewrite -> H.
  reflexivity.

  intros n m.
  asserts_rewrite (0 + n = n).
    reflexivity.     reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  cuts_rewrite (0 + n = n).
    reflexivity.     reflexivity. Qed.

(* タクティック asserts_rewrite と cuts_rewrite は補題を引数としてとることができます。 *)
Theorem mult_0_plus'' : forall u v w x y z: nat,
  (u + v) * (S (w * x + y)) = z.
Proof.
  intros. asserts_rewrite (forall a b, a*(S b) = a*b+a).
Abort.

(*
タクティック substs
ゴールが x = f x のような「循環する等式」を含むときも失敗しません。
*)
Lemma demo_substs : forall x y (f:nat->nat),
  x = f x ->
  y = x ->
  y = f x.
Proof.
  intros. substs.   assumption.
Qed.

(*
タクティック fequals
タクティック fequals は f_equal と同様ですが、 生成される自明なサブゴールを直接解決してしまう点が違います。 さらに、タクティック fequals はタプル間の等式の扱いが強化されています。
 *)

Lemma demo_fequals : forall (a b c d e : nat) (f : nat->nat->nat->nat->nat),
  a = 1 ->
  b = e ->
  e = 2 ->
  f a b c d = f 1 2 c 4.
Proof.
  intros. fequals.
Abort.

Axiom big_expression_using : nat->nat.
Lemma demo_applys_eq_1 : forall (P:nat->nat->Prop) x y z,
  P x (big_expression_using z) ->
  P x (big_expression_using y).
Proof.
  introv H. dup.

  assert (Eq: big_expression_using y = big_expression_using z).
    admit.   rewrite Eq. apply H.

  applys_eq H 1.
    admit. Abort.

Lemma demo_applys_eq_2 : forall (P:nat->nat->Prop) x y z,
  P (big_expression_using z) x ->
  P (big_expression_using y) x.
Proof.
  introv H. applys_eq H 2.
Abort.

Lemma demo_applys_eq_3 : forall (P:nat->nat->Prop) x1 x2 y1 y2,
  P (big_expression_using x2) (big_expression_using y2) ->
  P (big_expression_using x1) (big_expression_using y1).
Proof.
  introv H. applys_eq H 1 2.
Abort.

End EqualityExamples.




(* 便利な略記法をいくつか *)
(*
unfolds (引数なし): 先頭の定義を unfold します
false : ゴールを False で置換します
gen : dependent generalize の略記法です
admits : 承認した事実に名前をつけます
admit_rewrite : 承認した等式で書き換えます
admit_goal : 帰納法の仮定を、減少していることを示さないで使えるようにします
sort : 全ての命題を証明コンテキストの下へ動かします
*)
Module UnfoldsExample.
  Import hoare.

Lemma bexp_eval_true : forall b st,
  beval st b = true ->
  (bassn b) st.
Proof.
  intros b st Hbe. dup.

  unfold bassn. assumption.

  unfolds. assumption.
Qed.
End UnfoldsExample.

Lemma demo_false : forall n,
  S n = 1 ->
  n = 0.
Proof.
  intros. destruct n. reflexivity. false.
Qed.

Lemma demo_false_arg :
  (forall n, n < 0 -> False) ->
  3 < 0 ->
  4 < 0.
Proof.
  intros H L. false H. apply L.
Qed.

Lemma demo_tryfalse : forall n,
  S n = 1 ->
  n = 0.
Proof.
  intros. destruct n; tryfalse. reflexivity.
Qed.

(* genは generalize dependent の略記法 *)
Module GenExample.
  Import stlc.
  Import STLC.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
  has_type (update Gamma x U) t S ->
  has_type empty v U ->
  has_type Gamma ([x:=v]t) S.
Proof.
  dup.

  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.

  introv Htypt Htypv. gen S Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.
Abort.

End GenExample.

Module SkipExample.
  Import stlc.
  Import STLC.

Theorem demo_admits : True.
Proof.
  admits H: (forall n m : nat, (0 + n) * m = n * m).
Abort.

Theorem mult_plus_0 : forall n m : nat,
  (n + 0) * m = n * m.
Proof.
  dup 3.

  intros n m.
  assert (H: n + 0 = n). admit. rewrite -> H. clear H.
  reflexivity.

  intros n m.
  admit_rewrite (n + 0 = n).
  reflexivity.

  intros n m.
  admit_rewrite (forall a, a + 0 = a).
  reflexivity.
Admitted.

(* タクティックadmit_goalは現在のゴールを仮定として追加します。 このごまかしは帰納法による証明の構造の構成の際に、 帰納法の仮定がより小さい引数だけに適用されるかを心配しないで済むため有用です。 admit_goalを使うことで、証明を次の2ステップで構成できます： 最初に、帰納法の仮定の細部の調整に時間を浪費せずに、主要な議論が通るかをチェックし、 その後、帰納法の仮定の呼び出しの調整にフォーカスするというステップです。 *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  admit_goal.
  introv E1 E2. gen st2.
  (induction E1); introv E2; inverts E2 as.
  - reflexivity.
  -
    subst n.
    reflexivity.
  -
    intros st3 Red1 Red2.
    assert (st' = st3) as EQ1.
    {
      
       eapply IH. eapply E1_1. eapply Red1. }
    subst st3.
eapply IH. eapply E1_2. eapply Red2.
Abort.

End SkipExample.

Module SortExamples.
  Import imp.

(* タクティックsortは証明コンテキストを再構成し、変数が上に仮定が下になるようにします。 これにより、証明コンテキストはより読みやすくなります。 *)
Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  (induction E1); intros st2 E2; inverts E2.
  admit. admit.   sort. Abort.

End SortExamples.


(* 高度な補題具体化のためのタクティック *)

(* 利用したい補題(または仮定)がある場合、大抵、この補題に明示的に引数を与える必要があります。 例えば次のような形です: destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub). 何回も'_'記号を書かなければならないのは面倒です。 何回書くかを計算しなければならないだけでなく、このことで証明記述がかなり汚なくもなります。 タクティックletsを使うことで、次のように簡単に書くことができます: lets (T & Hctx & Hsub): typing_inversion_var Htypt. *)
Module ExamplesLets.
  Import sub.


Import sub.

Axiom typing_inversion_var : forall (G:context) (x:string) (T:ty),
  has_type G (var x) T ->
  exists S, G x = Some S /\ subtype S T.

Lemma demo_lets_1 : forall (G:context) (x:string) (T:ty),
  has_type G (var x) T ->
  True.
Proof.
  intros G x T H. dup.

  lets K: typing_inversion_var H.
  destruct K as (S & Eq & Sub).
  admit.

  lets (S & Eq & Sub): typing_inversion_var H.
  admit.
Abort.

Lemma demo_lets_2 : forall (G:context) (x:string) (T:ty), True.
Proof.
  intros G x T.
  lets (S & Eq & Sub): typing_inversion_var G x T ___.
Abort.

Lemma demo_lets_3 : forall (x:string), True.
Proof.
  intros x.
  lets (S & Eq & Sub): typing_inversion_var x ___.
Abort.

Lemma demo_lets_4 : True.
Proof.
  lets (S & Eq & Sub): typing_inversion_var ___.
Abort.

Lemma demo_lets_5 : True.
Proof.
  lets H: typing_inversion_var.
Abort.

Lemma demo_lets_underscore :
  (forall n m, n <= m -> n < m+1) ->
  True.
Proof.
  intros H.

  lets K: H 3.     clear K.

  lets K: H __ 3.     clear K.
Abort.

End ExamplesLets.

(*
forwardsは補題のすべての引数を具体化する略記法です。 より詳しくは、forwards H: E0 E1 E2 E3 は lets H: E0 E1 E2 E3 ___ と同じです。ここで ___ の意味は前に説明した通りです。
applysは、letsの高度な具体化モードにより補題を構築し、 それをすぐに使うことにあたります。 これから、applys E0 E1 E2 E3 は、 lets H: E0 E1 E2 E3 の後 eapply H、clear H と続けることと同じです。
specializesは、コンテキストの仮定を特定の引数でその場で具体化することの略記法です。 より詳しくは、specializes H E0 E1 は lets H': H E0 E1 の後 clear H、rename H' into H と続けることと同じです。
 *)

Module ExamplesInstantiations.
  Import sub.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
  has_type (update Gamma x U) t S ->
  has_type empty v U ->
  has_type Gamma ([x:=v]t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  (induction t); intros; simpl.
  -
    rename s into y.

lets (T&Hctx&Hsub): typing_inversion_var Htypt.
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y)...
    +
      subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.

        lets [T' HT']: free_in_context S (@empty ty) Hcontra...
        inversion HT'.
  -

    
    
    
     admit.

  -
    rename s into y. rename t into T1.

lets (T2&Hsub&Htypt2): typing_inversion_abs Htypt.

applys T_Sub (Arrow T1 T2)...
     apply T_Abs...
    destruct (eqb_stringP x y).
    +
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_stringP y x)...
    +
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst. rewrite false_eqb_string...
  -
    lets: typing_inversion_true Htypt...
  -
    lets: typing_inversion_false Htypt...
  -
    lets (Htyp1&Htyp2&Htyp3): typing_inversion_if Htypt...
  -
    
    
     lets: typing_inversion_unit Htypt...

Admitted.

End ExamplesInstantiations.

(* inversionの名前付けをよりよくするintrovとinverts。 *)
(* 証明できないゴールを捨てやすくするfalseとtryfalse。 *)
(* 先頭の定義を展開する（unfoldする）unfolds。 *)
(* 帰納法の状況を整えやすくするgen。 *)
(* 場合分けをよりよくするcasesとcases_if。 *)
(* n-引数コンストラクタを扱うsplitsとbranch。 *)
(* 等価性を扱いやすくするasserts_rewrite、cuts_rewrite、substs、fequals。 *)
(* 補題の具体化と使用方法を表現するlets、forwards、specializes、applys。 *)
(* 補題を適用する前に行う書き換えを自動化するapplys_eq。 *)
(* 柔軟に集中、無視するサブゴールを選ぶadmits、admit_rewrite、admit_goal。 *)
