Set Warnings "-notation-overridden,-parsing".
Require Coq.omega.Omega.
From LF Require Export logic.


(*偶数の定義
ev_0:0が偶数である
ev_SS: nが偶数のときn+2は偶数である*)
Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(*直感的には下の定義だけどこれは無理。
  帰納的定義にしないと。
 error message:
    "wrong_ev" must have "n" as 1st argument in "wrong_ev 0"*)
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).

(*これならOK*)
Inductive even' : nat -> Prop := 
| ev_0' : even' 0 
| ev_SS' : forall n, even' n -> even' (S (S n)).

(*4が偶数である証明*)
Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  even (double n).
Proof.
   intros. induction n. simpl. apply ev_0. simpl. apply ev_SS. apply IHn.
Qed.


Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  -
    left. reflexivity.
  -
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  -
    
Abort. (*destructじゃ無理*)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(*inversion使えば簡単*)
Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

(*inversionでdiscriminateをできる*)
Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.


Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
 intros n E. inversion E as [| n' E'].
  -
    exists 0. reflexivity.
  - 
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I.
Abort.

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  -
    exists 0. reflexivity.
  -
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m. destruct n. 
  - intros. apply H0.
  - intros. induction H0 as [|n' E H1].
       + simpl. rewrite <- plus_n_O. apply H.
       + simpl. Search plus. rewrite PeanoNat.Nat.add_succ_r. 
         apply ev_SS. rewrite PeanoNat.Nat.add_succ_r. rewrite PeanoNat.Nat.add_succ_l in H1.
          apply H1.
Qed.


Inductive even'' : nat -> Prop :=
| even''_0 : even'' 0
| even''_2 : even'' 2
| even''_sum n m (Hn : even'' n) (Hm : even'' m) : even'' (n + m).


Theorem even''_ev : forall n, even'' n <-> even n.
Proof.
  intros. induction n. split. intros. apply ev_0. intros. apply even''_0.
  - split. intros. induction H. 
     + apply ev_0. + apply ev_SS. apply ev_0.
     + apply ev_sum. apply IHeven''1. apply IHeven''2.
     + intro.
     { induction H. 
        - apply even''_0.
        - apply even''_sum with (n:= 2) (m:= n0). 
             + apply even''_2.
             + apply IHeven. }
Qed.


Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m H En.
  induction En as [| n' IHn'].
  simpl in H.
  apply H.
  simpl in H.
  inversion H.
  apply IHIHn'.
  apply H1.
Qed.  

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p H H1 . destruct m.
  - simpl. rewrite plus_comm in H. simpl in H. apply (ev_ev__ev n p) in H1.
    apply H1. apply H.
  - destruct p. + rewrite <- plus_n_O in H1. rewrite <- plus_n_O. apply (ev_ev__ev n (S m)).
    apply H. apply H1.
    + apply (ev_ev__ev n (S m)) in H. apply ev_sum. apply H. apply (ev_ev__ev n (S p)) in H1.
      apply H1. destruct n. apply ev_0.
Admitted.


(*------Inductive Relations--------*)
Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. generalize dependent H.
  induction H0. 
    - intros. apply H.
    - intros. apply le_S. apply IHle in H. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H. 
  - apply le_n.
  - apply le_S. apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - apply le_n.
  - apply le_trans with (n:= S n).
       + apply le_S. apply le_n.
       + apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction b.
  - rewrite plus_comm. simpl. apply le_n.
  - rewrite plus_comm. simpl. apply le_S. rewrite plus_comm. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt. intros. split. 
   - apply le_trans with (n:= S (n1 + n2) ).
    + Search plus S eq. rewrite <- plus_Sn_m. apply le_plus_l.
    + apply H.
  - apply le_trans with (n:= S (n1 + n2) ).
    + Search plus S eq. rewrite plus_n_Sm. rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S. apply H.
Qed.

Theorem leb_complete : forall n m,
  n =< m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n as [| n' IH].
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate.
    + apply n_le_m__Sn_le_Sm.
      apply IH.
      apply H.
Qed.


Theorem leb_succ : forall n m,
  (n =< m) = true -> (n =< S m) = true.
Proof.
  intros n m. generalize dependent m. induction n as [| n' IH].  reflexivity. intros. simpl. inversion H.
  destruct m. discriminate. rewrite H1. apply IH. apply H1.
Qed.

Theorem leb_nn : forall n,
  n =< n = true.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n =< m = true.
Proof.
  intros. induction m.
  -  inversion H. simpl. reflexivity.
  - intros. inversion H.
     + rewrite leb_nn. reflexivity.
     + apply leb_succ. apply IHm. apply H2.
Qed. 


Theorem leb_true_trans : forall n m o,
  n =< m = true -> m =< o = true -> n =< o = true.
Proof.
  intros n m o H H0. apply leb_correct. apply leb_complete in H. apply leb_complete in H0.
  generalize dependent H0. generalize dependent H. apply le_trans.
Qed.

Theorem leb_iff : forall n m,
  n =< m = true <-> n <= m.
Proof.
  intros. split.
  - apply leb_complete. - apply leb_correct.
Qed.





Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

Theorem R112:
  R 1 1 2.
Proof.
  apply c2. apply c3. apply c1.
Qed.
Theorem R226:
  R 2 2 6.
Proof.
  apply c2. apply c3. apply c3. apply c2. apply c4. apply c2. apply c3.
Abort.

Definition fR : nat -> nat -> nat :=
  fun n m =>  n + m.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR. intros. split.
  - intros. induction H. 
   + reflexivity.
   + apply eq_S with (x:= (m+n)). apply IHR.
   + rewrite plus_comm. simpl. rewrite plus_comm.
     apply eq_S with (x:= (m+n)). apply IHR.
   + simpl in IHR. apply S_injective in IHR. apply S_injective.
     rewrite plus_n_Sm. apply IHR.
   + rewrite plus_comm. apply IHR.
  - intros. destruct H. induction n. 
   + rewrite plus_comm. simpl. 
    induction m. apply c1. apply c2. apply IHm.
   + rewrite plus_comm. simpl. apply c3. rewrite plus_comm. apply IHn.
Qed.

Inductive subseq {X : Type} : list X -> list X -> Prop :=
  subseq_nil : forall l, subseq [] l
| subseq_inboth : forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
| subseq_in2nd  : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros. induction l. apply subseq_nil. apply subseq_inboth. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros. induction H.
  - apply subseq_nil.
  - simpl. apply subseq_inboth. apply IHsubseq.
  - simpl. apply subseq_in2nd. apply IHsubseq.
Qed.

Theorem subseq_nil_r : forall l : list nat,
  subseq l [] -> l = [].
Proof.
  intros. inversion H. reflexivity.
Qed.


Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 T12 T23.
  generalize dependent T12.
  generalize dependent l1.
  induction T23.
  - intros. inversion T12. apply subseq_nil.
  - intros. inversion T12.
    + apply subseq_nil.
    + apply subseq_inboth. apply IHT23. apply H1.
    + apply subseq_in2nd. apply IHT23. apply H1.
  - intros. apply subseq_in2nd. apply IHT23. apply T12.
Qed.

Inductive R' : nat -> list nat -> Prop := 
 | c7 : R' 0 [] 
 | c8 : forall n l, R' n l -> R' (S n) (n :: l) 
 | c9 : forall n l, R' (S n) l -> R' n l.
Theorem R'210:
  R' 2 [1;0].
Proof.
  apply c8. apply c8. apply c7.
Qed.
Theorem R11210 :
  R' 1 [1;2;1;0].
Proof.
  apply c9. apply c8. apply c9. apply c9. apply c8. apply c8. apply c8. apply c7.
Qed.
Theorem R'6321: 
  R' 6 [3;2;1;0].
Proof.
  Abort.




(*---------正規表現のモデル化--------------*)
(*
The expression EmptySet does not match any string.
The expression EmptyStr matches the empty string [].
The expression Char x matches the one-character string [x].

If re1 matches s1, and re2 matches s2, then App re1 re2 matches s1 ++ s2.
If at least one of re1 and re2 matches s, then Union re1 re2 matches s.
If we can write some string s as the concatenation of a sequence of strings s = s_1 ++ ... ++ s_k,
    and the expression re matches each one of the strings s_i, then Star re matches s.
As a special case, the sequence of strings may be empty,
   so Star re always matches the empty string [] no matter what re is.*)
Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).
Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.
Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.
Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros. inversion H. 
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros. inversion H.
  + apply MUnionL. apply H0.
  + apply MUnionR. apply H0.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros. induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
     + apply H. simpl. left. reflexivity.
     + apply IHss. intros. apply H. right. apply H0.
Qed.


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. 
  generalize dependent s1.
  induction s2 as [|h t].
  - (* s2 = [] *)
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
  - (* s2 = h::t *)
    intros s1. split. 
    + intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      apply (IHt s2) in H4. rewrite H4. reflexivity.
    + intros H. simpl. rewrite H.
      assert ( A : forall S (x:S) y, [x]++y = x::y).
      {  intros S x y. simpl. reflexivity.  }
      rewrite <- A. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
Qed.


Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  -
    apply Hin.
  -
    apply Hin.
  - simpl. apply In_app_iff. apply In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    +
      left. apply (IH1 Hin).
    +
      right. apply (IH2 Hin).
  -
    simpl. apply In_app_iff.
    left. apply (IH Hin).
  -
    simpl. apply In_app_iff.
    right. apply (IH Hin).
  -
    destruct Hin.
  -
    simpl. apply In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    +
      apply (IH1 Hin).
    +
      apply (IH2 Hin).
Qed.


Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with 
  | EmptySet => false
  | EmptyStr => true
  | Char _   => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re1 => true
  end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros. split.
  - intros [s H]. induction H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + simpl. rewrite IHexp_match. reflexivity.
    + simpl. rewrite IHexp_match. apply orb_true_iff. right. reflexivity.
    + reflexivity.
    + rewrite IHexp_match2. reflexivity.

   - intros. induction re.
     + discriminate.
     + exists []. apply MEmpty.
     + exists [t]. apply MChar.
     + simpl in H. apply andb_true_iff in H. inversion H. apply IHre1 in H0. apply IHre2 in H1.
       inversion H0. inversion H1. exists (x ++ x0). apply MApp. apply H2. apply H3.
     + simpl in H. apply orb_true_iff in H. inversion H.
      { apply IHre1 in H0. inversion H0. exists x. apply MUnionL. apply H1. }
      { apply IHre2 in H0. inversion H0. exists x. apply MUnionR. apply H1. }
    + exists []. apply MStar0.
Qed.


(*--------The remember Tactic--------*)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1. induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  -
    simpl. intros H. apply H.
  -
  Abort.


Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  -
    injection Heqre'. intros Heqre'' s H. apply H.
  -
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.


Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros. remember (Star re) as str.
  induction H  as [|x'|s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re''|s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqstr.
  - inversion Heqstr.
  - inversion Heqstr.
  - inversion Heqstr.
  - inversion Heqstr.
  - exists []. split. reflexivity.
    intros. inversion H.
  - destruct (IH2 Heqstr) as [ss' [L R]].
    exists (s1::ss'). split.
    + simpl. rewrite <- L. reflexivity.
    + intros s' H. destruct H.
      { rewrite <- H. inversion Heqstr. rewrite H1 in Hmatch1. apply Hmatch1. }
      { apply R. apply H. }
Qed.

(*pumping：一定以上の長さの文字列は分割して判定する。*)
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch. unfold not.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  -
    simpl. intros. inversion H. 
  -
   simpl. intros. inversion H. inversion H2.
  -
   simpl. intros.
Admitted.


(*---Case Study: Improving Reflection---*)

(*ブール演算とPropの関連付けで面倒になる証明*)
Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  -
    simpl. intros H. apply H. reflexivity.
  -
    simpl. destruct (n =? m) eqn:H.
    +
      intros _. apply eqb_eq in H. rewrite H.
      left. reflexivity.
    +
      intros H'. right. apply IHl'. apply H'.
Qed.


(*boolからPropへ直接変換する関数を用いる*)
Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. intros H'. apply H in H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros. induction H.
  - split. intros. reflexivity. intros. apply H.
  - split. intros. induction H. apply H0. intros. discriminate.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n == m).
Proof.
  intros n m. apply iff_reflect. split. apply eqb_eq. apply eqb_eq.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n == x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  -
    simpl. intros H. apply H. reflexivity.
  -
    simpl. destruct (eqbP n m) as [H | H].
    +
      intros _. rewrite H. left. reflexivity.
    +
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n == m then 1 else 0) + count n l'
  end.

Theorem count_0_app : forall n x l,
   count n (x :: l) = 0 ->  count n (l) = 0.
Proof.
  intros. inversion H. destruct (n == x).
  discriminate. simpl. reflexivity.
Qed.

Theorem In_x_app : forall {X: Type}(n x: X) l,
  In n l -> In n (x:: l).
Proof.
  intros. simpl. right. apply H.
Qed.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  unfold not. intros. induction l.
  - inversion H0.
  - apply IHl. 
     + apply count_0_app in H. apply H.
     + simpl in H0. inversion H0.
      * rewrite H1 in H. simpl in H. rewrite eqb_nn in H. discriminate.
      * apply H1.
Qed.



Inductive nostutter {X:Type} : list X -> Prop :=
  | st_nil : nostutter []
  | st_2nil (x: X): nostutter [x]
  | st_nm  : forall x h t, nostutter (h :: t) -> ~(x = h) -> nostutter (x :: h :: t).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. apply st_nm. apply st_nm. apply st_nm. apply st_nm. apply st_nm. apply st_2nil.
       - unfold not. intros. discriminate.
       - unfold not. intros. discriminate.
       - unfold not. intros. discriminate.
       - unfold not. intros. discriminate.
       - unfold not. intros. discriminate.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. apply st_nil. Qed.

Example test_nostutter_3: nostutter [5].
Proof. apply st_2nil. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. unfold not. intros. inversion H. inversion H2.
       unfold not in H9. apply H9. reflexivity.
Qed.

Inductive pal {X: Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_one (x: X) : pal [x]
  | pal_add : forall (x: X) l, pal l -> pal (x :: l ++ [x]).


Theorem rev_pal : forall {X: Type} (l: list X),
  pal (l ++ rev l).
Proof.
  intros. induction l.
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc. apply (pal_add x (l ++ rev l)). apply IHl.
Qed.


Theorem pal_rev : forall {X: Type} (l : list X),
  pal l -> l = rev l.
Proof.
  intros. induction H.
  - simpl. reflexivity. - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite <- IHpal. reflexivity.
Qed.

Theorem revpal : forall {X: Type} (l: list X),
  l = rev l -> pal l.
Proof.
  intros. induction l.
  - apply pal_nil.
  - induction IHl.
    + apply pal_one.
    + inversion H. assert ([x0; x0] = (x0 :: [] ++ [x0])). { reflexivity. }
      rewrite H0. apply pal_add. apply pal_nil.
    + simpl in H. inversion H.
Admitted.

Theorem in_x : forall {X: Type} (x: X) (l: list X),
  l = [x] -> In x l.
Proof.
  intros. inversion H. simpl. left. reflexivity.
Qed.

Theorem f_equal : forall {X Y : Type} (x y : X) (f: X-> Y),
 x = y -> f x = f y.
  Proof.
    destruct 1; trivial.
Defined.


Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l. simpl. intro. inversion H. destruct 1.
  subst x0; auto.
  exists [], l; auto.
  destruct (IHl H) as (l1, (l2, H0)).
  exists (x::l1), l2; simpl.
Admitted.


(*-------鳩の巣の原理無理だった---------*)
Inductive repeats {X:Type} : list X -> Prop :=
  | repeat (x: X): repeats [x ; x]
  | replace_many (l1 l2 l3: list X): repeats l2 -> repeats (l1 ++ l2 ++ l3).

Example retest : repeats [1; 3; 4; 5; 5].
  apply (replace_many [1; 3; 4] [5; 5] []). apply repeat.
Qed.

Theorem app_one : forall {X: Type} (l: list X) x,
  (x :: l) = [x] ++ l.
Proof. reflexivity. Qed.

Lemma lt_not_eq: forall n:nat , ~(n <n).
Proof.
  unfold not. unfold lt. intros. Search le. induction n. inversion H.
  apply IHn. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Lemma le_leftS : forall n m : nat, S n <= m -> n <= m.
Proof. intros. apply le_trans with (S n).
   apply le_S. apply le_n. apply H. 
Qed.

Theorem le_le_eq : forall n m, n <= m -> m <= n -> n = m.
Proof.
  intros. inversion H. reflexivity.
  inversion H0. rewrite H3. symmetry. apply H5.

(*induction H. reflexivity. induction H0. reflexivity.*)
Admitted.

Lemma lt_nn : forall n, ~(n < n).
Proof.
 intros. unfold lt. unfold not. intros. induction n. inversion H. apply IHn. 
 apply Sn_le_Sm__n_le_m in H. apply H.
Qed.


Lemma lt_not_le: forall n m : nat, n < m -> ~ m <= n.
Proof.
 intros. inversion H.
 - apply lt_not_eq.
 - apply n_le_m__Sn_le_Sm in H0. rewrite H2 in H0. rewrite H2. apply le_leftS in H0. apply le_leftS in H0.
 unfold not. intros. 
 unfold not. intros. apply le_le_eq in H0. rewrite H0 in H. apply lt_nn in H. apply H. apply H3.
Qed.


Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
 intros X l1. induction l1 as [|x l1' IHl1'].
 - intros. inversion H1.
 - intros. apply not_exists_dist with  (X:= list X) (P:= repeats) (x:= x:: l1') in H. apply H.
  unfold not. intros. inversion H2. apply H3.

(*  rewrite <- app_nil_r. simpl. rewrite app_one. apply replace_many. apply H.
  unfold not. intros. inversion H2. apply H3. induction x0. 
 apply IHl1' with (l2:= l2).
  apply H. intros. apply H0. simpl. right. apply H2.
  apply not_exists_dist with  (X:= nat) (P:= lt (length l2)) (x:= length l1') in H. apply H.
  unfold not. intros. inversion H3. induction x0. *)
Abort.




(*以下の4つはexcluded_middleを含めて等価である。
　証明しろ。*)
Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).






