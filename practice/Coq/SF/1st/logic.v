Set Warnings "-notation-overridden,-parsing".
From LF Require Export tactics.

(*命題に名前付けられるよ。嬉しいね。*)
Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(*論理積の書き方*)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(*and_introでsplitと同じことができる*)
Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros [] []. split.
  reflexivity. reflexivity. discriminate. discriminate. discriminate.
Qed.


(*仮説の論理積の分解方法
   destruct H as [Hn Hm] | 
   intros [Hn Hm]*)
Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(*論理積をHn -> Hmで表記できるけど論理積の扱いは理解しよう*)


Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.


Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof. intros P Q [HP HQ].
       apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Check and. (*Prop -> Prop -> Prop*)


(*------------論理和----------------*)
Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  -
    rewrite Hn. reflexivity.
  -
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(*論理和なんだから証明は片方でいいじゃん！！*)
Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [] [] H. - left. reflexivity. - left. reflexivity.
  - right. reflexivity. - discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof. intros P Q [HP | HQ]. right. apply HP. left. apply HQ.
Qed.  


Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.


Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P notP Q HP. destruct notP. apply HP.
Qed.  

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. discriminate.
Qed.


Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem  double_neg' : forall P : Prop,
  P -> ~~P.
Proof.
  unfold not. intros. apply H0. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not. intros. apply H in H1. apply H0 in H1. apply H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  unfold not. intros P H. destruct H. apply H0 in H. apply H.
Qed.


(*true = false などの矛盾したゴールのときは
　apply ex_falso_quodlibet.
　でFalseをゴールに設定できる*)
Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  -
    reflexivity.
Qed.

(*exfalso.はapply ex_falso_quodlibet.の代わりに使える*)
Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    exfalso.     apply H. reflexivity.
  - reflexivity.
Qed.

(*定数Iは予めTrueに設定されている*)
Lemma True_is_true : True.
Proof. apply I. Qed.



(*---------------------------------------*)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.


Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  -
    intros H. rewrite H. intros H'. discriminate H'.
Qed.


Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  split. 
  - intros. apply H.
  - intros. apply H.
Qed.


Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  split. intros.
  - apply H0. apply H. apply H1.
  - intros. apply H. apply H0. apply H1.
Qed.


Theorem or_distributes_over_and1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  split.
  - inversion H as [HP | [HQ HR]].
     + left. apply HP. 
     + right.  apply HQ.
  - inversion H as [HP | [HQ HR]].
     + left.  apply HP. 
     + right. apply HR.
Qed.

From Coq Require Import Setoids.Setoid.


Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split. 
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.


Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.


(*exists == ∃*)
Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.


Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].   exists (2 + m).
  apply Hm. Qed.


Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros H1. destruct H1. apply H0. apply H.
Qed.


Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H as [m Hm]. inversion Hm as [HP | HQ].
     + apply or_introl. exists m. apply HP.
     + apply or_intror. exists m. apply HQ.
  - intros. inversion H as [HH | H0]. inversion HH as [m  H2].
     + exists m. apply or_introl. apply H2.
     + inversion H0. exists x. apply or_intror. apply H1.
Qed.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  -
    simpl. intros [].
  -
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  induction l as [|h t].
  - simpl. intros [].
  - simpl. intros [].
    + exists h. split. apply H. left. reflexivity.
    + apply IHt in H. destruct H as [w [F I]].
      exists w. split. apply F. right. apply I.
  - intros [w [F I]].
    rewrite <- F. apply In_map. apply I.
Qed.


Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => (P x') \/ All P l'
  end.


Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n =>
    match oddb n with
      | true => Podd n
      | false => Peven n
    end.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold combine_odd_even. destruct (oddb n). 
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros A B n. unfold combine_odd_even. destruct (oddb n).
  + intros. apply H.
  + intros. discriminate H0.
Qed. 


Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros A B n.  unfold combine_odd_even. destruct (oddb n).
  + intros. discriminate. 
  + intros. apply H.
Qed.

Check plus_comm. (*forall n m : nat, n + m = m + n*)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm. (*y + z + x = z + y + x*)
  rewrite plus_comm. (*x + (y + z) = z + y + x*)
Abort.


Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.


Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.




(*------------Coq VS Set Theory-------*)

(*関数の等価性*)
Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(*(forall x, f x = g x) -> f = g
　　が組み込み論理ではない*)
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

(*AxiomはAdmittedと同じ役割をするが、あとで証明するわけではないことを明示する*)
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.


(*Print Assumptions ：自分で追加した公理に依存しているか確認*)
Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros. apply functional_extensionality.
  intros l. unfold tr_rev. induction l.
  - unfold tr_rev. simpl. reflexivity.
  - simpl. rewrite <- IHl.
    assert ( H: forall T l1 l2, @rev_append T l1 l2 = @rev_append T l1 [] ++ l2).
    { intros T. induction l1 as [|h' t'].
      - reflexivity.
      - simpl. rewrite IHt'. intros. 
        rewrite (IHt' (h'::l2)).
        rewrite <- app_assoc. reflexivity. }
    apply H.
Qed.

(*偶数の確認方法*)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.
Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros. induction n.
  - simpl. exists 0. reflexivity.
  - rewrite evenb_S. destruct IHn as [w H].
    destruct (evenb n).
    + simpl. exists w. rewrite H. reflexivity.
    + simpl. exists (S w). rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 == n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(*bool値はreflexivityでできる*)
Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.
Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.
Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.


Lemma plus_eqb_example : forall n m p : nat,
    n == m = true -> n + p == m + p = true.
Proof.
  intros n m p H.
    apply eqb_eq in H.
  rewrite H.
  apply eqb_eq.
  reflexivity.
Qed.


Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros [] []. split.
  - intros. split. reflexivity. reflexivity. 
  - intros. reflexivity.
  - simpl. split. discriminate. intros. apply proj2 in H. apply H. 
  - split. intros. discriminate. intros. simpl. apply proj1 in H. apply H.
  - simpl. split. discriminate. intros. apply proj1 in H. apply H.
Qed.


Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros [] [].  split.
  - intros. left. reflexivity.
  - intros. simpl. reflexivity.
  - simpl. split. intros. left. reflexivity. intros. reflexivity.
  - simpl. split. intros. right. reflexivity. intros. reflexivity.
  - simpl. split. intros. discriminate. intros. Search or. induction H. apply H. apply H.
Qed.

Theorem eqb_neq : forall x y : nat,
  x == y = false <-> ~(x = y).
Proof.
  intros x y. unfold not.
  destruct (x == y) eqn:IH. split.
  -  discriminate.
  -  intros. rewrite <- IH. apply eqb_true in IH. destruct H. apply IH.
  - split. intros. destruct H0. rewrite eqb_nn in IH. discriminate.
      + intros. reflexivity.
Qed.


Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1 with
  | nil => match l2 with 
           | nil => true
           | _   => false
           end
  | h1 :: t1 => match l2 with
                | nil => false
                | h2 :: t2 => if (eqb h1 h2) then eqb_list eqb t1 t2
                                             else false
                end
end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H.
  induction l1 as [| a t IH].
  - destruct l2.
    + split.
      intros _. reflexivity.
      intros _. reflexivity.
    + split.
      * intros H'. discriminate.
      * intros H'. discriminate.
  - destruct l2.
    + split.
      * intros H'. discriminate.
      * intros H'. discriminate.
    + simpl. split.
      * intros H'. apply andb_true_iff in H'.
        destruct H' as [H1 H2].
        apply H in H1.
        apply IH in H2.
        rewrite H1, H2.
        reflexivity.
      * intros H'.
        injection H' as H1 H2.
        apply H in H1.
        apply IH in H2.
        rewrite H1, H2.
        reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.


Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split.
  - induction l. simpl. + intro. reflexivity.
      + simpl. intros. apply andb_true_iff in H. left. apply proj1 in H. apply H.
  - induction l. simpl. intro. reflexivity. 
      + simpl. intros H. apply andb_true_iff. induction (forallb test l).
Admitted.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. unfold not. intros. apply H in H0. discriminate.
Qed.

Theorem prop_no : forall (P : Prop),
  P -> ~~P.
Proof.
  intros. unfold not. intros. apply H0. apply H.
Qed.


Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros. apply H. right.
  intros. apply H. left. apply H0.
Qed.


Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. intros H X P H0 a. 
   assert ( P a \/ ~ P a).  apply H.
   inversion H1. apply H2. apply ex_falso_quodlibet.
   unfold not in H0. apply H0. unfold not in H2. exists a.
   apply H2.
Qed.
  


(*以下の４つとexcluded_middle は等価である証明
  できたらやる。*)
Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).


Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split. induction l.
  - simpl. intros. right. apply H.
  - simpl. induction l'.
      + simpl. rewrite app_nil_r. rewrite app_nil_r in IHl. simpl in IHl. intros. left. apply H.
      + simpl. simpl in IHl. intros.
Admitted.

(*
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
 intros P Q R H. inversion H. inversion H0.
 - left. apply H2.
 - apply  or_commut in H0. Search and. apply proj1 in H0. inversion H1.
    + left. apply H3.
    + apply (and_commut R Q). Search and. rewrite proj2. generalize dependent H2. apply (or_intror R Q ). apply or_commut in H1. apply  Search or. split. 
    + right.  Search and. apply (proj2 Q R).  apply H.





Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - induction l as [|h t].
    + reflexivity.
    + intros. simpl.
      left. apply H. simpl. left. reflexivity.
  - induction l as [|h t].
    + intros. inversion H0.
    + intros. simpl in H0. simpl in H.  
      apply IHt. generalize dependent H. Search or. apply or_comm.
 apply proj2 with (P h ). Search and. in H.  apply H. inversion H.
      inversion H0. apply or_intro in H. inversion H. rewrite H1 in H2.
      apply H2. 
      destruct H as [PH | APT].*)

