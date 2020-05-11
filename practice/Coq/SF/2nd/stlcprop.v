Set Warnings "-notation-overridden,-parsing".
Require Import maps.
Require Import types.
Require Import stlc.
Require Import smallstep.


Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  (t = tru) \/ (t = fls).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (Arrow T1 T2) ->
  value t ->
  exists x u, t = abs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0, t0. auto.
Qed.


Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  -
    
    inversion H.

  -
    
    right. destruct IHHt1...
    +
      destruct IHHt2...
      *
        assert (exists x0 t0, t1 = abs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      *
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...

    +
      inversion H as [t1' Hstp]. exists (app t1' t2)...

  -
    right. destruct IHHt1...

    +
      destruct (canonical_forms_bool t1); subst; eauto.

    +
      inversion H as [t1' Hstp]. exists (test t1' t2 t3)...
Qed.

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  inversion Ht; subst. inversion H1.

  inversion Ht; subst. apply IHt1 in H2. apply IHt2 in H4.
  inversion H2. inversion H4.
  inversion H. right. exists ([x0:=t2]t). apply ST_AppAbs. assumption.
  subst. inversion Ht; subst. inversion H6. inversion Ht; subst. inversion H7.
  inversion H0. right. exists (app t1 x0). constructor; assumption.
  inversion H. right. exists (app x0 t2). constructor; assumption.

  inversion Ht; subst. apply IHt2 in H5. apply IHt3 in H6. right.
   apply IHt1 in H3. inversion Ht. subst. inversion H3.
   apply canonical_forms_bool in H4. inversion H4; subst.
   exists t2. apply ST_TestTru. exists t3. apply ST_TestFls. assumption.
   inversion H. exists (test x0 t2 t3). apply ST_Test. assumption.
Qed.


(*
example:
y appears free, but x does not, in \x:T->U. x y
both x and y appear free in (\x:T->U. x y) x
no variables appear free in \x:T->U. \y:T. x y
 *)
Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3).

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  -
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
  unfold closed, not. intros.
  apply free_in_context with (x:=x0) (t:=t) (T:=T) (Gamma:=empty) in H0.
  inversion H0. inversion H1. assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  -
    apply T_Var. rewrite <- H0...
  -
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    unfold update. unfold t_update. destruct (eqb_string x0 x1) eqn: Hx0x1...
    rewrite eqb_string_false_iff in Hx0x1. auto.
  -
    apply T_App with T11...
Qed.


(*
置換が型を持つ証明
  U型＝閉じている仮定
 *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    
    inversion H; subst; simpl...
  -
    rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
    +
      subst.
      rewrite update_eq in H2.
      inversion H2; subst.
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros. apply (Ht' x0) in H0. inversion H0.
    +
      apply T_Var. rewrite update_neq in H2...
  -
    rename s into y. rename t into T. apply T_Abs.
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    +
      subst. rewrite update_shadow in H5. apply H5.
    +
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T ->
  t --> t' ->
  empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  -
    inversion HE; subst...
    +
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.


Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  apply progress in Hhas_type. inversion Hhas_type.
    apply Hnot_val; assumption. apply Hnf in H; assumption.
  apply IHHmulti; try assumption. eapply preservation. apply Hhas_type. assumption.
Qed.

Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros. generalize dependent T'. induction H; intros.
  inversion H0; subst. rewrite H in H3. inversion H3. reflexivity.
  inversion H0; subst. apply IHhas_type in H6. rewrite H6. reflexivity.
  inversion H1; subst. apply IHhas_type1 in H5. inversion H5. reflexivity.
  inversion H0. reflexivity. inversion H0. reflexivity.
  inversion H2; subst. apply IHhas_type2 in H9. assumption.
Qed.

End STLCProp.


Module STLCArith.
Import STLC.

Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_nat : forall n,
      value (const n).

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | const n =>
      const n
  | scc t1 =>
      scc ([x:= s] t1)
  | prd t1 =>
      prd ([x:=s]t1)
  | mlt t1 t2 =>
      mlt ([x:=s]t1) ([x:=s]t2)
  | test0 t1 t2 t3 =>
      test0 ([x:=s]t1) ([x:=s]t2) ([x:=s]t3)

  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 ->
      (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      app v1 t2 --> app v1 t2'
  | ST_SccNat : forall n,
      scc (const n) --> const (S n)
  | ST_Scc : forall t1 t1',
      t1 --> t1' -> scc t1 --> scc t1'
  | ST_PrdNat : forall n,
      prd (const n) --> const (pred n)
  | ST_Prd : forall t1 t1',
      t1 --> t1' -> prd t1 --> prd t1'
  | ST_MltNat2 : forall n1 n2,
      mlt (const n1) (const n2) --> const (n1 * n2)
  | ST_MltNat1 : forall n1 t2 t2',
      t2 --> t2' ->
      mlt (const n1) t2 --> mlt (const n1) t2'
  | ST_Mlt : forall t1 t1' t2,
      t1 --> t1' ->
      mlt t1 t2 --> mlt t1' t2
  | ST_Test0 : forall t1 t2,
      (test0 (const 0) t1 t2) --> t1
  | ST_TestNot0 : forall n1 t1 t2,
      n1 <> 0 ->
      (test0 (const n1) t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test0 t1 t2 t3) --> (test0 t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in Arrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- app t1 t2 \in T12
  | T_Nat : forall Gemma n,
      Gemma |- (const n) \in Nat
  | T_Scc : forall Gemma t1,
      Gemma |- t1 \in Nat ->
      Gemma |- scc t1 \in Nat
  | T_Prd : forall Gemma t1,
      Gemma |- t1 \in Nat ->
      Gemma |- prd t1 \in Nat
  | T_Mlt : forall Gemma t1 t2,
      Gemma |- t1 \in Nat ->
      Gemma |- t2 \in Nat ->
      Gemma |- mlt t1 t2 \in Nat
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Nat ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_scc : forall x t,
      appears_free_in x t ->
      appears_free_in x (scc t)
  | afi_prd : forall x t,
      appears_free_in x t ->
      appears_free_in x (prd t)
  | afi_mlt1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (mlt t1 t2)
  | afi_mlt2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (mlt t1 t2)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test0 t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test0 t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test0 t1 t2 t3).


Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with auto.
  intros.  generalize dependent Gamma'.
  induction H; intros; auto.
  - 
    constructor. rewrite <- H. symmetry. apply H0. apply afi_var.
  -
    constructor. apply IHhas_type. intros. unfold update. unfold t_update. destruct (eqb_string x0 x1) eqn: Hx0x1...
    apply H0. constructor. apply eqb_string_false_iff. assumption. assumption.
  -
    apply T_App with (T11:= T11); specialize (IHhas_type1 Gamma'); specialize (IHhas_type2 Gamma').
    apply IHhas_type1. intros. apply H1. constructor. assumption.
    apply IHhas_type2. intros. apply H1. apply afi_app2. assumption.
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  inversion H1; subst.
  apply IHappears_free_in in H7.
  rewrite update_neq in H7; assumption.
Qed.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.


Corollary typable_empty__closed : forall t T,
    empty |- t \in T ->
    closed t.
Proof.
  unfold closed, not. intros.
  apply free_in_context with (x:=x0) (t:=t) (T:=T) (Gamma:=empty) in H0.
  inversion H0. inversion H1. assumption.
Qed.


Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty |- v \in U ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    inversion H; subst; simpl...
  - 
    rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
    +
      subst.
      rewrite update_eq in H2. 
      inversion H2; subst.
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros. apply (Ht' x0) in H0. inversion H0.
    +
      apply T_Var. rewrite update_neq in H2...
  -
    rename s into y. rename t into T. apply T_Abs.
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    +
      subst. rewrite update_shadow in H5. apply H5.
    +
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- eqb_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

Theorem preservation : forall t t' T,
  empty |- t \in T ->
  t --> t' ->
  empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE;  subst;
       try solve [inversion HE; subst; auto].
  -
    inversion HE; subst...
    +
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

Lemma canonical_forms_nat : forall t,
  empty |- t \in Nat ->
  value t ->
  (exists n, t = (const n)).
Proof.
  intros t HT HVal. 
  inversion HVal; intros; subst.
  inversion HT.
  destruct n. exists 0. reflexivity. exists (S n). reflexivity.
Qed.


Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (Arrow T1 T2) ->
  value t ->
  exists x u, t = abs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0, t0. auto.
Qed.


Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst...
  -
    
    inversion H.

  -
    
    right. destruct IHHt1...
    +
      destruct IHHt2...
      *
        assert (exists x0 t0, t1 = abs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      *
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...

    +
      inversion H as [t1' Hstp]. exists (app t1' t2)...

  -
     destruct IHHt...

    +
      apply canonical_forms_nat in Ht... inversion Ht.
      right. subst. exists (const (S x0)). constructor.
    +
      inversion H. right. exists (scc x0). constructor. assumption.
  -
    destruct IHHt...
    + destruct (canonical_forms_nat t1); subst; eauto.
    + inversion H. right. exists (prd x0); constructor; assumption.
  -
    destruct IHHt1... destruct IHHt2... apply canonical_forms_nat in H... apply canonical_forms_nat in H0...
    inversion H; inversion H0; subst. right. exists (const (x0 * x1)). constructor.
    apply canonical_forms_nat in H... inversion H; inversion H0; subst; right. exists (mlt (const x0) x1); constructor; assumption.
    inversion H. right. exists (mlt x0 t2); constructor; assumption.
  -
    right. destruct IHHt1... apply canonical_forms_nat in H...
    inversion H; subst. destruct x0. exists t2. constructor. exists t3. constructor...
    inversion H. exists (test0 x0 t2 t3)...
Qed.

End STLCArith.
