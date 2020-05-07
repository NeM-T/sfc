Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import maps.
Require Import smallstep.


(*
       t ::= x variable
           | \x:T1.t2 abstraction
           | t1 t2 application
           | tru constant true
           | fls constant false
           | test t1 then t2 else t3 conditional

 *)

Module STLC.

Inductive ty : Type :=
  | Bool : ty
  | Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Notation idB :=
  (abs x Bool (var x)).

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

Notation idBBBB :=
  (abs x (Arrow (Arrow Bool Bool)
                      (Arrow Bool Bool))
    (var x)).

Notation k := (abs x Bool (abs y Bool (var x))).

Notation notB := (abs x Bool (test (var x) fls tru)).


(*
簡約は関数抽象で止まる。
一般的な関数型言語と同じ。適用する時に評価される
Coqは逆。関数抽象の段階で評価する
*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.

Hint Constructors value.

(*
       [x:=s]x = s
       [x:=s]y = y if x <> y
       [x:=s](\x:T11. t12) = \x:T11. t12
       [x:=s](\y:T11. t12) = \y:T11. [x:=s]t12 if x <> y
       [x:=s](t1 t2) = ([x:=s]t1) ([x:=s]t2)
       [x:=s]tru = tru
       [x:=s]fls = fls
       [x:=s](test t1 then t2 else t3) =
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3

 *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).


Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall y: string,
      x <> y -> substi s x (var y) (var y)
  | s_abs1 : forall T t,
      substi s x (abs x T t) (abs x T t)
  | s_abs2 : forall y T t t',
      x <> y -> substi s x t t' ->
      substi s x (abs y T t) (abs y T t')
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru : substi s x tru tru
  | s_fls : substi s x fls fls
  | s_test : forall t1 t1' t2 t2' t3 t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (test t1 t2 t3) (test t1' t2' t3').

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  split; generalize dependent t'.
  - induction t.
    + unfold subst. intros. destruct (eqb_string x0 s0) eqn: IH; subst.
      apply eqb_string_true_iff in IH; subst.  apply s_var1. apply s_var2. apply eqb_string_false_iff; assumption.
    + intros.
      replace ([x0 := s]app t1 t2) with (app ([x0 := s]t1) ([x0 := s] t2)) in H by reflexivity.
      rewrite <- H. constructor. apply IHt1. reflexivity. apply IHt2. reflexivity.
    + intros. rewrite <- H.  destruct (eqb_string x0 s0) eqn: IH.
      unfold subst. rewrite IH. apply eqb_string_true_iff in IH. rewrite IH. apply s_abs1.
      unfold subst. rewrite IH. apply eqb_string_false_iff in IH. constructor. assumption. apply IHt. reflexivity.
    + intros. rewrite <- H. unfold subst. apply s_tru.
    + intros. rewrite <- H. unfold subst. apply s_fls.
    + intros. rewrite <- H. apply s_test. apply IHt1. reflexivity. apply IHt2. reflexivity. apply IHt3. reflexivity.
  - induction t; intros.
    + inversion H. subst. simpl. rewrite <- eqb_string_refl. reflexivity.
      subst. simpl. apply eqb_string_false_iff in H1. rewrite H1. reflexivity.
    + inversion H; subst. simpl. apply IHt1 in H2. apply IHt2 in H4. subst. reflexivity.
    + inversion H. simpl. subst. rewrite <- eqb_string_refl. reflexivity.
      simpl. subst. apply eqb_string_false_iff in H4. rewrite H4. apply IHt in H5. rewrite H5. reflexivity.
    + inversion H. reflexivity.
    + inversion H; reflexivity.
    + inversion H; subst. apply IHt1 in H3. apply IHt2 in H5. apply IHt3 in H6. subst. reflexivity.
Qed.


(*
ベータ簡約
 *)
(*
                               value v2 
                     ----------------------------                   (ST_AppAbs) 
                     (\x:T.t12) v2 --> [x:=v2]t12 
 
                              t1 --> t1' 
                           ----------------                           (ST_App1) 
                           t1 t2 --> t1' t2 
 
                              value v1 
                              t2 --> t2' 
                           ----------------                           (ST_App2) 
                           v1 t2 --> v1 t2' 

     -------------------------------------------------------------------------------

                    --------------------------------               (ST_TestTru) 
                    (test tru then t1 else t2) --> t1 
 
                    ---------------------------------              (ST_TestFls) 
                    (test fls then t1 else t2) --> t2 
 
                             t1 --> t1' 
      --------------------------------------------------------     (ST_Test) 
      (test t1 then t2 else t3) --> (test t1' then t2 else t3) 
 *)

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
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1 :
  (app idBB idB) -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.

Lemma step_example2 :
  (app idBB (app idBB idB)) -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl. Qed.

Lemma step_example3 :
  app (app idBB notB) tru -->* fls.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_TestTru. apply multi_refl. Qed.

Lemma step_example4 :
  app idBB (app notB tru) -->* fls.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_TestTru.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl. Qed.


Lemma step_example1' :
  app idBB idB -->* idB.
Proof. normalize. Qed.

Lemma step_example2' :
  app idBB (app idBB idB) -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  app (app idBB notB) tru -->* fls.
Proof. normalize. Qed.

Lemma step_example4' :
  app idBB (app notB tru) -->* fls.
Proof. normalize. Qed.

Lemma step_example5 :
       app (app idBBBB idBB) idB
  -->* idB.
Proof. normalize. Qed.

Definition context := partial_map ty.

(*型付け

                              Gamma x = T 
                            ----------------                            (T_Var) 
                            Gamma |- x \in T 
 
                   (x |-> T11 ; Gamma) |- t12 \in T12 
                   ----------------------------------                   (T_Abs) 
                    Gamma |- \x:T11.t12 \in T11->T12 
 
                        Gamma |- t1 \in T11->T12 
                          Gamma |- t2 \in T11 
                         ----------------------                         (T_App) 
                         Gamma |- t1 t2 \in T12 
 
                         ---------------------                          (T_Tru) 
                         Gamma |- tru \in Bool 
 
                         ---------------------                          (T_Fls) 
                         Gamma |- fls \in Bool 
 
       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T 
       --------------------------------------------------------------   (T_Test) 
                  Gamma |- test t1 then t2 else t3 \in T 

 *)

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
  | T_Tru : forall Gamma,
       Gamma |- tru \in Bool
  | T_Fls : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Example typing_example_1 :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof.
  apply T_Abs. apply T_Var. reflexivity. Qed.

Example typing_example_1' :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. auto. Qed.



Example typing_example_2 :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

Example typing_example_3 :
  exists T,
    empty |-
      (abs x (Arrow Bool Bool)
         (abs y (Arrow Bool Bool)
            (abs z Bool
               (app (var y) (app (var x) (var z)))))) \in
      T.
Proof with auto.
  exists (Arrow (Arrow Bool Bool) (Arrow (Arrow Bool Bool) (Arrow Bool Bool ) ) ).
  apply T_Abs. apply T_Abs.
  apply T_Abs. eapply T_App. apply T_Var. reflexivity.
  eapply T_App. apply T_Var. reflexivity. apply T_Var. reflexivity.
Qed.


Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (abs x Bool
            (abs y Bool
               (app (var x) (var y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1. Qed.


Lemma no_infinite_nested_type :
  ~ (exists T, exists S, T = Arrow T S).
Proof.
  intros Hc. inversion Hc as [T H]. clear Hc. induction T.
  inversion H. inversion H0.
  inversion H. inversion H0. apply IHT1. exists T2. assumption.
Qed.


Example typing_nonexample_3 :
  (exists S T,
        empty |-
          (abs x S
             (app (var x) (var x))) \in
          T) -> False.
Proof.
 intros Hc. inversion Hc as [S H]. clear Hc.
  inversion H as [T H1]. subst.
  inversion H1. subst. clear H1.
  inversion H6. subst. clear H6.
  inversion H3. subst. clear H3.
  inversion H2. subst. inversion H5. subst. rewrite H2 in H3. inversion H3.
  symmetry in H1. apply no_infinite_nested_type. exists T11. exists T12. assumption.
Qed.


End STLC.

