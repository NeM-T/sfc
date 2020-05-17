Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import maps.
Require Import types.
Require Import smallstep.



(*
型Tの値が求められている任意のコンテキストで型Sの値が安全に使えるとき、「SはTのサブタイプである」と言い、 S <: T と書きます。 サブタイプの概念はレコードだけではなく、関数、対、など言語のすべての型コンストラクタに適用されます。

example：
      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
      (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}
  を型付け可能に
 *)

(*
この章のゴールは（MoreStlcの拡張機能を持つ）単純型付きラムダ計算にサブタイプを追加することです。 これは2つのステップから成ります：
型の間の二項サブタイプ関係(subtype relation)を定義します。
型付け関係をサブタイプを考慮した形に拡張します。
2つ目のステップは実際はとても単純です。型付け関係にただ1つの規則だけを追加します。 その規則は、包摂規則(rule of subsumption)と呼ばれます：
                         Gamma |- t \in S     S <: T 
                         ---------------------------                    (T_Sub) 
                               Gamma |- t \in T 
この規則は、直観的には、項について知っている情報のいくらかを「忘れる」ようにしてよいと言っています。
 *)

(*
構造規則
                              S <: U    U <: T 
                              ----------------                        (S_Trans) 
                                   S <: T 

                                   ------                              (S_Refl) 
                                   T <: T 

直積型
                            S1 <: T1    S2 <: T2 
                            --------------------                        (S_Prod) 
                             S1 * S2 <: T1 * T2 

関数型
                                  S2 <: T2 
                              ----------------                     (S_Arrow_Co) 
                            S1 -> S2 <: S1 -> T2 

                            T1 <: S1    S2 <: T2 
                            --------------------                      (S_Arrow) 
                            S1 -> S2 <: T1 -> T2 

レコード
                        forall jk in j1..jn, 
                    exists ip in i1..im, such that 
                          jk=ip and Sp <: Tk 
                  ----------------------------------                    (S_Rcd) 
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}
      (左のレコードは(少なくとも)右のレコードのフィールドラベルをすべて持ち、両者で共通するフィールドはサブタイプ関係になければならない)
       分割する
                               n > m 
                 ---------------------------------                 (S_RcdWidth) 
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm} 

                       S1 <: T1  ...  Sn <: Tn 
                  ----------------------------------               (S_RcdDepth) 
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn} 

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn} 
         ---------------------------------------------------        (S_RcdPerm) 
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn} 


Top
                                   --------                             (S_Top) 
                                   S <: Top 
 *)




(*演習skip*)



(*レコード型は省略*)
(*構文*)
Inductive ty : Type :=
  | Top : ty
  | Bool : ty
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | Unit : ty
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | unit : tm
.

(*置換*)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      unit
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(*簡約*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_true :
      value tru
  | v_false :
      value fls
  | v_unit :
      value unit
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(*サブタイプ*)
Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").

Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").


Module Exaple.
Example subtyping_example_0 :
  (Arrow C Bool) <: (Arrow C Top).
Proof. auto. Qed.

Definition Person : ty := 
  Arrow String Top.

Definition Student : ty := 
  Arrow String Float.

Definition Employee : ty := 
  Arrow String Integer.

Example sub_student_person :
  Student <: Person.
Proof. constructor. constructor. constructor. Qed.

Example sub_employee_person :
  Employee <: Person.
Proof. constructor. constructor. constructor. Qed.

Example subtyping_example_1 :
  (Arrow Top Student) <: (Arrow (Arrow C C) Person).
Proof with eauto.
  constructor. constructor. apply sub_student_person. Qed.

Example subtyping_example_2 :
  (Arrow Top Person) <: (Arrow Person Top).
Proof with eauto.
  constructor; constructor. Qed.


End Exaple.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_True : forall Gamma,
       Gamma |- tru \in Bool
  | T_False : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

Lemma sub_inversion_Bool : forall U,
     U <: Bool ->
     U = Bool.
Proof with auto.
  intros U Hs.
  remember Bool as V.
  induction Hs; subst.
  - reflexivity.
  - destruct IHHs1...
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: Arrow V1 V2 ->
     exists U1 U2,
     U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; subst.
  - exists V1, V2. split...
  - specialize (IHHs2 V1 V2). destruct  IHHs2... inversion H. inversion H0. apply IHHs1 in H1.
    inversion H1. inversion H3. inversion H4. inversion H6. inversion H2. exists x1, x2. split.
    assumption. split; eapply S_Trans; eassumption; assumption.
  - inversion HeqV.
  - inversion HeqV. subst. exists S1, S2...
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in Arrow T1 T2 ->
  value s ->
  exists x S1 s2,
     s = abs x S1 s2.
Proof with eauto.
  intros.
  remember (Arrow T1 T2) as V.
  generalize dependent T1. generalize dependent T2.
  induction H; intros; eauto; subst; try solve_by_invert.
  inversion H1. subst.
  apply IHhas_type with (T3:= T2) (T4:= T1)...
  subst. apply sub_inversion_arrow in H1. inversion H1. inversion H4. inversion H5. apply IHhas_type with x0 x...
  subst. apply IHhas_type with S2 S1...
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tru \/ s = fls.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember Bool as T.
  induction Hty; try solve_by_invert...
  -
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  -
    inversion H.
  -
    right.
    destruct IHHt1; subst...
    +
      destruct IHHt2; subst...
      *
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      *
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  -
    right.
    destruct IHHt1.
    + eauto.
    + assert (t1 = tru \/ t1 = fls)
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto.
Qed.



(*
「補題」: もし Gamma |- \x:S1.t2 \in T ならば、型S2が存在して x|->S1; Gamma |- t2 \in S2 かつ S1 -> S2 <: T となる。
（この補題は「Tはそれ自身が関数型である」とは言っていないことに注意します。 そうしたいところですが、それは成立しません!）
 *)
Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (abs x S1 t2) \in T ->
     exists S2,
       Arrow S1 S2 <: T
       /\ (x |-> S1 ; Gamma) |- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (abs x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  -
    exists T12...
  -
    destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_var : forall Gamma x T,
  Gamma |- (var x) \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (var x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  -
    exists T...
  -
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- (app t1 t2) \in T2 ->
  exists T1,
    Gamma |- t1 \in (Arrow T1 T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (app t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  -
    exists T1...
  -
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
  Gamma |- tru \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tru as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
  Gamma |- fls \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember fls as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  Gamma |- (test t1 t2 t3) \in T ->
  Gamma |- t1 \in Bool
  /\ Gamma |- t2 \in T
  /\ Gamma |- t3 \in T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (test t1 t2 t3) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  -
    auto.
  -
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- unit \in T ->
    Unit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember unit as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- (abs x S1 s2) \in (Arrow T1 T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst... Qed.



(*コンテキスト不変性*)
Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
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
      appears_free_in x (test t1 t2 t3)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  -
    apply T_Var... rewrite <- Heqv...
  -
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold update, t_update. destruct (eqb_stringP x x0)...
  -
    apply T_Test...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp;
      subst; inversion Hafi; subst...
  -
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite <- eqb_string_false_iff in H2.
    rewrite H2 in Hctx... Qed.

(*置換*)

(*置換補題*)
Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (x |-> U ; Gamma) |- t \in S ->
     empty |- v \in U ->
     Gamma |- [x:=v]t \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  -
    rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt)
        as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto;
    subst.
    inversion Hctx; subst. clear Hctx.
    apply context_invariance with empty...
    intros x Hcontra.
    destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
    inversion HT'.
  -
    destruct (typing_inversion_app _ _ _ _ Htypt)
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  -
    rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (Arrow T1 T2)... apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    +
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    +
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst.
      rewrite <- eqb_string_false_iff in Hxy. rewrite Hxy...
  -
      assert (Bool <: S)
        by apply (typing_inversion_true _ _ Htypt)...
  -
      assert (Bool <: S)
        by apply (typing_inversion_false _ _ Htypt)...
  -
    assert ((x |-> U ; Gamma) |- t1 \in Bool
         /\ (x |-> U ; Gamma) |- t2 \in S
         /\ (x |-> U ; Gamma) |- t3 \in S)
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  -
    assert (Unit <: S)
      by apply (typing_inversion_unit _ _ Htypt)...
Qed.


(*保存*)
Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  -
    inversion HE; subst...
    +
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T...
Qed.


Module more.

Inductive ty : Type :=
  | Top : ty
  | Bool : ty
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | Unit : ty
  | Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | unit : tm
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
.

(*置換*)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | test t1 t2 t3 =>
      test (subst x s t1) (subst x s t2) (subst x s t3)
  | _ => t
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(*簡約*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_true :
      value tru
  | v_false :
      value fls
  | v_unit :
      value unit
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (pair v1 v2)
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  (*直積*)
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      pair t1 t2 --> pair t1' t2
  | ST_Pair2 : forall t1 t2 t2',
      value t1 ->
      t2 --> t2' ->
      pair t1 t2 --> pair t1 t2'
  | ST_Fst1 : forall t1 t1',
      t1 --> t1' ->
      fst t1 --> fst t1'
  | ST_FstPair : forall v1 v2,
      value (pair v1 v2) ->
      fst (pair v1 v2) --> v1
  | ST_Snd1 : forall t1 t1',
      t1 --> t1' ->
      snd t1 --> snd t1'
  | ST_SndPair : forall v1 v2,
      value (pair v1 v2) ->
      snd (pair v1 v2) --> v2
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(*サブタイプ*)
Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)

  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      (Prod S1 S2) <: (Prod T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_True : forall Gamma,
       Gamma |- tru \in Bool
  | T_False : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (*直積*)
  | T_Pair : forall Gemma t1 t2 T1 T2,
      Gemma |- t1 \in T1 ->
      Gemma |- t2 \in T2 ->
      Gemma |- (pair t1 t2) \in (Prod T1 T2)
  | T_Fst : forall Gemma t T1 T2,
      Gemma |- t \in (Prod T1 T2) ->
      Gemma |- fst t \in T1
  | T_Snd : forall Gemma t T1 T2,
      Gemma |- t \in (Prod T1 T2) ->
      Gemma |- snd t \in T2
  
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.


Lemma sub_inversion_arrow : forall U V1 V2,
     U <: Arrow V1 V2 ->
     exists U1 U2,
     U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; subst.
  - exists V1, V2. split...
  - specialize (IHHs2 V1 V2). destruct  IHHs2... inversion H. inversion H0. apply IHHs1 in H1.
    inversion H1. inversion H3. inversion H4. inversion H6. inversion H2. exists x1, x2. split.
    assumption. split; eapply S_Trans; eassumption; assumption.
  - inversion HeqV.
  - inversion HeqV. subst. exists S1, S2...
  - inversion HeqV.
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in Arrow T1 T2 ->
  value s ->
  exists x S1 s2,
     s = abs x S1 s2.
Proof with eauto.
  intros.
  remember (Arrow T1 T2) as V.
  generalize dependent T1. generalize dependent T2.
  induction H; intros; eauto; subst; try solve_by_invert.
  inversion H1. subst.
  apply IHhas_type with (T3:= T2) (T4:= T1)...
  subst. apply sub_inversion_arrow in H1. inversion H1. inversion H4. inversion H5. apply IHhas_type with x0 x...
  subst. apply IHhas_type with S2 S1...
Qed.


Lemma sub_inversion_Bool : forall U,
     U <: Bool ->
     U = Bool.
Proof with auto.
  intros U Hs.
  remember Bool as V.
  induction Hs; subst; try solve_by_invert.
  - reflexivity.
  - destruct IHHs1...
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tru \/ s = fls.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember Bool as T.
  induction Hty; try solve_by_invert...
  -
    subst. apply sub_inversion_Bool in H. subst...
Qed.


Lemma sub_inversion_prod : forall U V1 V2,
     U <: Prod V1 V2 ->
     exists U1 U2,
     U = Prod U1 U2 /\ U1 <: V1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Prod V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; subst.
  - exists V1, V2. split...
  - specialize (IHHs2 V1 V2). destruct  IHHs2... inversion H. inversion H0. apply IHHs1 in H1.
    inversion H1. inversion H3. inversion H4. inversion H6. inversion H2. exists x1, x2. split.
    assumption. split; eapply S_Trans; eassumption; assumption.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV. subst. exists S1, S2...
Qed.



Lemma canonical_forms_of_Prod : forall Gamma s v1 v2,
  Gamma |- s \in (Prod v1 v2) ->
                value s ->
  exists t1 t2, s = pair t1 t2.
Proof with eauto.
  intros.
  remember (Prod v1 v2) as V.
  generalize dependent v1. generalize dependent v2.
  induction H; intros; eauto; subst; try solve_by_invert.
  inversion H1. subst.
  apply IHhas_type with (v3:= v2) (v4:= v1)...
  subst. apply sub_inversion_prod in H1. inversion H1. inversion H4. inversion H5. apply IHhas_type with x0 x...
  subst. apply IHhas_type with S2 S1...
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - inversion H.
  - right.
    destruct IHHt1; subst...
    +
      destruct IHHt2; subst...
      *
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      *
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  -
    right.
    destruct IHHt1.
    + eauto.
    + assert (t1 = tru \/ t1 = fls)
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto.
  - destruct IHHt1... destruct IHHt2...
    inversion H0. right. eexists. eapply ST_Pair2. assumption. eassumption.
    inversion H. right. eexists. eapply ST_Pair1. eassumption.
  - right. destruct IHHt...
    inversion Ht; subst; try solve_by_invert. 
    eexists. eapply ST_FstPair. assumption.
    apply canonical_forms_of_Prod in Ht... inversion Ht. inversion H2. subst. exists x. constructor. assumption.
    inversion H. eexists. eapply ST_Fst1. apply H0.
  - right. destruct IHHt... inversion Ht; subst; try solve_by_invert. 
    eexists. eapply ST_SndPair. assumption.
    apply canonical_forms_of_Prod in Ht... inversion Ht. inversion H2. subst...
    inversion H. eexists. eapply ST_Snd1. apply H0.
Qed.



Lemma typing_inversion_pair : forall Gamma t1 t2 T,
     Gamma |- (pair t1 t2) \in T ->
     exists S1 S2,
       Prod S1 S2 <: T.
Proof with eauto.
  intros Gamma t1 t2 T H.
  remember (pair t1 t2) as t.
  generalize dependent t1. generalize dependent t2.
  induction H;
    subst; intros; try solve_by_invert.
  -
    exists T1, T2. constructor.
  -
    specialize (IHhas_type t2 t1).
    destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.


Lemma prod_pair : forall Gemma s1 s2 T1 T2,
  Gemma |- (pair s1 s2) \in (Prod T1 T2) ->
     Gemma |- s1 \in T1
  /\ Gemma |- s2 \in T2.
Proof with eauto.
  intros. 

  remember (pair s1 s2) as v.
  induction H; intros; try solve_by_invert.
  admit.

  apply IHhas_type in Heqv. assumption.

Abort.


Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  -
    admit.
  -
    inversion H0; subst.
    inversion HT; subst...

    inversion HE; subst.
    inversion H2.
    

    admit.

  -
    admit.
Abort.

End more.

