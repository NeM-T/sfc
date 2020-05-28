Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import maps.
Require Import smallstep.
Require Import morestlc.


(* 構文 *)
Inductive ty : Type :=
  
  | Top : ty
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  
  | RNil : ty
  | RCons : string -> ty -> ty -> ty.

Inductive tm : Type :=
  
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | rproj : tm -> string -> tm
  
  | rnil : tm
  | rcons : string -> tm -> tm -> tm.

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty RNil
  | RTcons : forall i T1 T2,
        record_ty (RCons i T1 T2).

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm rnil
  | rtcons : forall i t1 t2,
        record_tm (rcons i t1 t2).

Inductive well_formed_ty : ty -> Prop :=
  | wfTop :
        well_formed_ty Top
  | wfBase : forall i,
        well_formed_ty (Base i)
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (Arrow T1 T2)
  | wfRNil :
        well_formed_ty RNil
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (RCons i T1 T2).

Hint Constructors record_ty record_tm well_formed_ty.


(* 置換 *)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if eqb_string x y then s else t
  | abs y T t1 => abs y T (if eqb_string x y then t1
                             else (subst x s t1))
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | rproj t1 i => rproj (subst x s t1) i
  | rnil => rnil
  | rcons i t1 tr2 => rcons i (subst x s t1) (subst x s tr2)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* 簡約 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_rnil : value rnil
  | v_rcons : forall i v vr,
      value v ->
      value vr ->
      value (rcons i v vr).

Hint Constructors value.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | RCons i' T Tr' =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | rcons i' t tr' =>
      if eqb_string i i' then Some t else tlookup i tr'
  | _ => None
  end.

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
  | ST_Proj1 : forall tr tr' i,
        tr --> tr' ->
        (rproj tr i) --> (rproj tr' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
       (rproj tr i) --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        (rcons i t1 tr2) --> (rcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        (rcons i v1 tr2) --> (rcons i v1 tr2')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.


(* サブタイプ *)
Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    Arrow S1 S2 <: Arrow T1 T2
  
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty (RCons i T1 T2) ->
    RCons i T1 T2 <: RNil
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    RCons i S1 Sr2 <: RCons i T1 Tr2
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty (RCons i1 T1 (RCons i2 T2 Tr3)) ->
    i1 <> i2 ->
       RCons i1 T1 (RCons i2 T2 Tr3)
    <: RCons i2 T2 (RCons i1 T1 Tr3)

where "T '<:' U" := (subtype T U).

Hint Constructors subtype.


(*サブタイプの性質*)
Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
Proof with eauto.
  intros S T Hsub.
  induction Hsub;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  -
    split... inversion H. subst. inversion H5... Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  -
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)... inversion H0; subst... Qed.


(*
フィールド参照
  サブタイプがあることで、レコードマッチング補題はいくらか複雑になります。
  それには2つの理由があります。
  1つはレコード型が対応する項の正確な構造を記述する必要がなくなることです。
  2つ目は、has_typeの導出に関する帰納法を使う推論が一般には難しくなることです。 なぜなら、has_typeが構文指向ではなくなるからです。
 *)
Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget. generalize dependent Ti.
  induction Hsub; intros Ti Hget;
    try solve_by_invert.
  -
    exists Ti...
  -
    destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
    destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
    exists Si...
  -
    rename i0 into k.
    unfold Tlookup. unfold Tlookup in Hget.
    destruct (eqb_string i k)...
    +
      inversion Hget. subst. exists S1...
  -
    exists Ti. split.
    +
      unfold Tlookup. unfold Tlookup in Hget.
      destruct (eqb_stringP i i1)...
      *
        destruct (eqb_stringP i i2)...
        destruct H0.
        subst...
    +
      inversion H. subst. inversion H5. subst... Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     subtype U (Arrow V1 V2) ->
     exists U1 U2,
       (U=(Arrow U1 U2)) /\ (subtype V1 U1) /\ (subtype U2 V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1. induction Hs; intros; subst; try solve_by_invert.
  -
    inversion H; subst. exists V1, V2...
  -
    inversion Hs2.
    +
      inversion H; subst; apply IHHs1...
    +
      subst. specialize (IHHs2 V1 V2). destruct IHHs2...
      inversion H1. inversion H2. inversion H4; subst.
      specialize (IHHs1 x x0). destruct IHHs1...
      inversion H3. inversion H7; subst. inversion H9.
      exists x1, x2...
    +
      symmetry in H1. apply IHHs1 in H1. inversion H1. inversion H4.
      inversion H5. inversion H7; subst. exists x, x0. split...
  -
    inversion HeqV. subst. exists S1, S2...
Qed.



(* --------型付け------- *)
Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |- rproj t i \in Ti
  
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      subtype S T ->
      Gamma |- t \in T
  
  | T_RNil : forall Gamma,
      Gamma |- rnil \in RNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- rcons i t tr \in RCons i T Tr

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Module Examples.
Open Scope string_scope.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").

Definition TRcd_j :=
  (RCons j (Arrow B B) RNil). Definition TRcd_kj :=
  RCons k (Arrow A A) TRcd_j.

Definition trcd_kj :=
  (rcons k (abs z A (var z))
           (rcons j (abs z B (var z))
                      rnil)).

Example typing_example_0 :
  has_type empty
           (rcons k (abs z A (var z))
                     (rcons j (abs z B (var z))
                               rnil))
           TRcd_kj.
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  apply T_RCons. apply T_Abs. apply wfBase.
  apply T_Var. reflexivity. apply wfBase.
  apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase.
  apply T_RNil. apply RTnil. apply rtnil. apply RTcons. apply rtcons.
Qed.

Example subtyping_example_0 :
  subtype (Arrow C TRcd_kj)
          (Arrow C RNil).
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
    unfold TRcd_kj, TRcd_j. apply S_RcdWidth; auto.
Qed.

Example subtyping_example_1 :
  subtype TRcd_kj TRcd_j.
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  eapply S_Trans.
  apply S_RcdPerm...
  intros H; inversion H.
  apply S_RcdDepth...
Qed.

Example typing_example_1 :
  has_type empty
           (app (abs x TRcd_j (rproj (var x) j))
                   (trcd_kj))
           (Arrow B B).
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  eapply T_App. apply T_Abs. apply wfRCons. apply wfArrow. apply wfBase. apply wfBase. apply wfRNil. apply RTnil.
  econstructor. apply T_Var. reflexivity. apply wfRCons. apply wfArrow; apply wfBase. apply wfRNil. apply RTnil.
  reflexivity.
  unfold trcd_kj. econstructor. apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase.
  apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase. apply T_RNil. apply RTnil. apply rtnil.
  apply RTcons. apply rtcons.
  apply subtyping_example_1.
Qed.


Example typing_example_2 :
  has_type empty
           (app (abs z (Arrow (Arrow C C) TRcd_j)
                           (rproj (app (var z)
                                            (abs x C (var x)))
                                    j))
                   (abs z (Arrow C C) trcd_kj))
           (Arrow B B).
Proof with eauto.
  unfold trcd_kj, TRcd_j.
  eapply T_App. apply T_Abs. apply wfArrow. apply wfArrow; apply wfBase. apply wfRCons.
  apply wfArrow; apply wfBase. apply wfRNil. apply RTnil.
  econstructor. eapply T_App.
  apply T_Var. reflexivity. apply wfArrow. apply wfArrow; apply wfBase. apply wfRCons.
  apply wfArrow; apply wfBase. apply wfRNil. apply RTnil.
  apply T_Abs. apply wfBase.
  apply T_Var. reflexivity. apply wfBase. reflexivity.
  apply T_Abs. apply wfArrow; apply wfBase.
  econstructor.
  apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase.
  apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase.
  apply T_RNil. apply RTnil. apply rtnil. apply RTcons. apply rtcons.
  apply subtyping_example_1.
Qed.

End Examples.

(* 型付けの性質 *)

(* Well-Formedness *)

Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  -
    inversion IHHtyp1...
  -
    eapply wf_rcd_lookup...
  -
    apply subtype__wf in H.
    destruct H...
Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; eauto.
Qed.

(* フィールド参照 *)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  has_type empty v T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ has_type empty vi Ti.
Proof with eauto.
  remember empty as Gamma.
  intros t T i Ti Hval Htyp. revert Ti HeqGamma Hval.
  induction Htyp; intros; subst; try solve_by_invert.
  -
    apply (rcd_types_match S) in H0...
    destruct H0 as [Si [HgetSi Hsub]].
    destruct (IHHtyp Si) as [vi [Hget Htyvi]]...
  -
    simpl in H0. simpl. simpl in H1.
    destruct (eqb_string i i0).
    +
      inversion H1. subst. exists t...
    +
      destruct (IHHtyp2 Ti) as [vi [get Htyvi]]...
      inversion Hval... Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     has_type Gamma s (Arrow T1 T2) ->
     value s ->
     exists x S1 s2,
        s = abs x S1 s2.
Proof with eauto.
  intros.

  destruct s; intros; eauto; try solve_by_invert.
  inversion H. subst.
  remember (Arrow T1 T2) as SS.
  revert HeqSS. generalize dependent S.
  induction H; intros; try solve_by_invert.
  inversion HeqSS; subst...
  subst... admit.
  admit.
Admitted.



Theorem progress : forall t T,
     has_type empty t T ->
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
        destruct H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      destruct H as [t1' Hstp]. exists (app t1' t2)...
  -
    right. destruct IHHt...
    +
      destruct (lookup_field_in_value t T i Ti)
        as [t' [Hget Ht']]...
    +
      destruct H0 as [t' Hstp]. exists (rproj t' i)...
  -
    destruct IHHt1...
    +
      destruct IHHt2...
      *
        right. destruct H2 as [tr' Hstp].
        exists (rcons i t tr')...
    +
      right. destruct H1 as [t' Hstp].
      exists (rcons i t' tr)... Qed.

(* 反転補題 *)

Lemma typing_inversion_var : forall Gamma x T,
  has_type Gamma (var x) T ->
  exists S,
    Gamma x = Some S /\ subtype S T.
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
  has_type Gamma (app t1 t2) T2 ->
  exists T1,
    has_type Gamma t1 (Arrow T1 T2) /\
    has_type Gamma t2 T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (app t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  -
    exists T1...
  -
    destruct IHHty as [U1 [Hty1 Hty2]]...
    assert (Hwf := has_type__wf _ _ _ Hty2).
    exists U1... Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     has_type Gamma (abs x S1 t2) T ->
     (exists S2, subtype (Arrow S1 S2) T
              /\ has_type (update Gamma x S1) t2 S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (abs x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  -
    assert (Hwf := has_type__wf _ _ _ H0).
    exists T12...
  -
    destruct IHhas_type as [S2 [Hsub Hty]]...
    Qed.

Lemma typing_inversion_proj : forall Gamma i t1 Ti,
  has_type Gamma (rproj t1 i) Ti ->
  exists T Si,
    Tlookup i T = Some Si /\ subtype Si Ti /\ has_type Gamma t1 T.
Proof with eauto.
  intros Gamma i t1 Ti H.
  remember (rproj t1 i) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  -
    assert (well_formed_ty Ti) as Hwf.
    {
      apply (wf_rcd_lookup i T Ti)...
      apply has_type__wf in H... }
    exists T, Ti...
  -
    destruct IHhas_type as [U [Ui [Hget [Hsub Hty]]]]...
    exists U, Ui... Qed.

Lemma typing_inversion_rcons : forall Gamma i ti tr T,
  has_type Gamma (rcons i ti tr) T ->
  exists Si Sr,
    subtype (RCons i Si Sr) T /\ has_type Gamma ti Si /\
    record_tm tr /\ has_type Gamma tr Sr.
Proof with eauto.
  intros Gamma i ti tr T Hty.
  remember (rcons i ti tr) as t.
  induction Hty;
    inversion Heqt; subst...
  -
    apply IHHty in H0.
    destruct H0 as [Ri [Rr [HsubRS [HtypRi HtypRr]]]].
    exists Ri, Rr...
  -
    assert (well_formed_ty (RCons i T Tr)) as Hwf.
    {
      apply has_type__wf in Hty1.
      apply has_type__wf in Hty2... }
    exists T, Tr... Qed.

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
  inversion Heq; subst... Qed.

(* コンテキスト不変性 *)

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
  | afi_proj : forall x t i,
      appears_free_in x t ->
      appears_free_in x (rproj t i)
  | afi_rhead : forall x i t tr,
      appears_free_in x t ->
      appears_free_in x (rcons i t tr)
  | afi_rtail : forall x i t tr,
      appears_free_in x tr ->
      appears_free_in x (rcons i t tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' t S.
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
    apply T_App with T1...
  -
    apply T_RCons... Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; subst; inversion Hafi; subst...
  -
    destruct (IHHtyp H5) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx... Qed.

(* 保存 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (update Gamma x U) t S ->
     has_type empty v U ->
     has_type Gamma ([x:=v]t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  -
    rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y)...
    +
      subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    +
      destruct (subtype__wf _ _ Hsub)...
  -
    destruct (typing_inversion_app _ _ _ _ Htypt)
      as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  -
    rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    destruct (subtype__wf _ _ Hsub) as [Hwf1 Hwf2].
    inversion Hwf2. subst.
    apply T_Sub with (Arrow T1 T2)... apply T_Abs...
    destruct (eqb_stringP x y).
    +
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    +
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst. rewrite false_eqb_string...
  -
    destruct (typing_inversion_proj _ _ _ _ Htypt)
      as [T [Ti [Hget [Hsub Htypt1]]]]...
  -
    eapply context_invariance...
    intros y Hcontra. inversion Hcontra.
  -
    destruct (typing_inversion_rcons _ _ _ _ _ Htypt) as
      [Ti [Tr [Hsub [HtypTi [Hrcdt2 HtypTr]]]]].
    apply T_Sub with (RCons s Ti Tr)...
    apply T_RCons...
    +
      apply subtype__wf in Hsub. destruct Hsub. inversion H0...
    +
      inversion Hrcdt2; subst; simpl... Qed.

Theorem preservation : forall t t' T,
     has_type empty t T ->
     t --> t' ->
     has_type empty t' T.
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
  -
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Hty]].
    rewrite H4 in Hget. inversion Hget. subst...
  -
    eauto using step_preserves_record_tm. Qed.

