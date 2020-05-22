Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import maps.
Require Import imp.
Require Import smallstep.
Require Import stlc.

(*レコードの形式化*)
(*
前の非形式的定義

構文:
       t ::=                          項:
           | {i1=t1, ..., in=tn}         レコード
           | t.i                         射影
           | ... 
 
       v ::=                          値:
           | ... 
           | {i1=v1, ..., in=vn}         レコード値
 
       T ::=                          型:
           | ... 
           | {i1:T1, ..., in:Tn}         レコード型
簡約:
                               ti ==> ti'
  -------------------------------------------------------------------- (ST_Rcd) 
  {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...} 
 
                                 t1 ==> t1' 
                               --------------                        (ST_Proj1) 
                               t1.i ==> t1'.i 
 
                          -------------------------                (ST_ProjRcd) 
                          {..., i=vi, ...}.i ==> vi 
型付け:
               Gamma |- t1 : T1     ...     Gamma |- tn : Tn 
             --------------------------------------------------         (T_Rcd) 
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn} 
 
                       Gamma |- t : {..., i:Ti, ...} 
                       -----------------------------                   (T_Proj) 
                             Gamma |- t.i : Ti 
*)

Module STLCExtendedRecords.

Module FirstTry.
Definition alist (X : Type) := list (string * X).

Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | TRcd : (alist ty) -> ty.
(*tyの情報がないので失敗する*)

(* Check ty_ind. 
   ====> 
    ty_ind : 
      forall P : ty -> Prop, 
        (forall i : id, P (Base i)) -> 
        (forall t : ty, P t -> forall t0 : ty, P t0  
                            -> P (Arrow t t0)) -> 
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *) 
        forall t : ty, P t 
*) 

End FirstTry.

(*
 Coq 標準のlist型の代わりに、型の構文にリストのコンストラクタ（"nil"と"cons"）を本質的に含めてしまうという方法
 *)
Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | RNil : ty
  | RCons : string -> ty -> ty -> ty.


Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  
  | rproj : tm -> string -> tm
  | trnil : tm
  | rcons : string -> tm -> tm -> tm.


Open Scope string_scope.

Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := (Base "A").
Notation B := (Base "B").
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

(*以下の型を可能にしてしまう*)
Definition weird_type := RCons X A B.
(*「後部」は実際にはレコード型ではない*)


(*型チェックを入れる*)
(*record_tyが再帰になってない＝一番外側のものだけを判定する*)
Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty RNil
  | RTcons : forall i T1 T2,
        record_ty (RCons i T1 T2).

Inductive well_formed_ty : ty -> Prop :=
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

Hint Constructors record_ty well_formed_ty.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (rcons i t1 t2).

Hint Constructors record_tm.



(*置換*)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var y => if eqb_string x y then s else t
  | abs y T t1 => abs y T
                     (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | rproj t1 i => rproj (subst x s t1) i
  | trnil => trnil
  | rcons i t1 tr1 => rcons i (subst x s t1) (subst x s tr1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(*簡約*)
(*レコードがvalueになるのはフィールドがすべてvalueの時*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (rcons i v1 vr).

(*レコードから取り出す関数*)
Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | rcons i' t tr' => if eqb_string i i' then Some t else tlookup i tr'
  | _ => None
  end.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        (rproj t1 i) --> (rproj t1' i)
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

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.


(*型付け*)
Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | RCons i' T Tr' =>
      if eqb_string i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2
  
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (rproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in RNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (rcons i t tr) \in (RCons i T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


(*練習問題*)
Lemma typing_example_2 :
  empty |-
    (app (abs a (RCons i1 (Arrow A A)
                      (RCons i2 (Arrow B B)
                       RNil))
              (rproj (var a) i2))
            (rcons i1 (abs a A (var a))
            (rcons i2 (abs a B (var a))
             trnil))) \in
    (Arrow B B).
Proof.
  eapply T_App. eapply T_Abs. apply wfRCons. apply wfArrow; apply wfBase.
  apply wfRCons. apply wfArrow; apply wfBase. apply wfRNil. apply RTnil.
  apply RTcons.
  
  eapply T_Proj. apply T_Var. constructor.
  apply wfRCons. apply wfArrow; apply wfBase.
  apply wfRCons. apply wfArrow; apply wfBase.
  apply wfRNil. apply RTnil.
  apply RTcons.
  reflexivity.

  eapply T_RCons.
  apply T_Abs. apply wfBase.
  apply T_Var. reflexivity. apply wfBase.
  apply T_RCons. apply T_Abs. apply wfBase. apply T_Var. reflexivity. apply wfBase.
  apply T_RNil. apply RTnil. constructor.
  apply RTcons. constructor.
Qed.

Example typing_nonexample :
  ~ exists T,
      (update empty a (RCons i2 (Arrow A A)
                                RNil)) |-
               (rcons i1 (abs a B (var a)) (var a)) \in
               T.
Proof.
  intro H. inversion H. inversion H0; subst. inversion H9.
Qed.



(*型付けの性質*)
(*進行と保存の証明は本質的に同じ、補題が必要になる*)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  -
    inversion H. subst. unfold Tlookup in H0.
    destruct (eqb_string i s)...
    inversion H0. subst... Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  induction Htyp...
  -
    inversion IHHtyp1...
  -
    eapply wf_rcd_lookup...
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  induction Htyp; subst; try solve_by_invert...
  -
    simpl in Hget. simpl. destruct (eqb_string i i0).
    +
      simpl. inversion Hget. subst.
      exists t...
    +
      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  -
    
    
    inversion H.
  -
    
    
    left... constructor.
  -
    
    
    right.
    destruct IHHt1; subst...
    +
      destruct IHHt2; subst...
      *
      
      
        inversion H; subst; try solve_by_invert.
        exists ([x:=t2]t12)...
      *
        
        
        destruct H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      
      
      destruct H as [t1' Hstp]. exists (app t1' t2)...
  -
    
    
    right. destruct IHHt...
    +
      
      
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H)
        as [ti [Hlkup _]].
      exists ti...
    +
      
      
      destruct H0 as [t' Hstp]. exists (rproj t' i)...
  -
    
    
    left... constructor.
  -
    
    
    destruct IHHt1...
    +
      destruct IHHt2; try reflexivity.
      *
      
      
        left... constructor...
      *
        
        
        right. destruct H2 as [tr' Hstp].
        exists (rcons i t tr')...
    +
      
      
      right. destruct H1 as [t' Hstp].
      exists (rcons i t' tr)... Qed.


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
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (rproj t i)
  | afi_rhead : forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (rcons i ti tr)
  | afi_rtail : forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (rcons i ti tr).

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
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update. destruct (eqb_stringP x y)...
  -
    apply T_App with T1...
  -
    apply T_RCons... Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  -
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.


(*保存*)


Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (update Gamma x U) |- t \in S ->
     empty |- v \in U ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  induction t;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  -
    simpl. rename s into y.
    unfold update, t_update in H0.
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    +
    
    
      subst.
      inversion H0; subst. clear H0.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
      inversion HT'.
    +
    
    
      apply T_Var...
  -
    rename s into y. rename t into T11.
    apply T_Abs...
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
      subst. rewrite false_eqb_string...
  -
    apply T_RCons... inversion H7; subst; simpl...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T ->
     t --> t' ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  -
    
    
    inversion HE; subst...
    +
      
      
      apply substitution_preserves_typing with T1...
      inversion HT1...
  -
    
    
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp]].
    rewrite H4 in Hget. inversion Hget. subst...
  -
    
    
    apply T_RCons... eapply step_preserves_record_tm...
Qed.

End STLCExtendedRecords.

