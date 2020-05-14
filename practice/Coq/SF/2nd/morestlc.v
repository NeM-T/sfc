Set Warnings "-notation-overridden,-parsing".
Require Import maps.
Require Import types.
Require Import smallstep.
Require Import stlc.
From Coq Require Import Strings.String.

Module STLCExtended.

(*letの導入*)
(*
構文:
       t ::=                項
           | ...               （前と同じ他の項）
           | let x=t in t      let束縛

簡約:
                                 t1 --> t1' 
                     ----------------------------------               (ST_Let1) 
                     let x=t1 in t2 --> let x=t1' in t2 
 
                        ----------------------------              (ST_LetValue) 
                        let x=v1 in t2 --> [x:=v1]t2 
型付け:
             Gamma |- t1 \in T1      x|->T1; Gamma |- t2 \in T2 
             --------------------------------------------------        (T_Let) 
                        Gamma |- let x=t1 in t2 \in T2 
 *)

(*
対 射影 直積
*)

(*
構文:
       t ::=                項
           | ... 
           | (t,t)             対
           | t.fst             第1射影
           | t.snd             第2射影
 
       v ::=                値
           | ... 
           | (v,v)             対値
 
       T ::=                型
           | ... 
           | T * T             直積型


簡約：
                              t1 --> t1' 
                         --------------------                        (ST_Pair1) 
                         (t1,t2) --> (t1',t2) 
 
                              t2 --> t2' 
                         --------------------                        (ST_Pair2) 
                         (v1,t2) --> (v1,t2') 
 
                              t1 --> t1' 
                          ------------------                          (ST_Fst1) 
                          t1.fst --> t1'.fst 
 
                          ------------------                       (ST_FstPair) 
                          (v1,v2).fst --> v1 
 
                              t1 --> t1' 
                          ------------------                          (ST_Snd1) 
                          t1.snd --> t1'.snd 

                           ------------------                       (ST_SndPair) 
                          (v1,v2).snd --> v2 


型付け：
               Gamma |- t1 \in T1     Gamma |- t2 \in T2 
               -----------------------------------------               (T_Pair) 
                       Gamma |- (t1,t2) \in T1*T2 
 
                        Gamma |- t \in T1*T2 
                        ---------------------                          (T_Fst) 
                        Gamma |- t.fst \in T1 
 
                        Gamma |- t \in T1*T2 
                        ---------------------                          (T_Snd) 
                        Gamma |- t.snd \in T2 

 *)

(*1要素の型Unit*)
(*
構文:
       t ::=                項
           | ...               （前と同様）
           | unit              unit値
 
       v ::=                値
           | ... 
           | unit              unit 
 
       T ::=                型
           | ... 
           | Unit              Unit型
型付け:
                         ----------------------                        (T_Unit) 
                         Gamma |- unit \in Unit 

 *)
(*
 Unitが本当に便利なのはよりリッチな言語で副作用(side effects)を持つ場合です。 例えば、変更可能な変数やポインタについての代入文や、例外その他のローカルではないコントロール機構を持つ場合、などです。 そのような言語では、副作用のためだけに評価される式の(どうでもよい)結果のための型が便利なのです。
 *)

(*直和型*)
(*
構文:
       t ::=                項
           | ...               （前と同様）
           | inl T t           タグ付け（左）
           | inr T t           タグ付け（右）
           | case t of         case 
               inl x => t 
             | inr x => t 
 
       v ::=                値
           | ... 
           | inl T v           タグ付き値（左）
           | inr T v           タグ付き値（右）
 
       T ::=                型
           | ... 
           | T + T             直和型

簡約:
                               t1 --> t1' 
                        ------------------------                       (ST_Inl) 
                        inl T2 t1 --> inl T2 t1' 
 
                               t2 --> t2' 
                        ------------------------                       (ST_Inr) 
                        inr T1 t2 --> inr T1 t2' 
 
                               t0 --> t0' 
               -------------------------------------------            (ST_Case) 
                case t0 of inl x1 => t1 | inr x2 => t2 --> 
               case t0' of inl x1 => t1 | inr x2 => t2 
 
            -----------------------------------------------        (ST_CaseInl) 
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2 
                           -->  [x1:=v1]t1 
 
            -----------------------------------------------        (ST_CaseInr) 
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2 
                           -->  [x2:=v1]t2 

型付け:
                          Gamma |- t1 \in T1 
                   ------------------------------                       (T_Inl) 
                   Gamma |- inl T2 t1 \in T1 + T2 
 
                          Gamma |- t2 \in T2 
                   -------------------------------                      (T_Inr) 
                    Gamma |- inr T1 t2 \in T1 + T2 
 
                        Gamma |- t \in T1+T2 
                     x1|->T1; Gamma |- t1 \in T 
                     x2|->T2; Gamma |- t2 \in T 
         ----------------------------------------------------          (T_Case) 
         Gamma |- case t of inl x1 => t1 | inr x2 => t2 \in T 

inlとinrに型を付記する理由は、関数に対して行ったのと同様、型付け規則を単純にするためです。
*)

(*リスト*)
(*
構文:
       t ::=                項
           | ... 
           | nil T 
           | cons t t 
           | lcase t of nil  => t 
                      | x::x => t 
 
       v ::=                値
           | ... 
           | nil T             nil値
           | cons v v          cons値
 
       T ::=                型
           | ... 
           | List T            Tのリスト

簡約:
                                t1 --> t1' 
                       --------------------------                    (ST_Cons1) 
                       cons t1 t2 --> cons t1' t2 
 
                                t2 --> t2' 
                       --------------------------                    (ST_Cons2) 
                       cons v1 t2 --> cons v1 t2' 
 
                              t1 --> t1' 
                -------------------------------------------         (ST_Lcase1) 
                 (lcase t1 of nil => t2 | xh::xt => t3) --> 
                (lcase t1' of nil => t2 | xh::xt => t3) 
 
               -----------------------------------------          (ST_LcaseNil) 
               (lcase nil T of nil => t2 | xh::xt => t3) 
                                --> t2 
 
            ------------------------------------------------     (ST_LcaseCons) 
            (lcase (cons vh vt) of nil => t2 | xh::xt => t3) 
                          --> [xh:=vh,xt:=vt]t3 

型付け:
                        -------------------------                       (T_Nil) 
                        Gamma |- nil T \in List T 
 
             Gamma |- t1 \in T      Gamma |- t2 \in List T 
             ---------------------------------------------             (T_Cons) 
                    Gamma |- cons t1 t2 \in List T 
 
                        Gamma |- t1 \in List T1 
                        Gamma |- t2 \in T 
                (h|->T1; t|->List T1; Gamma) |- t3 \in T 
          ---------------------------------------------------         (T_Lcase) 
          Gamma |- (lcase t1 of nil => t2 | h::t => t3) \in T 

*)

(*一般再帰*)
(*
      fact = \x:Nat. 
                test x=0 then 1 else x * (fact (pred x))) 
のように書く代わりに、次のように書きます。
      fact = 
          fix 
            (\f:Nat->Nat. 
               \x:Nat. 
                  test x=0 then 1 else x * (f (pred x))) 
*)

(*
構文:
       t ::=                項
           | ... 
           | fix t             不動点演算子
簡約:
                                t1 --> t1' 
                            ------------------                        (ST_Fix1) 
                            fix t1 --> fix t1' 
 
               --------------------------------------------         (ST_FixAbs) 
               fix (\xf:T1.t2) --> [xf:=fix (\xf:T1.t2)] t2 
型付け:
                           Gamma |- t1 \in T1->T1 
                           ----------------------                       (T_Fix) 
                           Gamma |- fix t1 \in T1 
*)

(*レコード*)
(*
構文:
       t ::=                          項
           | ... 
           | {i1=t1, ..., in=tn}         レコード
           | t.i                         射影
 
       v ::=                          値
           | ... 
           | {i1=v1, ..., in=vn}         レコード値
 
       T ::=                          型
           | ... 
           | {i1:T1, ..., in:Tn}         レコード型

簡約:
                              ti --> ti' 
                 ------------------------------------                  (ST_Rcd) 
                     {i1=v1, ..., im=vm, in=ti , ...} 
                 --> {i1=v1, ..., im=vm, in=ti', ...} 
 
                              t1 --> t1' 
                            --------------                           (ST_Proj1) 
                            t1.i --> t1'.i 
 
                      -------------------------                    (ST_ProjRcd) 
                      {..., i=vi, ...}.i --> vi 

型付け；
            Gamma |- t1 \in T1     ...     Gamma |- tn \in Tn 
          ----------------------------------------------------          (T_Rcd) 
          Gamma |- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn} 
 
                    Gamma |- t \in {..., i:Ti, ...} 
                    -------------------------------                    (T_Proj) 
                          Gamma |- t.i \in Ti 

*)


(*構文*)
Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty
  | Sum : ty -> ty -> ty (*直和*)
  | List : ty -> ty
  | Unit : ty
  | Prod : ty -> ty -> ty (*直積*) .

Inductive tm : Type :=
  (*puree*)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (*数値*)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm
  (*直和*)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> string -> tm -> string -> tm -> tm
  (*リスト*)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
  (*Unit*)
  | unit : tm
  (*直積*)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
  (*let*)
  | tlet : string -> tm -> tm -> tm
  (*fix*)
  | tfix : tm -> tm.


(*置換*)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with

  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)

  | const n =>
      const n
  | scc t1 =>
      scc (subst x s t1)
  | prd t1 =>
      prd (subst x s t1)
  | mlt t1 t2 =>
      mlt (subst x s t1) (subst x s t2)
  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)

  | tinl T t1 =>
      tinl T (subst x s t1)
  | tinr T t1 =>
      tinr T (subst x s t1)
  | tcase t0 y1 t1 y2 t2 =>
      tcase (subst x s t0)
         y1 (if eqb_string x y1 then t1 else (subst x s t1))
         y2 (if eqb_string x y2 then t2 else (subst x s t2))

  | tnil T =>
      tnil T
  | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
      tlcase (subst x s t1) (subst x s t2) y1 y2
        (if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else (subst x s t3))

  | unit => unit


  | _ => t
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(*簡約*)

Inductive value : tm -> Prop :=
  (*pure*)
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)
  (*数値*)
  | v_nat : forall n1,
      value (const n1)
  (*直和*)
  | v_inl : forall v T,
      value v ->
      value (tinl T v)
  | v_inr : forall v T,
      value v ->
      value (tinr T v)
  (*リスト*)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl)
  (*unit*)
  | v_unit : value unit
  (*直積*)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (pair v1 v2).

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (*pure*)
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')
  (*数値*)
  | ST_Succ1 : forall t1 t1',
       t1 --> t1' ->
       (scc t1) --> (scc t1')
  | ST_SuccNat : forall n1,
       (scc (const n1)) --> (const (S n1))
  | ST_Pred : forall t1 t1',
       t1 --> t1' ->
       (prd t1) --> (prd t1')
  | ST_PredNat : forall n1,
       (prd (const n1)) --> (const (pred n1))
  | ST_Mult1 : forall t1 t1' t2,
       t1 --> t1' ->
       (mlt t1 t2) --> (mlt t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (mlt v1 t2) --> (mlt v1 t2')
  | ST_Mulconsts : forall n1 n2,
       (mlt (const n1) (const n2)) --> (const (mult n1 n2))
  | ST_Test01 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       (test0 t1 t2 t3) --> (test0 t1' t2 t3)
  | ST_Test0Zero : forall t2 t3,
       (test0 (const 0) t2 t3) --> t2
  | ST_Test0Nonzero : forall n t2 t3,
       (test0 (const (S n)) t2 t3) --> t3
  (*直和*)
  | ST_Inl : forall t1 t1' T,
        t1 --> t1' ->
        (tinl T t1) --> (tinl T t1')
  | ST_Inr : forall t1 t1' T,
        t1 --> t1' ->
        (tinr T t1) --> (tinr T t1')
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        (tcase t0 x1 t1 x2 t2) --> (tcase t0' x1 t1 x2 t2)
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinl T v0) x1 t1 x2 t2) --> [x1:=v0]t1
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinr T v0) x1 t1 x2 t2) --> [x2:=v0]t2
  (*リスト*)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (tcons t1 t2) --> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (tcons v1 t2) --> (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       (tlcase t1 t2 x1 x2 t3) --> (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
       (tlcase (tnil T) t2 x1 x2 t3) --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       (tlcase (tcons v1 vl) t2 x1 x2 t3)
         --> (subst x2 vl (subst x1 v1 t3))
  (*UnitはStepない*)
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
  (*let*)
  | ST_Let1 : forall x t1 t1' t2,
      t1 --> t1' ->
      tlet x t1 t2 --> tlet x t1' t2
  | ST_LetValue : forall x v1 t2,
      value v1 ->
      tlet x v1 t2 --> [x:= v1]t2
  (*fix*)
  | ST_Fix1 : forall t1 t1',
      t1 --> t1' ->
      tfix t1 --> tfix t1'
  | ST_FixAbs : forall x T t,
      tfix (abs x T t) --> [x:= tfix (abs x T t)]t
where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Definition context := partial_map ty.


Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (*pure*)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2
  (*数値*)
  | T_Nat : forall Gamma n1,
      Gamma |- (const n1) \in Nat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (scc t1) \in Nat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (prd t1) \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- (mlt t1 t2) \in Nat
  | T_Test0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (test0 t1 t2 t3) \in T1
  (*直和*)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (tinl T2 t1) \in (Sum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (tinr T1 t2) \in (Sum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |- t0 \in (Sum T1 T2) ->
      (update Gamma x1 T1) |- t1 \in T ->
      (update Gamma x2 T2) |- t2 \in T ->
      Gamma |- (tcase t0 x1 t1 x2 t2) \in T
  (*リスト*)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (List T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (tcons t1 t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (List T1) ->
      Gamma |- t2 \in T2 ->
      (update (update Gamma x2 (List T1)) x1 T1) |- t3 \in T2 ->
      Gamma |- (tlcase t1 t2 x1 x2 t3) \in T2
  (*Unit*)
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
  (*let*)
  | T_Let : forall Gemma x t1 t2 T1 T2,
      Gemma |- t1 \in T1 ->
      (update Gemma x T1) |- t2 \in T2 ->
      Gemma |- (tlet x t1 t2) \in T2
(*fix*)
  | T_Fix : forall Gemma t1 T1,
      Gemma |- t1 \in (Arrow T1 T1) ->
      Gemma |- (tfix t1) \in T1
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Definition manual_grade_for_extensions_definition : option (nat*string) := None.



Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

Module Numtest.

Definition test :=
  test0
    (prd
      (scc
        (prd
          (mlt
            (const 2)
            (const 0)))))
    (const 5)
    (const 6).

Example typechecks :
  empty |- test \in Nat.
Proof.
  unfold test.
  auto 10.
Qed.

Example numtest_reduces :
  test -->* const 5.
Proof.
  unfold test. eauto 20. Qed.
  (* econstructor. constructor. constructor. constructor. constructor. apply ST_Mulconsts. *)
  (* econstructor. constructor. constructor. constructor. apply ST_PredNat. *)
  (* econstructor. constructor. constructor. apply ST_SuccNat. *)
  (* econstructor. constructor. apply ST_PredNat. *)
  (* econstructor. apply ST_Test0Zero. *)
  (* constructor. *)
(* Qed. *)

End Numtest.

Module Prodtest.

Definition test :=
  snd
    (fst
      (pair
        (pair
          (const 5)
          (const 6))
        (const 7))).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test -->* const 6.
Proof.
  unfold test.
  econstructor. constructor. apply ST_FstPair; constructor; constructor; constructor.
  econstructor. apply ST_SndPair; constructor; constructor.
  constructor.
Qed.

End Prodtest.


Module LetTest.

Definition test :=
  tlet
    x
    (prd (const 6))
    (scc (var x)).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test -->* const 6.
Proof.
  unfold test. 
  econstructor. constructor. apply ST_PredNat.
  econstructor. apply ST_LetValue. constructor.
  econstructor. unfold subst. rewrite <- eqb_string_refl. simpl. apply ST_SuccNat.
  constructor.
Qed.

End LetTest.


Module Sumtest1.

Definition test :=
  tcase (tinl Nat (const 5))
    x (var x)
    y (var y).

Example typechecks :
  empty |- test \in Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test -->* (const 5).
Proof.
  unfold test.
  econstructor. apply ST_CaseInl. constructor.
  constructor.
Qed.

End Sumtest1.

Module Sumtest2.

Definition test :=
  tlet
    processSum
    (abs x (Sum Nat Nat)
      (tcase (var x)
         n (var n)
         n (test0 (var n) (const 1) (const 0))))
    (pair
      (app (var processSum) (tinl Nat (const 5)))
      (app (var processSum) (tinr Nat (const 5)))).

Example typechecks :
  empty |- test \in (Prod Nat Nat).
Proof.
  unfold test.
  econstructor. constructor. econstructor; constructor. constructor. constructor. constructor. constructor. constructor. constructor.
  econstructor. econstructor; constructor. constructor. constructor. econstructor. constructor. constructor.
  constructor. constructor.
Qed.

Example reduces :
  test -->* (pair (const 5) (const 0)).
Proof.
  unfold test.
  econstructor. apply ST_LetValue. constructor.
  econstructor. Abort.

End Sumtest2.


Module ListTest.

Definition test :=
  tlet l
    (tcons (const 5) (tcons (const 6) (tnil Nat)))
    (tlcase (var l)
       (const 0)
       x y (mlt (var x) (var x))).

Example typechecks :
  empty |- test \in Nat.
Proof.
  unfold test.
  econstructor. constructor. constructor. constructor. constructor. constructor.
  econstructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor.
Qed.

Example reduces :
  test -->* (const 25).
Proof.
  unfold test.
  econstructor. apply ST_LetValue. constructor. constructor. constructor. constructor. constructor.
  econstructor. simpl. apply ST_LcaseCons. constructor. constructor. constructor. constructor.
  econstructor. simpl. apply ST_Mulconsts.
  constructor.
Qed.

End ListTest.

Module FixTest1.

Definition fact :=
  tfix
    (abs f (Arrow Nat Nat)
      (abs a Nat
        (test0
           (var a)
           (const 1)
           (mlt
              (var a)
              (app (var f) (prd (var a))))))).

Example typechecks :
  empty |- fact \in (Arrow Nat Nat).
Proof.
  unfold fact.
  econstructor. constructor. constructor. constructor.
  constructor. constructor.
  constructor.
  constructor.
  constructor. constructor.
  econstructor. constructor. constructor. constructor. constructor. constructor.
Qed.

Example reduces :
  (app fact (const 4)) -->* (const 24).
Proof.
  unfold fact. normalize. 
  (* econstructor. constructor. apply ST_FixAbs. *)
  (* simpl. econstructor. constructor. constructor. *)
  (* econstructor. unfold subst. simpl. apply ST_Test0Nonzero. *)
  (* econstructor. apply ST_Mult2. constructor. constructor. apply ST_FixAbs. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_App2. constructor. apply ST_PredNat. *)
  (* econstructor. apply ST_Mult2. constructor. apply ST_AppAbs. constructor. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Test0Nonzero. *)
  (* econstructor. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_App1. apply ST_FixAbs. *)
  (* econstructor. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_App2. constructor. apply ST_PredNat. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_AppAbs. constructor. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_Test0Nonzero. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_App1. apply ST_FixAbs. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_App2. constructor. apply ST_PredNat. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_AppAbs. constructor. *)
  (* econstructor. apply ST_Mult2. constructor. simpl. apply ST_Mult2. constructor. apply ST_Mult2. constructor. apply ST_Test0Nonzero. *)
  (*以下略*)
Qed.

End FixTest1.


Module FixTest2.

Definition map :=
  abs g (Arrow Nat Nat)
    (tfix
      (abs f (Arrow (List Nat) (List Nat))
        (abs l (List Nat)
          (tlcase (var l)
            (tnil Nat)
            a l (tcons (app (var g) (var a))
                         (app (var f) (var l))))))).

Example typechecks :
  empty |- map \in
    (Arrow (Arrow Nat Nat)
      (Arrow (List Nat)
        (List Nat))).
Proof.
  unfold map. 
  econstructor. constructor. constructor. constructor.
  econstructor. constructor. constructor. constructor. constructor.
  econstructor. constructor. constructor. constructor. constructor.
  econstructor. constructor. constructor.
  constructor. constructor.
Qed.

Example reduces :
  app (app map (abs a Nat (scc (var a))))
         (tcons (const 1) (tcons (const 2) (tnil Nat)))
  -->* (tcons (const 2) (tcons (const 3) (tnil Nat))).
Proof.
  econstructor. constructor. constructor. constructor.
  econstructor. constructor. simpl. apply ST_FixAbs.
  econstructor. simpl. constructor. constructor. constructor. constructor. constructor. constructor.
  econstructor. simpl. apply ST_LcaseCons. constructor. constructor. constructor. constructor.
  econstructor. simpl. apply ST_Cons1. constructor. Abort.

End FixTest2.

End Examples.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  -
    
    inversion H.
  -
    
    left...
  -
    
    right.
    destruct IHHt1; subst...
    +
      destruct IHHt2; subst...
      *
        
        inversion H; subst; try solve_by_invert.
        exists (subst x t2 t12)...
      *
        
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    +
      
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  -
    left...
  -
    right.
    destruct IHHt...
    +
      inversion H; subst; try solve_by_invert.
      exists (const (S n1))...
    +
      inversion H as [t1' Hstp].
      exists (scc t1')...
  -
    right.
    destruct IHHt...
    +
      inversion H; subst; try solve_by_invert.
      exists (const (pred n1))...
    +
      inversion H as [t1' Hstp].
      exists (prd t1')...
  -
    right.
    destruct IHHt1...
    +
      destruct IHHt2...
      *
        inversion H; subst; try solve_by_invert.
        inversion H0; subst; try solve_by_invert.
        exists (const (mult n1 n0))...
      *
        inversion H0 as [t2' Hstp].
        exists (mlt t1 t2')...
    +
      inversion H as [t1' Hstp].
      exists (mlt t1' t2)...
  -
    right.
    destruct IHHt1...
    +
      inversion H; subst; try solve_by_invert.
      destruct n1 as [|n1'].
      *
        exists t2...
      *
        exists t3...
    +
      inversion H as [t1' H0].
      exists (test0 t1' t2 t3)...
  -
    destruct IHHt...
    +
      right. inversion H as [t1' Hstp]...
  -
    destruct IHHt...
    +
      right. inversion H as [t1' Hstp]...
  -
    right.
    destruct IHHt1...
    +
      inversion H; subst; try solve_by_invert.
      *
        exists ([x1:=v]t1)...
      *
        exists ([x2:=v]t2)...
    +
      inversion H as [t0' Hstp].
      exists (tcase t0' x1 t1 x2 t2)...
  -
    left...
  -
    destruct IHHt1...
    +
      destruct IHHt2...
      *
        right. inversion H0 as [t2' Hstp].
        exists (tcons t1 t2')...
    +
      right. inversion H as [t1' Hstp].
      exists (tcons t1' t2)...
  -
    right.
    destruct IHHt1...
    +
      inversion H; subst; try solve_by_invert.
      *
        exists t2...
      *
        exists ([x2:=vl]([x1:=v1]t3))...
    +
      inversion H as [t1' Hstp].
      exists (tlcase t1' t2 x1 x2 t3)...
  -
    left...
  -
    destruct IHHt1... destruct IHHt2...
    inversion H0. right. exists (pair t1 x). constructor; assumption.
    inversion H. right. exists (pair x t2). constructor; assumption.
  -
    right. destruct IHHt...
    inversion H; subst; inversion Ht; subst. exists v1. constructor; assumption.
    inversion H. exists (fst x). constructor; assumption.
  -
    right. destruct IHHt...
    inversion H; subst; inversion Ht; subst. exists v2. constructor; assumption.
    inversion H. exists (snd x). constructor; assumption.
  -
    destruct IHHt1... inversion H. right. exists (tlet x x0 t2). constructor; assumption.
  -
    right. destruct IHHt...
    inversion H; subst; inversion Ht; subst. exists ([x:= tfix (abs x T1 t12)]t12). apply ST_FixAbs.
    inversion H. exists (tfix x). constructor. assumption.
Qed.

Definition manual_grade_for_progress : option (nat*string) := None.

End STLCExtended.
