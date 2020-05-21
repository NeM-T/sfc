Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
Require Import maps.
Require Import smallstep.
Require Import stlc.
Require morestlc.

Module STLCTypes.
Export STLC.

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | Bool, Bool =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity. Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  -
    reflexivity.
  -
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst... Qed.
End STLCTypes.

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      Gamma x
  | abs x T11 t12 =>
      match type_check (update Gamma x T11) t12 with
      | Some T12 => Some (Arrow T11 T12)
      | _ => None
      end
  | app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some (Arrow T11 T12),Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | tru =>
      Some Bool
  | fls =>
      Some Bool
  | test guard t f =>
      match type_check Gamma guard with
      | Some Bool =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.


(*モナディック記法*)
Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 ;;
      return (Arrow T11 T12)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tru =>
      return Bool
  | fls =>
      return Bool
  | test guard t1 t2 =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | Bool =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  -
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  -
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - eauto.
  - eauto.
  -
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - destruct (Gamma x0) eqn:H0; assumption.
  - rewrite IHHty...
  -
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T11)...
  - eauto.
  - eauto.
  - rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T)...
Qed.

End STLCChecker.



(*演習問題*)
Module TypecheckerExtensions.
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import morestlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | Nat, Nat =>
      true
  | Unit, Unit =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Prod T11 T12, Prod T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Sum T11 T12, Sum T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | List T11, List T21 =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1.
  induction T1; simpl;
    try reflexivity;
    try (rewrite IHT1_1; rewrite IHT1_2; reflexivity);
    try (rewrite IHT1; reflexivity). Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  (*pure*)
  | var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | abs x1 T1 t2 =>
      T2 <- type_check (update Gamma x1 T1) t2 ;;
      return (Arrow T1 T2)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  (*Nat*)
  | const _ =>
      return Nat
  | scc t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | Nat => return Nat
      | _ => fail
      end
  | prd t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | Nat => return Nat
      | _ => fail
      end
  | mlt t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | Nat, Nat => return Nat
      | _,_ => fail
      end
  | test0 guard t f =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | Nat => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  | tinl T2 t1 =>
    T1 <- type_check Gamma t1;;
    return Sum T1 T2
  | tinr T1 t2 =>
    T2 <- type_check Gamma t2;;
    return Sum T1 T2
  | tcase t0 x1 t1 x2 t2 =>
    T <- type_check Gamma t0;;
    match T with
    | Sum T1 T2 =>
      T <- type_check (x1 |-> T1; Gamma) t1;;
      T0 <- type_check (x2 |-> T2; Gamma) t2;;
      if eqb_ty T T0 then return T else fail
    | _ => fail
    end

  | tnil T =>
      return List T
  | tcons t1 t2 =>
    T1 <- type_check Gamma t1;;
    T2 <- type_check Gamma t2;;
    match T2 with
    | List T3 => if eqb_ty T1 T3 then return List T1 else fail
    | _ => fail
    end
  | tlcase t0 t1 x21 x22 t2 =>
      match type_check Gamma t0 with
      | Some (List T) =>
          match type_check Gamma t1,
                type_check (update (update Gamma x22 (List T)) x21 T) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then Some T1' else None
          | _,_ => None
          end
      | _ => None
      end
  | unit => return Unit
  | pair t1 t2 =>
    T1 <- type_check Gamma t1;;
    T2 <- type_check Gamma t2;;
    return Prod T1 T2
  | fst t =>
    T <- type_check Gamma t ;;
    match T with
    | Prod T1 T2 => return T1
    | _ => fail
    end
  | snd t =>
    T <- type_check Gamma t;;
    match T with
    | Prod T1 T2 => return T2
    | _ => fail
    end
  | tlet x t1 t2 =>
    T1 <- type_check Gamma t1;;
    T2 <- type_check (x |-> T1; Gamma) t2;;
    return T2
  | tfix t =>
    T <- type_check Gamma t ;;
    match T with
    | (Arrow T1 T2) => if eqb_ty T1 T2 then return T1 else fail
    | _ => fail
    end
  end.


Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  -
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  -
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - eauto.
  -
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  -
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  -
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  -
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  -
    invert_typecheck Gamma t0 T1.
  -
    invert_typecheck Gamma t0 T2.
  -
    fully_invert_typecheck Gamma t1 T T1 T2.
    symmetry in HeqTO. apply IHt1 in HeqTO.

    econstructor. eassumption.
    invert_typecheck (s |-> T1; Gamma) t2 T3.
    symmetry in HeqTO0. apply IHt2 in HeqTO0.
    invert_typecheck (s0 |-> T2; Gamma) t3 T0.

    destruct (eqb_ty T3 T0) eqn: IH.
    apply eqb_ty__eq in IH. inversion H0. subst. assumption.
    inversion H0.

    invert_typecheck (s |-> T1; Gamma) t2 T3.
    invert_typecheck (s0 |-> T2; Gamma) t3 T0.
    symmetry in HeqTO1. apply IHt3 in HeqTO1.

    destruct (eqb_ty T3 T0) eqn: IH.
    apply eqb_ty__eq in IH. inversion H0. subst. assumption.
    inversion H0.
  -
    auto.
  -
    invert_typecheck Gamma t1 T1.
    symmetry in HeqTO; apply IHt1 in HeqTO.
    fully_invert_typecheck Gamma t2 T1 T0 T2.
    symmetry in HeqTO0. apply IHt2 in HeqTO0.
    destruct (eqb_ty T1 T0) eqn: IH.
    apply eqb_ty__eq in IH; inversion H0; subst.
    econstructor...
    inversion H0.
  -
    rename s into x31. rename s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (update (update Gamma x32 (List T11)) x31 T11) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  -
    auto.
  -
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  -
    fully_invert_typecheck Gamma t T T1 T2.
  -
    fully_invert_typecheck Gamma t T T1 T2.
  -
    invert_typecheck Gamma t1 T1.
    invert_typecheck (s |-> T1; Gamma) t2 T2.
  -
    fully_invert_typecheck Gamma t T T1 T2.
    symmetry in HeqTO. apply IHt in HeqTO.
    constructor.
    destruct (eqb_ty T1 T2) eqn: IH. apply eqb_ty__eq in IH. inversion H0. subst. assumption.
    inversion H1.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    eauto.
  - destruct (Gamma x); try solve_by_invert. eauto.
Qed.


End TypecheckerExtensions.


Module StepFunction.
Import morestlc.
Import STLCExtended.

(* Fixpoint stepf (t : tm) : option tm := *)
  (* match t with *)
  (* end *)
  (* . Admitted. *)


(* Theorem sound_stepf : forall t t', *)
(*     stepf t = Some t' -> t --> t'. *)
(* Proof. Admitted. *)

(* Theorem complete_stepf : forall t t', *)
(*     t --> t' -> stepf t = Some t'. *)
(* Proof. Admitted. *)

End StepFunction.


Module StlcImpl.

From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Import ListNotations.

(*-----------字句解析-----------*)
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)
           (n =? 9))
      (orb (n =? 10)
           (n =? 13)).
Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3 223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.


(*---------構文解析----------*)
(*エラー付きオプション*)
Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.
Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).


(*一般コンビネータ*)
Open Scope string_scope.


Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(*再帰下降パーサ*)
Import morestlc.STLCExtended.
Import TypecheckerExtensions.
Notation "[]" := nil.


(*識別子*)
Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(*数値*)
Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

(*算術式*)
(*一通り終わったらヤル。以下のものは 1st/coqpit/impparser.vのコピペ*)
(* Fixpoint parsePrimaryExp (steps:nat) *)
(*                          (xs : list token) *)
(*                        : optionE (tm * list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*       TRY ' (i, rest) <- parseIdentifier xs ;; *)
(*           SomeE (AId i, rest) *)
(*       OR *)
(*       TRY ' (n, rest) <- parseNumber xs ;; *)
(*           SomeE (ANum n, rest) *)
(*       OR *)
(*       ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;; *)
(*       ' (u, rest') <- expect ")" rest ;; *)
(*       SomeE (e,rest') *)
(*   end *)

(* with parseProductExp (steps:nat) *)
(*                      (xs : list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*     ' (e, rest) <- parsePrimaryExp steps' xs ;; *)
(*     ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps')) *)
(*                           steps' rest ;; *)
(*     SomeE (fold_left AMult es e, rest') *)
(*   end *)

(* with parseSumExp (steps:nat) (xs : list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*     ' (e, rest) <- parseProductExp steps' xs ;; *)
(*     ' (es, rest') <- *)
(*         many (fun xs => *)
(*                 TRY ' (e,rest') <- *)
(*                     firstExpect "+" *)
(*                                 (parseProductExp steps') xs ;; *)
(*                     SomeE ( (true, e), rest') *)
(*                 OR *)
(*                 ' (e, rest') <- *)
(*                     firstExpect "-" *)
(*                                 (parseProductExp steps') xs ;; *)
(*                 SomeE ( (false, e), rest')) *)
(*         steps' rest ;; *)
(*       SomeE (fold_left (fun e0 term => *)
(*                           match term with *)
(*                           | (true, e) => APlus e0 e *)
(*                           | (false, e) => AMinus e0 e *)
(*                           end) *)
(*                        es e, *)
(*              rest') *)
(*   end. *)

(* Definition parseAExp := parseSumExp. *)


(* (*ブール式*) *)
(* Fixpoint parseAtomicExp (steps:nat) *)
(*                         (xs : list token) := *)
(* match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*      TRY ' (u,rest) <- expect "true" xs ;; *)
(*          SomeE (BTrue,rest) *)
(*      OR *)
(*      TRY ' (u,rest) <- expect "false" xs ;; *)
(*          SomeE (BFalse,rest) *)
(*      OR *)
(*      TRY ' (e,rest) <- firstExpect "~" *)
(*                                    (parseAtomicExp steps') *)
(*                                    xs ;; *)
(*          SomeE (BNot e, rest) *)
(*      OR *)
(*      TRY ' (e,rest) <- firstExpect "(" *)
(*                                    (parseConjunctionExp steps') *)
(*                                    xs ;; *)
(*          ' (u,rest') <- expect ")" rest ;; *)
(*          SomeE (e, rest') *)
(*      OR *)
(*      ' (e, rest) <- parseProductExp steps' xs ;; *)
(*      TRY ' (e', rest') <- firstExpect "=" *)
(*                                   (parseAExp steps') rest ;; *)
(*          SomeE (BEq e e', rest') *)
(*      OR *)
(*      TRY ' (e', rest') <- firstExpect "<=" *)
(*                                       (parseAExp steps') rest ;; *)
(*          SomeE (BLe e e', rest') *)
(*      OR *)
(*      NoneE "Expected '=' or '<=' after arithmetic expression" *)
(* end *)

(* with parseConjunctionExp (steps:nat) *)
(*                          (xs : list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*     ' (e, rest) <- parseAtomicExp steps' xs ;; *)
(*     ' (es, rest') <- many (firstExpect "&&" *)
(*                (parseAtomicExp steps')) *)
(*             steps' rest ;; *)
(*     SomeE (fold_left BAnd es e, rest') *)
(*   end. *)

(* Definition parseBExp := parseConjunctionExp. *)

(* Check parseConjunctionExp. *)

(* Definition testParsing {X : Type} *)
(*            (p : nat -> *)
(*                 list token -> *)
(*                 optionE (X * list token)) *)
(*            (s : string) := *)
(*   let t := tokenize s in *)
(*   p 100 t. *)


(* (*コマンド*) *)
(* Fixpoint parseSimpleCommand (steps:nat) *)
(*                             (xs : list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*     TRY ' (u, rest) <- expect "SKIP" xs ;; *)
(*         SomeE (SKIP%imp, rest) *)
(*     OR *)
(*     TRY ' (e,rest) <- *)
(*             firstExpect "TEST" *)
(*                         (parseBExp steps') xs ;; *)
(*         ' (c,rest') <- *)
(*             firstExpect "THEN" *)
(*                         (parseSequencedCommand steps') rest ;; *)
(*         ' (c',rest'') <- *)
(*             firstExpect "ELSE" *)
(*                         (parseSequencedCommand steps') rest' ;; *)
(*         ' (tt,rest''') <- *)
(*             expect "END" rest'' ;; *)
(*        SomeE(TEST e THEN c ELSE c' FI%imp, rest''') *)
(*     OR *)
(*     TRY ' (e,rest) <- *)
(*             firstExpect "WHILE" *)
(*                         (parseBExp steps') xs ;; *)
(*         ' (c,rest') <- *)
(*             firstExpect "DO" *)
(*                         (parseSequencedCommand steps') rest ;; *)
(*         ' (u,rest'') <- *)
(*             expect "END" rest' ;; *)
(*         SomeE(WHILE e DO c END%imp, rest'') *)
(*     OR *)
(*     TRY ' (i, rest) <- parseIdentifier xs ;; *)
(*         ' (e, rest') <- firstExpect "::=" (parseAExp steps') rest ;; *)
(*         SomeE ((i ::= e)%imp, rest') *)
(*     OR *)
(*         NoneE "Expecting a command" *)
(* end *)

(* with parseSequencedCommand (steps:nat) *)
(*                            (xs : list token) := *)
(*   match steps with *)
(*   | 0 => NoneE "Too many recursive calls" *)
(*   | S steps' => *)
(*     ' (c, rest) <- parseSimpleCommand steps' xs ;; *)
(*     TRY ' (c', rest') <- *)
(*             firstExpect ";;" *)
(*                         (parseSequencedCommand steps') rest ;; *)
(*         SomeE ((c ;; c')%imp, rest') *)
(*     OR *)
(*     SomeE (c, rest) *)
(*   end. *)

(* Definition bignumber := 1000. *)

(* Definition parse (str : string) : optionE com := *)
(*   let tokens := tokenize str in *)
(*   match parseSequencedCommand bignumber tokens with *)
(*   | SomeE (c, []) => SomeE c *)
(*   | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t) *)
(*   | NoneE err => NoneE err *)
(*   end. *)


End StlcImpl.
