Set Warnings "-notation-overridden,-parsing".
From LF Require Export indprop.


Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'. (*forall n : nat, even n -> even (4 + n)*)

Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

(*依存型の書き方に使う。
 　明示的な項でなくても定義できる。*)
Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S. (*ここで +1を指定*)
Show Proof.
apply n. Defined.
Print add1.

Compute add1 2.

Module and.
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.
End and.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Search "/\".

Definition conj_fact P Q R (H0: P /\ Q ) (H1: Q /\ R)  :=
    match H0 with
    | conj HP HQ => match H1 with
                    | conj HQ HR => conj HP HR
                    end
    end.

Module or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P ->  or P Q
| or_intror : Q ->  or P  Q.

End or.

Search "\/".

Definition or_comm  P Q (H: P \/ Q)  :=
  match H with
  | or_introl HP => or_intror HP
  | or_intror HQ  => or_introl HQ
  end.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => even n).


Definition some_nat_is_even : exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).

Module Props.

(*TrueはTrueを返す
 　Falseはコンストラクタを持たない定義である*)
Inductive True : Prop :=
  | I : True.


Inductive False : Prop := .

End Props.


Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.


Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].



Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
  intros X x y H H0. inversion H. intros.  apply H3.
Qed.


Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros X x y.
Abort.

End MyEquality.
