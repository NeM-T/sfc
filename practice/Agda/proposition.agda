module proposition where

postulate A : Set
postulate B : Set

Lemma1 : Set
Lemma1 = A -> ( A -> B ) -> B
lemma1 : Lemma1
lemma1 a b = b a
-- lemma1 a a-b = a-b a

lemma2 : Lemma1
lemma2 = \a b -> b a
-- lemma1 = \a a-b -> a-b a
-- lemma1 = \a b -> b a
-- lemma1  a b = b a

lemma3 : Lemma1
lemma3 = \a -> ( \b -> b a )

record _∧_ (A B : Set) : Set where
  field
    and1 : A
    and2 : B

--data & ( A B : Set ) : Set where
  --and : A -> B -> A & B

Lemma4 : Set
Lemma4 = B -> A -> (B ∧ A)
lemma4 : Lemma4
lemma4 = \b -> \a -> record { and1 = b ;  and2 = a }

Lemma5 : Set
Lemma5 = (A ∧ B) -> B
lemma5 : Lemma5
lemma5 = \a -> (_∧_.and2 a)

data _∨_  (A B : Set) : Set where
  or1 : A -> A ∨ B
  or2 : B -> A ∨ B

Lemma6  : Set
Lemma6 = B -> ( A ∨ B )
lemma6 : Lemma6
lemma6 = \b ->  or2 b

Lemma41 : Set
Lemma41 = A -> A
lemma41 : Lemma41
lemma41 = \a -> a

Lemma42 : Set
Lemma42 = (A ∧ (A -> B)) -> B
lemma42 : Lemma42
lemma42 = \a -> (_∧_.and2 a) (_∧_.and1 a)

Lemma31 : Set
Lemma31 = (A ∧ (A -> B)) -> (A -> B)
lemma31 : Lemma31
lemma31 = \a -> _∧_.and2 a

Lemma32 : Set
Lemma32 = (A ∧ (A -> B)) ->  A
lemma32 : Lemma32
lemma32 = \a -> _∧_.and1 a

Lemma33 : Set
Lemma33 = A -> ( A -> B ) -> B
lemma33 : Lemma33
lemma33 = \a -> \b -> b a

Lemma43 : Set
Lemma43 = (A ∧ (A -> B)) -> B

Lemma44 : Set
Lemma44 = A -> (B -> A)

