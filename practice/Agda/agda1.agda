module agda1 where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data Nat : Set where
  O : Nat
  S  : Nat -> Nat

infixl 40 _+_
infixl 60 _*_

_+_ : Nat -> Nat -> Nat
O + m = m
S n + m = S (n + m)

_*_ : Nat -> Nat -> Nat
O * m = O
S n * m = m + (n * m)

