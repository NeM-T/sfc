module plfa.part1.Naturals where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ = refl

_*_ : Nat → Nat → Nat
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

_^_ : Nat → Nat → Nat
m ^ 0        =  1
m ^ (suc n)  =  m * (m ^ n)


_∸_ : Nat → Nat → Nat
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    3 ^ 4
   ≡⟨⟩
    3 * (3 ^ 3)
   ≡⟨⟩
    3 * (3 * (3 ^ 2))
   ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
   ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
   ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
   ≡⟨⟩
    81
   ∎

infixl 6 _+_
infixl 7 _*_
infixl 8 _^_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  <> : Bin
  _O : Bin → Bin
  _I : Bin → Bin

