module Basics

%access public export

namespace Days
  data Day =
    Monday
    | Tuesday
    | Wednesday
    | Thursday
    | Friday
    | Saturday
    | Sunday

nextWeekday : Day -> Day
nextWeekday Monday    = Tuesday
nextWeekday Tuesday   = Wednesday
nextWeekday Wednesday = Thursday
nextWeekday Thursday  = Friday
nextWeekday Friday    = Saturday
nextWeekday Saturday  = Sunday
nextWeekday Sunday    = Monday

testNextWeekday :
  (nextWeekday(nextWeekday Saturday)) = Monday
testNextWeekday = Refl
-- Refl = reflexivity かな？

namespace Booleans

  data Bol = True | False

  data Bool' : Type where
       True' : Bool'
       False' : Bool'

not : (b: Bol) -> Bol
not True  = False
not False = True

andb : (b1: Bol) -> (b2: Bol) -> Bol
andb True b2 = b2
andb False _ = False

orb : (b1: Bol) -> (b2: Bol) -> Bol
orb True _   = True
orb False b2 = b2

infixl 4 &?, |?

(&?) : Bol -> Bol -> Bol
(&?) = andb

(|?) : Bol -> Bol -> Bol
(|?) = orb

testOrb : False |? False |? True = True
testOrb = Refl


namespace Number
  data Nat' : Type where
         Z : Nat'
         S : Nat' -> Nat'

  pred : (n: Nat') -> Nat'
  pred Z     = Z
  pred (S m) = m

  evenb : (n: Nat') -> Bol
  evenb Z         = True
  evenb (S Z)     = False
  evenb (S (S m)) = evenb m

  oddb : (n: Nat') -> Bol
  oddb Z          = False
  oddb (S Z)      = True
  oddb (S (S m))  = oddb m


namespace Playground2
  plus' : (n: Nat') -> (m: Nat') -> Nat'
  plus' Z m = m
  plus' (S k) m = S (plus' k m)

  mult' : (n, m: Nat') -> Nat'
  mult' Z _     = Z
  mult' (S k) m = plus' m (mult' k m)

  minus' : (n, m: Nat')  -> Nat'
  minus' Z      _    = Z
  minus' n      Z    = n
  minus' (S k) (S j) = minus' k j

  exp' : (base, power: Nat') -> Nat'
  exp' base Z     = S Z
  exp' base (S p) = mult' base (exp' base p)

  fanctional : (n: Nat') -> Nat'
  fanctional Z     = S Z
  fanctional (S m) = mult' (S m) (fanctional m)

  testfanctional : fanctional (S (S (S Z))) = (S (S (S (S (S (S Z))))))
  testfanctional = Refl

plus_Z_n : (n: Nat) -> 0 + n = n
plus_Z_n n = Refl

plus_1_S : (n: Nat) -> 1 + n = S n
plus_1_S n = Refl

mult_0_1 : (n: Nat) -> 0 * n = 0
mult_0_1 n = Refl

-- p.21 Proof by Rewriting
plus_id_exaple : (n, m: Nat) -> (n = m) -> n + n = m + m
plus_id_exaple n m prf = rewrite prf in Refl
