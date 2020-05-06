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

plus_id_exaple : (n, m: Nat) -> (n = m) -> n + n = m + m
plus_id_exaple n m prf = rewrite prf in Refl

plus_id_exercise : (n, m, o : Nat) -> (n = m) -> (m = o)  -> n + m = m + o
plus_id_exercise n m o h h1 = rewrite h in rewrite h1 in Refl

mult_S_1 : (n, m: Nat) -> (m = S n) -> m * (1 + n) = m * m
mult_S_1 n m prf = ?mult_S_1_rhs -- proof hool (後回しにする)
mult_S_1_rhs n m prf = rewrite prf in Refl


plus_1_neq_0_firsttry : (n: Nat) -> (n + 1) == 0 = False
plus_1_neq_0_firsttry Z = Refl
plus_1_neq_0_firsttry (S n) = Refl

not_involutive : (b: Bool) -> not (not b) = b
not_involutive True  = Refl
not_involutive False = Refl

andb_commutative : (b, c: Bool) -> b && c = c && b
andb_commutative True True   = Refl
andb_commutative True False  = Refl
andb_commutative False True  = Refl
andb_commutative False False = Refl

andb_true_elim_2 : (b, c: Bool) -> (b && c = True) -> c = True
andb_true_elim_2 True True prf = Refl


zero_nbeq_plus_1 : (n: Nat) -> 0 == (n + 1) = False
zero_nbeq_plus_1    Z  = Refl
zero_nbeq_plus_1 (S n) = Refl

identity_fn_applied_twice :
  (f: Bool -> Bool) -> ((x: Bool) -> f x = x) -> (b: Bool) -> f (f b)  = b
identity_fn_applied_twice f h b = ?id_tw


---------- Proofs ----------
id_tw = proof
  intros
  rewrite h b
  rewrite h (f b)
  trivial

andb_eq_orb : (b, c: Bool) -> (b && c = b || c) -> b = c
andb_eq_orb True True h = Refl
andb_eq_orb False False h = Refl
