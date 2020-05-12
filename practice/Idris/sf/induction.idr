module induction

import Prelude.Interfaces
import Prelude.Nat

%access public export
%default total


-- 帰納法
plus_n_Z : (n: Nat) -> n = n + 0
plus_n_Z Z = Refl
plus_n_Z (S n) =
  let inductiveHypothesis = plus_n_Z n in
    rewrite inductiveHypothesis in Refl

minus_diag : (n: Nat) -> minus n n = 0
minus_diag  Z = Refl
minus_diag (S k) = minus_diag k

mult_0_r : (n: Nat) -> n * 0 = 0
mult_0_r    Z  = Refl
mult_0_r (S n) = mult_0_r n

plus_n_S : (n, m: Nat) -> S (n + m) = n + (S m)
plus_n_S    Z  m = Refl
plus_n_S (S n) m =
  let inductionh = plus_n_S n m in
    rewrite inductionh in Refl

plus_comm : (n, m: Nat) -> n + m = m + n
plus_comm n  Z = rewrite plus_n_Z n in Refl
plus_comm n (S m) =
  let h = plus_comm n m in
    ?plus_ch

plus_ch = proof
  intros
  rewrite h
  rewrite plus_n_S n m
  trivial

plus_assoc : (n, m, p: Nat) -> n + (m + p) = (n + m) + p
plus_assoc Z m p = Refl
plus_assoc (S n) m p =
  let inductionh = plus_assoc n m p in
    rewrite inductionh in Refl

double : (n: Nat) -> Nat
double    Z  = Z
double (S n) = S (S (double n))

double_plus : (n: Nat) -> double n = n + n
double_plus Z = Refl
double_plus (S n) =
  let h = double_plus n in
    ?dp

dp = proof
  intros
  rewrite plus_n_S n n
  rewrite h
  trivial


evenb : (n: Nat) -> Bool
evenb Z         = True
evenb (S Z)     = False
evenb (S (S m)) = evenb m


not_involutive : (b: Bool) -> not (not b) = b
not_involutive True  = Refl
not_involutive False = Refl


evenb_S : (n: Nat) -> evenb (S n) = not (evenb n)
evenb_S Z = Refl
evenb_S (S n) = 
  let h = evenb_S n in ?evS

---------- Proofs ----------
evS = proof

  intros
  rewrite not_involutive (evenb n)
  rewrite h
  trivial

plus_rearrange_firsttry : (n, m, p, q: Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange_firsttry n m p q= rewrite plus_rearrange_lemma n m in Refl
  where
  plus_rearrange_lemma : (n, m: Nat) -> n + m = m + n
  plus_rearrange_lemma = plus_comm

plus_swap : (n, m, p: Nat) -> n + (m + p) = m + (n + p)
plus_swap Z m p = Refl
plus_swap (S n) m p =
  let h = plus_swap n m p in
    rewrite h in rewrite plus_n_S m (n + p) in Refl

mult_scc : (n, m: Nat) -> m * (S n) = plus m (m * n)
mult_scc n Z = Refl
mult_scc n (S m) =
  let h = mult_scc n m in
    let h1= plus_swap n m (m * n) in
      rewrite h in rewrite h1 in Refl


mult_comm : (n, m: Nat) -> m * n = n * m
mult_comm Z m = rewrite mult_0_r m in Refl
mult_comm (S n) m =
  let h = mult_comm n m in 
    rewrite mult_scc n m in rewrite h in Refl

lte_refl : (n: Nat) -> True = lte n n
lte_refl Z = Refl
lte_refl (S n) = let h = lte_refl n in rewrite h in Refl

zero_nbeq_S : (n: Nat) -> 0 == (S n) = False
zero_nbeq_S n = Refl

andb_false_r : (b: Bool) -> b && False = False
andb_false_r True  = Refl
andb_false_r False = Refl

plus_ble_compat_l : (n, m, p: Nat) -> lte n m = True -> lte (p + n) (p + m) = True
plus_ble_compat_l n m Z h = rewrite h in Refl
plus_ble_compat_l n m (S p) h =
  let h1 = plus_ble_compat_l n m p in
     rewrite h1 h in Refl

S_nbeq_0 : (n: Nat) -> (S n) == 0 = False
S_nbeq_0 Z = Refl
S_nbeq_0 (S n) = Refl

mult_1_1 : (n: Nat) -> 1 * n = n
mult_1_1 Z = Refl
mult_1_1 (S n) =
  rewrite plus_n_Z n in Refl

all_3_spec : (b, c: Bool) -> (b && c) || (not b) || (not c) = True
all_3_spec False _     = Refl
all_3_spec True  False = Refl
all_3_spec True  True  = Refl
