module Peano
  
-- Check all definitions for totality.
-- This is necessary to actually prove anything.
-- Furthermore, Idris will not evaluate non-total functions while typechecking.
%default total

-- Define the Peano numbers.
data N = Z | S N

-- Define addition on Peano numbers (in terms of repeated successor).
pls : N -> N -> N
pls m Z = m
pls m (S n) = S (pls m n)
  
plus_succ_shift : (m, n : N) -> pls (S m) n = pls m (S n)
plus_succ_shift m Z = Refl
plus_succ_shift m (S n) = rewrite plus_succ_shift m n in Refl
-- rewrite is sugar around replace (actually around rewrite__impl)
  
plus_commutes : (m, n : N) -> pls m n = pls n m
plus_commutes Z n = plus_zero_commutes n
  where plus_zero_left : (m : N) -> m = pls Z m
        plus_zero_left Z = Refl 
        plus_zero_left (S k) = cong (plus_zero_left k) 
        plus_zero_commutes : (m : N) -> pls Z m = pls m Z
        plus_zero_commutes m = sym (plus_zero_left m)
plus_commutes (S m) n = rewrite plus_succ_shift m n in cong (plus_commutes m n)

plus_associates : (m, n, p : N) -> pls (pls m n) p = pls m (pls n p)
plus_associates m n Z = Refl
plus_associates m n (S p) = rewrite plus_associates m n p in Refl

-- Define multiplication on Peano numbers (in terms of repeated addition).
mul : N -> N -> N
mul m Z = Z
mul m (S n) = pls m (mul m n)
  
mul_commutes : (m, n : N) -> mul m n = mul n m
mul_commutes Z n = mul_zero_commutes n
  where mul_zero_left : (m : N) -> mul Z m = Z
        mul_zero_left Z = Refl
        mul_zero_left (S m) = rewrite mul_zero_left m in Refl
        mul_zero_commutes : (m : N) -> mul Z m = mul m Z
        mul_zero_commutes m = rewrite mul_zero_left m in Refl
mul_commutes (S m) n = rewrite mul_plus_right m n in
                       rewrite mul_commutes m n in
                       rewrite plus_commutes n (mul n m) in Refl
  where mul_plus_right : (m, n : N) -> mul (S m) n = pls (mul m n) n
        mul_plus_right m Z = Refl
        mul_plus_right m (S n) = rewrite mul_plus_right m n in
                                 rewrite plus_succ_shift m (pls (mul m n) n) in
                                 rewrite plus_associates m (mul m n) n in Refl
  
mul_distributes_plus : (m, n, p : N) -> mul (pls m n) p = pls (mul m p) (mul n p)
mul_distributes_plus m n Z = Refl
mul_distributes_plus m n (S p) = rewrite mul_distributes_plus m n p in
                                 rewrite plus_associates m n (pls (mul m p) (mul n p)) in
                                 rewrite plus_associates m (mul m p) (pls n (mul n p)) in
                                 rewrite plus_swapout (mul m p) n (mul n p) in Refl
  where plus_swapout : (m, n, p : N) -> pls m (pls n p) = pls n (pls m p)
        plus_swapout m n p = rewrite plus_commutes m (pls n p) in
                             rewrite plus_associates n p m in
                             rewrite plus_commutes m p in Refl

mul_associates : (m, n, p : N) -> mul (mul m n) p = mul m (mul n p)
mul_associates m n Z = Refl
mul_associates m n (S p) = rewrite mul_associates m n p in
                           rewrite mul_commutes m (pls n (mul n p)) in
                           rewrite mul_distributes_plus n (mul n p) m in
                           rewrite mul_commutes (mul n p) m in
                           rewrite mul_commutes n m in Refl

-- Define exponentiation on Peano numbers (in terms of repeated multiplication).
exp : N -> N -> N
exp m Z = (S Z)
exp m (S n) = mul m (exp m n)

exp_distributes_mul : (m, n, p : N) -> exp (mul m n) p = mul (exp m p) (exp n p)
exp_distributes_mul m n Z = Refl
exp_distributes_mul m n (S p) = rewrite exp_distributes_mul m n p in
                                rewrite mul_associates m n (mul (exp m p) (exp n p)) in
                                rewrite mul_associates m (exp m p) (mul n (exp n p)) in
                                rewrite mul_swapout (exp m p) n (exp n p) in Refl
  where mul_swapout : (m, n, p : N) -> mul m (mul n p) = mul n (mul m p)
        mul_swapout m n p = rewrite mul_commutes m (mul n p) in
                            rewrite mul_associates n p m in
                            rewrite mul_commutes m p in Refl
