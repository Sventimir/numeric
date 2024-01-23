module Data.Integer

import Data.Nat

%default total


data I : Type where
  N : Nat -> I
  Neg : (n : Nat) -> NonZero n -> I

data Negative : I -> Type where
  NegI : (n : Nat) -> (prf : NonZero n) -> Negative (Neg n prf)
  
data Positive : I -> Type where
  PosI : (n : Nat) -> NonZero n -> Positive (N n)
  
data NonZero : I -> Type where
  PosNonZero : (n : Nat) -> NonZero n -> NonZero (N n)
  NegNonZero : (n : Nat) -> (prf : NonZero n) -> NonZero (Neg n prf)
 

succ : I -> I
succ (N k) = N (S k)
succ (Neg 1 prf) = N 0
succ (Neg (S (S k)) _) = Neg (S k) SIsNonZero

pred : I -> I
pred (N 0) = Neg 1 SIsNonZero
pred (N (S k)) = N k
pred (Neg n _) = Neg (S n) SIsNonZero

predSuccId : (i : I) -> pred (succ i) = i
predSuccId (N k) = Refl
predSuccId (Neg (S 0) SIsNonZero) = Refl
predSuccId (Neg (S (S k)) SIsNonZero) = Refl

succPredId : (i : I) -> succ (pred i) = i
succPredId (N 0) = Refl
succPredId (N (S k)) = Refl
succPredId (Neg (S n) SIsNonZero) = Refl

neg : I -> I
neg (N 0) = N 0
neg (N (S k)) = Neg (S k) SIsNonZero
neg (Neg (S n) SIsNonZero) = N (S n)


plusI : I -> I -> I
plusI (N k) (N j) = N (k + j)
plusI (N k) (Neg j _) with (cmp k j)
  plusI (N (j + S d)) (Neg j _) | CmpGT d = N (S d)
  plusI (N k) (Neg k _) | CmpEQ = N 0
  plusI (N k) (Neg (k + S d) _) | CmpLT d = Neg (S d) SIsNonZero
plusI (Neg k _) (N j) with (cmp k j)
  plusI (Neg (j + S d) _) (N j) | CmpGT d = Neg (S d) SIsNonZero
  plusI (Neg k _) (N k) | CmpEQ = N 0
  plusI (Neg k _) (N (k + S d)) | CmpLT d = N (S d)
plusI (Neg (S _) SIsNonZero) (Neg 0 prf) = absurd prf
plusI (Neg (S k) SIsNonZero) (Neg (S j) SIsNonZero) = Neg (S (S (k + j))) SIsNonZero

(+) : I -> I -> I
(+) = plusI

minusI : I -> I -> I
minusI i j = plusI i (neg j)

(-) : I -> I -> I
(-) = minusI

mulI : I -> I -> I
mulI (N k) (N j) = N (k * j)
mulI (N k) (Neg (S j) SIsNonZero) = Neg (S k * S j) SIsNonZero
mulI (Neg (S k) SIsNonZero) (N j) = Neg (S k * S j) SIsNonZero
mulI (Neg (S k) SIsNonZero) (Neg (S j) SIsNonZero) = N (k * j)

(*) : I -> I -> I
(*) = mulI

negNat : Nat -> I
negNat 0 = N 0
negNat (S k) = Neg (S k) SIsNonZero

divModI : (p, d : I) -> NonZero d -> (I, I)
divModI (N k) (N j) (PosNonZero j prf) =
  let (q, r) = divmodNatNZ k j prf in
  (N q, N r)
divModI (N k) (Neg j prf) (NegNonZero j prf) =
  let (q, r) = divmodNatNZ k j prf in
  (negNat q, N r)
divModI (Neg k y) (N j) (PosNonZero j prf) =
  let (q, r) = divmodNatNZ k j prf in
  (negNat q, negNat r)
divModI (Neg k y) (Neg j prf) (NegNonZero j prf) =
  let (q, r) = divmodNatNZ k j prf in
  (N q, negNat r)
