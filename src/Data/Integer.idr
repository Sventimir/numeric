module Data.Integer

import Data.Nat

%default total


data Sign = Positive | Zero | Negative

nonNegative : Sign -> Type
nonNegative Positive = ()
nonNegative Zero = ()
nonNegative Negative = Void

nonPositive : Sign -> Type
nonPositive Positive = Void
nonPositive Zero = ()
nonPositive Negative = ()

nonZero : Sign -> Type
nonZero Positive = ()
nonZero Zero = Void
nonZero Negative = ()


data SignedI : Sign -> Type where
  Z : SignedI Zero
  S : (0 s : Sign) -> (w : nonNegative s) -> (i : SignedI s) -> SignedI Positive
  P : (0 s : Sign) -> (w : nonPositive s) -> (i : SignedI s) -> SignedI Negative
  
data I : Type where
  MkI : (i : SignedI s) -> I
  
succ' : SignedI s -> (s' : Sign ** SignedI s')
succ' Z = (Positive ** S Zero () Z)
succ' (S s w i) = (Positive ** S Positive () (S s w i))
succ' (P Zero w Z) = (Zero ** Z)
succ' (P Positive w (S s _ i)) = void w
succ' (P Negative w (P s w' i)) = (Negative ** P s w' i)

succ : I -> I
succ (MkI i) = let (_ ** i') = succ' i in MkI i'

pred' : SignedI s -> (s' : Sign ** SignedI s')
pred' Z = (Negative ** P Zero () Z)
pred' (S Zero w Z) = (Zero ** Z)
pred' (S Positive w (S s w' i)) = (Positive ** S s w' i)
pred' (S Negative w (P _ _ _)) = void w
pred' (P s w i) = (Negative ** P Negative () (P s w i))

pred : I -> I
pred (MkI i) = let (_ ** i') = pred' i in MkI i'

predSuccId : (i : I) -> succ (pred i) = i
predSuccId (MkI Z) = Refl
predSuccId (MkI (S Zero () Z)) = Refl
predSuccId (MkI (S Positive () (S s w i))) = Refl
predSuccId (MkI (S Negative w (P _ _ _))) = void w
predSuccId (MkI (P s w i)) = Refl

succPredId : (i : I) -> pred (succ i) = i
succPredId (MkI Z) = Refl
succPredId (MkI (S s w i)) = Refl
succPredId (MkI (P Zero () Z)) = Refl
succPredId (MkI (P Positive w (S _ _ _))) = void w
succPredId (MkI (P Negative () (P s w i))) = Refl

fromNat' : Nat -> Either (SignedI Zero) (SignedI Positive)
fromNat' 0 = Left Z
fromNat' (S k) = Right $ case fromNat' k of
    Left i => S Zero () i
    Right i => S Positive () i
    
fromNat : Nat -> I
fromNat n = case fromNat' n of
  Left i => MkI i
  Right i => MkI i

fromIntegerI : Integer -> I
fromIntegerI i = case compare i 0 of
  GT => case fromNat' $ fromInteger i of
    Left i => MkI i
    Right i => MkI i
  EQ => MkI Z
  LT => case fromNat' $ fromInteger (-i) of
    Left i => MkI i
    Right i => MkI i

abs' : SignedI s -> Nat
abs' Z = Z
abs' (S s w i) = S (abs' i)
abs' (P s w i) = S (abs' i)

abs : I -> Nat
abs (MkI i) = abs' i

plusI' : SignedI _ -> SignedI _ -> I
plusI' i Z = MkI i
plusI' Z i = MkI i
plusI' (S Zero () Z) (S s w j) = MkI (S Positive () (S s w j))
plusI' (S Positive () (S s w i)) (S _ _ j) = plusI' (S Positive () (S Positive () (S s w i))) j
plusI' (S Negative w (P x y i)) (S _ _ _) = void w
plusI' (S _ _ i) (P _ _ j) = plusI' i j
plusI' (P _ _ i) (S _ _ j) = plusI' i j
plusI' (P Zero () Z) (P s w j) = MkI (P Negative () (P s w j))
plusI' (P Positive w (S x y i)) (P _ _ _) = void w
plusI' (P Negative () (P s w i)) (P _ _ j) = plusI' (P Negative () (P Negative () (P s w i))) j

plusI : I -> I -> I
plusI (MkI i) (MkI j) = plusI' i j



mulI : I -> I -> I

Num I where
  (+) = plusI
  (*) = mulI
  fromInteger = fromIntegerI

succEq : (i, j : I) -> i = j -> succ i = succ j
succEq (MkI Z) (MkI Z) Refl = Refl
succEq (MkI (S s w i)) (MkI (S s w i)) Refl = Refl
succEq (MkI (P s w i)) (MkI (P s w i)) Refl = Refl

-- ATTENTION: notice the ugly believe_me at the end. It shouldn't be
-- needed; I believe we're being hit by a unification bug in the
-- typechecker here. Please revisit, when the issue is investigated.
succElim : (i, j : I) -> succ i = succ j -> i = j
succElim (MkI Z) (MkI Z) Refl = Refl
succElim (MkI Z) (MkI (P Positive w (S _ _ _))) prf = void w
succElim (MkI (S s w i)) (MkI (S s w i)) Refl = Refl
succElim (MkI (S s _ i)) (MkI (P Positive w (S s' _ j))) prf = void w
succElim (MkI (P Positive w (S _ _ _))) (MkI Z) prf = void w
succElim (MkI (P Positive w (S _ _ _))) (MkI (S _ _ _)) prf = void w
succElim (MkI (P Zero () Z)) (MkI (P Zero () Z)) Refl = Refl
succElim (MkI (P Zero _ Z)) (MkI (P Positive w (S _ _ _))) prf = void w
succElim (MkI (P Positive w (S _ _ _))) (MkI (P _ _ _)) prf = void w
succElim (MkI (P Negative _ (P _ _ _))) (MkI (P Positive w (S _ _ _))) prf = void w
succElim (MkI (P Negative () (P s w i))) (MkI (P Negative x (P s' w' j))) prf =
  rewrite the (x = ()) $ believe_me () in
  cong pred prf

predEq : (i, j : I) -> i = j -> pred i = pred j
predEq (MkI Z) (MkI Z) Refl = Refl
predEq (MkI (S s w i)) (MkI (S s w i)) Refl = Refl
predEq (MkI (P s w i)) (MkI (P s w i)) Refl = Refl

predElim : (i, j : I) -> pred i = pred j -> i = j
predElim (MkI Z) (MkI Z) Refl = Refl
predElim (MkI Z) (MkI (S Negative w (P _ _ _))) prf = void w
predElim (MkI (S Negative w (P _ _ _))) (MkI Z) prf = void w
predElim (MkI (S Zero () Z)) (MkI (S Zero () Z)) Refl = Refl
predElim (MkI (S Zero _ Z)) (MkI (S Negative w (P _ _ _))) prf = void w
predElim (MkI (S Positive () (S s w i))) (MkI (S Positive () (S s w i))) Refl = Refl
predElim (MkI (S Positive _ (S _ _ _))) (MkI (S Negative w (P _ _ _))) prf = void w
predElim (MkI (S Negative w (P _ _ _))) (MkI (S _ _ _)) prf = void w
predElim (MkI (S Negative w (P _ _ _))) (MkI (P Zero _ Z)) prf = void w
predElim (MkI (P _ _ _)) (MkI (S Negative w (P _ _ _))) prf = void w
predElim (MkI (P s w i)) (MkI (P s w i)) Refl = Refl

-- plusISuccLeftSucc : (i, j : I) -> succ (i + j) = succ i + j
