
module Vec where

data Nat = Zero | Succ Nat

data Vec :: * -> Nat -> * where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

type family Plus a b where
  Plus Zero a = a
  Plus (Succ a) b = Succ (Plus a b)

type family VecAppend (v1 :: Vec a m) (v2 :: Vec a n) :: Vec a (Plus m n) where
  VecAppend VNil v2 = v2
  VecAppend (VCons h t) v2 = VCons h (VecAppend t v2)

type family SafeHead (v :: Vec a (Succ n)) :: a where
  SafeHead (VCons h t) = h

type family Pred n where
  Pred Zero = Zero
  Pred (Succ n) = n

type family Tail (v :: Vec a n) :: Pred n where
  Tail VNil = VNil
  Tail (VCons h t) = t