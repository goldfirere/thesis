{-# LANGUAGE GADTs, KindSignatures, PolyKinds, DeriveTraversable, DeriveFoldable,
             DeriveFunctor, TypeFamilies, RankNTypes, TypeOperators, DataKinds,
             TemplateHaskell, MagicHash, UnboxedTuples, StandaloneDeriving,
             FlexibleInstances, MultiWayIf, LambdaCase, CPP, ParallelListComp,
             BangPatterns, MonadComprehensions, MultiParamTypeClasses,
             UndecidableInstances, -- AllowAmbiguousTypes,
             ScopedTypeVariables, GeneralizedNewtypeDeriving,
             NoMonomorphismRestriction #-}


module Scratch where

import Prelude hiding (filter)
import GHC.TypeLits
import Data.Type.Bool

data Proxy p = Proxy
data family Sing (a :: k)

data Nat1 = Zero | Succ Nat1

data instance Sing (a :: Nat1) where
  SZero :: Sing Zero
  SSucc :: Sing n -> Sing (Succ n)

data instance Sing (a :: Bool) where
  SFalse :: Sing False
  STrue  :: Sing True

deriving instance Show (Sing (a :: Nat1))
deriving instance Show (Sing (a :: Bool))

class SingI (a :: k) where
  sing :: Sing a

instance SingI Zero where
  sing = SZero
instance SingI n => SingI (Succ n) where
  sing = SSucc sing

data Flag = Empty | NotEmpty

data List :: Flag -> [k] -> * where
  Nil :: List Empty '[]
  Cons :: Sing h -> List f t -> List NotEmpty (h ': t)
infixr 5 `Cons`

data TyFun :: * -> * -> *

type family Gt2 n where
  Gt2 Zero = False
  Gt2 (Succ Zero) = False
  Gt2 (Succ (Succ Zero)) = False
  Gt2 (Succ (Succ (Succ n))) = True

data Gt2_sym :: TyFun Nat1 Bool -> *

type family (fun :: TyFun k1 k2 -> *) @@ (arg :: k1) :: k2

type instance Gt2_sym @@ n = Gt2 n
infixl 9 @@

type family Any f xs where
  Any f '[] = False
  Any f (x ': xs) = f @@ x || Any f xs

type family Filter f xs where
  Filter f '[] = '[]
  Filter f (x ': xs) = If (f @@ x) (x ': Filter f xs) (Filter f xs)

type family ToFlag b where
  ToFlag False = Empty
  ToFlag True  = NotEmpty

filter :: Proxy f
       -> (forall a. Sing a -> Sing (f @@ a))
       -> List flag1 as
       -> List (ToFlag (Any f as)) (Filter f as)
filter _ _ Nil = Nil
filter proxy f (Cons x xs) =
  case f x of
    STrue  -> Cons x (filter proxy f xs)
    SFalse -> filter proxy f xs

type family U n where
  U 0 = Zero
  U n = Succ (U (n-1))

one :: Sing (U 1)
one = sing

two :: Sing (U 2)
two = sing

three :: Sing (U 3)
three = sing

four :: Sing (U 4)
four = sing

zero :: Sing (U 0)
zero = sing

example = three `Cons` one `Cons` four `Cons` two `Cons` three `Cons` zero `Cons` Nil

gt2 :: Sing a -> Sing (Gt2 a)
gt2 SZero = SFalse
gt2 (SSucc SZero) = SFalse
gt2 (SSucc (SSucc SZero)) = SFalse
gt2 (SSucc (SSucc (SSucc _))) = STrue


