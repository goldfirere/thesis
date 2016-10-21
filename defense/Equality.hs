{-# LANGUAGE TypeOperators, GADTs, TypeInType, TypeFamilies #-}

module Equality where

import qualified Basics as B
import Basics ( Sing, Π, Nat )
import Data.Kind
import qualified Data.Type.Equality as DTE

data SNat :: Nat -> Type where
  Zero :: SNat 'B.Zero
  Succ :: SNat n -> SNat ('B.Succ n)

type instance Sing = SNat
















data a :~: b where
  Refl :: a :~: a

class DEq a where
  eq :: Π (x :: a) -> Π (y :: a) -> Maybe (x :~: y)
