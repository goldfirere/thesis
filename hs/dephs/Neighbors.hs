-- ideas From Conor's ICFP '14 paper

{-# LANGUAGE TemplateHaskell, DataKinds, PolyKinds, ScopedTypeVariables,
             GADTs, TypeOperators, TypeFamilies, UndecidableInstances #-}

module Neighbors where

import Data.Singletons.TH
import Data.Singletons.Prelude
import GHC.TypeLits hiding (Nat)

$(singletons [d|
  data Nat = Zero | Succ Nat
  |])

$(promote [d|
  instance Num Nat where
    Zero + n = n
    (Succ n) + m = Succ (n + m)

    Zero * n = Zero
    (Succ n) * m = m + (n * m)

    Zero - n = Zero
    (Succ n) - Zero = (Succ n)
    (Succ n) - (Succ m) = n - m

    negate _ = error "no negative Nats"

    abs n = n

    signum Zero = Zero
    signum (Succ _) = Succ Zero

    from

  |])

type family U n where
  U 0 = Zero
  U n = Succ (U (n-1))

type Inf = U 20
sInf :: Sing Inf
sInf = sing

data (<) :: Nat -> Nat -> * where
  LtZ :: Zero < (Succ n)
  LtS :: m < n -> Succ m < Succ n

data BST :: Nat -> Nat -> * where
  Node :: BST min n -> SNat n -> BST n max -> BST min max
  Leaf :: BST min max

type IBST = BST Zero Inf

-- insert :: SNat n -> BST min max -> BST (Min 
