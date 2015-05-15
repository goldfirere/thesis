{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Singletons where


import Prelude ( Bool(..), undefined, return )
import GHC.TypeLits ( type (-) )
import Data.Type.Equality
import GHC.Exts
import Data.Type.Bool
import Data.Proxy


-- standard definition of natural numbers and their
-- singletons
data Nat :: * where
  Zero :: Nat
  Succ :: Nat -> Nat

data family Sing (a :: k)

data instance Sing (n :: Nat) where
  SZero :: Sing 'Zero
  SSucc :: Sing n -> Sing ('Succ n)

(+) :: Nat -> Nat -> Nat
Zero   + m = m
Succ n + m = Succ (n + m)
infixl 6 +

type family a :+ b where
  'Zero :+ m = m
  'Succ n :+ m = 'Succ (n :+ m)

(%:+) :: Sing a -> Sing b -> Sing (a :+ b)
SZero %:+ m = m
SSucc n %:+ m = SSucc (n %:+ m)

-- singletons for lists and booleans
data instance Sing (a :: [k]) where
  SNil  :: Sing '[]
  SCons :: Sing h -> Sing t -> Sing (h ': t)
infixr 5 `SCons`

data instance Sing (a :: Bool) where
  SFalse :: Sing 'False
  STrue :: Sing 'True

-- If type family from Data.Type.Bool
sIf :: Sing a -> Sing b -> Sing c -> Sing (If a b c)
sIf SFalse _ c = c
sIf STrue  b _ = b
