{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Singletons where

-- A version of singletons designed to work with kind equalities
-- and with typelits

import Data.Type.Equality
import GHC.Exts
import Data.Type.Bool
import Data.Proxy

import GHC.TypeLits
import Unsafe.Coerce

----------------------------------------------------------------------
-- basic singletons stuff
----------------------------------------------------------------------

data family Sing (a :: k)

class SingI (a :: k) where sing :: Sing a

class SingKind k where
  type DemoteRep k :: *
  fromSing :: Sing (x :: k) -> DemoteRep k


----------------------------------------------------------------------
-- singletons for GHC.TypeLit Nats
----------------------------------------------------------------------
    
data instance Sing (n :: Nat) = KnownNat n => SNat

instance KnownNat n => SingI n where sing = SNat

instance SingKind Nat where
  type DemoteRep Nat = Integer
  fromSing (SNat :: Sing n) = natVal (Proxy :: Proxy n)

  
sEqNat :: forall (a :: Nat) b. Sing a -> Sing b -> Maybe (a :~: b)
sEqNat SNat SNat = sameNat (Proxy :: Proxy a) (Proxy :: Proxy b)
  

(%:+) :: forall a b . Sing a -> Sing b -> Sing (a + b)
sa %:+ sb =
    let a = fromSing sa
        b = fromSing sb
        ex = someNatVal (a + b)
    in
    case ex of
      Just (SomeNat (_ :: Proxy ab)) -> unsafeCoerce (SNat :: Sing ab)
      Nothing                        -> error "Two naturals added to a negative?"

----------------------------------------------------------------------
-- singletons for lists and booleans
----------------------------------------------------------------------
      
data instance Sing (a :: [k]) where
  SNil  :: Sing '[]
  SCons :: Sing h -> Sing t -> Sing (h ': t)
infixr 5 `SCons`

data instance Sing (a :: Bool) where
  SFalse :: Sing 'False
  STrue :: Sing 'True

-- `If` type family from Data.Type.Bool
sIf :: Sing a -> Sing b -> Sing c -> Sing (If a b c)
sIf SFalse _ c = c
sIf STrue  b _ = b
