-- Adapted from Idris's algebraic effects library

{-# LANGUAGE TypeInType, RebindableSyntax, GADTs, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies, ScopedTypeVariables,
             TypeApplications, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Effect.Random where

import Data.Kind
import Data.Nat
import Effects
import Data.Singletons

data Random :: Type -> Type -> Type -> Type where
  GetRandom :: Random Nat Nat Nat
  SetSeed   :: Nat -> Random Nat Nat ()

data instance Sing (x :: Random a b c) where
  SGetRandom :: Sing GetRandom
  SSetSeed   :: Sing n -> Sing (SetSeed n)

instance (Good a, Good b, Good c) => SingKind (Random a b c) where
  type DemoteRep (Random a b c) = Random a b c

  fromSing SGetRandom = GetRandom
  fromSing (SSetSeed x) = SetSeed (fromSing x)

  toSing GetRandom = SomeSing SGetRandom
  toSing (SetSeed x) = case toSing x of SomeSing x' -> SomeSing (SSetSeed x')

instance Handler (TyCon3 Random) m where
  handle GetRandom seed k
    = let seed' = (3 * seed + 1) `mod` 213 in
      k seed' seed'
  handle (SetSeed n) _ k = k n ()

type RND = MkEff Nat (TyCon3 Random)

rndNat_ :: Nat -> Nat -> Eff m '[RND] Nat
rndNat_ lower upper = do v <- effect SHere SGetRandom
                         return (v `mod` (upper - lower) + lower)

rndNat :: forall xs prf m.
          SingI (prf :: SubList '[RND] xs)
       => Nat -> Nat -> EffM m xs (UpdateWith '[RND] xs prf) Nat
rndNat lower upper = lift @_ @_ @prf (rndNat_ lower upper)

srand_ :: Nat -> Eff m '[RND] ()
srand_ n = case toSing n of SomeSing n' -> effect SHere (SSetSeed n')

srand :: forall xs prf m.
         SingI (prf :: SubList '[RND] xs)
      => Nat -> EffM m xs (UpdateWith '[RND] xs prf) ()
srand n = lift @_ @_ @prf (srand_ n)
