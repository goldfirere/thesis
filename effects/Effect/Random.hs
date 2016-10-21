-- Adapted from Idris's algebraic effects library

{-# LANGUAGE TypeInType, RebindableSyntax, GADTs, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies, ScopedTypeVariables,
             TypeApplications, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Effect.Random where

import qualified Prelude as P
import Data.Nat
import Effects
import Data.Singletons
import qualified System.Random as R

data Random :: Effect where
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

-- top-level definition so that it is computed only once
modulus :: P.Int
modulus = P.fromIntegral 1007

instance Handler Random m where
  handle GetRandom seed k
    = let gen = R.mkStdGen (P.fromIntegral seed)
          (n, _) = R.random @P.Int gen
          seed' = fromInteger (P.fromIntegral (n `P.mod` modulus)) in
      k seed' seed'
  handle (SetSeed n) _ k = k n ()

type RND = MkEff Nat Random

rndNat_ :: Nat -> Nat -> Eff m '[RND] Nat
rndNat_ lower upper = do v <- Effect SHere SGetRandom
                         return (v `mod` (upper - lower) + lower)

rndNat :: forall xs prf m.
          SingI (prf :: SubList '[RND] xs)
       => Nat -> Nat -> EffM m xs (UpdateWith '[RND] xs prf) Nat
rndNat lower upper = lift @_ @_ @prf (rndNat_ lower upper)

srand_ :: Nat -> Eff m '[RND] ()
srand_ n = case toSing n of SomeSing n' -> Effect SHere (SSetSeed n')

srand :: forall xs prf m.
         SingI (prf :: SubList '[RND] xs)
      => Nat -> EffM m xs (UpdateWith '[RND] xs prf) ()
srand n = lift @_ @_ @prf (srand_ n)
