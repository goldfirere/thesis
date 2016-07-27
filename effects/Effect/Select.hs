-- adapted from Idris's algebraic effects library

{-# LANGUAGE TypeInType, GADTs, TypeFamilies, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes #-}

module Effect.Select where

import Effects
import Data.Singletons
import Data.Kind

data Selection :: Type -> Type -> Type -> Type where
  Select :: [a] -> Selection () () a

data instance Sing (x :: Selection a b c) where
  SSelect :: Sing xs -> Sing (Select xs)

instance (Good a, Good b, Good c) => SingKind (Selection a b c) where
  type DemoteRep (Selection a b c) = Selection a b c

  fromSing (SSelect xs) = Select (fromSing xs)

  toSing (Select xs) = case toSing xs of SomeSing xs' -> SomeSing (SSelect xs')

instance Handler (TyCon3 Selection) (TyCon1 Maybe) where
  handle (Select xs) _ k = tryAll xs where
    tryAll [] = Nothing
    tryAll (x : xs) = case k () x of
                        Nothing -> tryAll xs
                        Just v  -> Just v

instance Handler (TyCon3 Selection) (TyCon1 []) where
  handle (Select xs) r k = concatMap (k r) xs

type SELECT = MkEff () (TyCon3 Selection)

select_ :: Good a => [a] -> Eff m '[SELECT] a
select_ xs = case toSing xs of SomeSing xs' -> effect SHere (SSelect xs')

select :: forall xs prf a m.
          (SingI (prf :: SubList '[SELECT] xs), Good a)
       => [a] -> EffM m xs (UpdateWith '[SELECT] xs prf) a
select xs = lift @_ @_ @prf (select_ xs)
