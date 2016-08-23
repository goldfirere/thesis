{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeFamilies, TypeOperators,
             ConstraintKinds, StandaloneDeriving, FlexibleContexts,
             UndecidableInstances, NullaryTypeClasses, MultiParamTypeClasses,
             FlexibleInstances #-}

module UniqList where

import Data.Singletons.Prelude
import Data.Constraint
import Unsafe.Coerce
import GHC.TypeLits

instance (SingKind (KindOf a), Show (Demote a)) => Show (Sing a) where
  show x = show (fromSing x)

type a /~ b = ((a :== b) ~ False, (b :== a) ~ False)
type KindOfs (as :: [k]) = ('KProxy :: KProxy k)

type family a `NotIn` as :: Constraint where
  a `NotIn` '[]       = ()
  a `NotIn` (x ': xs) = (a /~ x, a `NotIn` xs)

data UniqList :: [k] -> * where
  Nil   :: UniqList '[]
  (:::) :: (a `NotIn` as) => Sing a -> UniqList as -> UniqList (a ': as)
infixr 5 :::
deriving instance (SingKind (KindOfs as), Show (DemoteRep (KindOfs as)))
                    => Show (UniqList as)

sZero  = sing :: Sing 0
sOne   = sing :: Sing 1
sTwo   = sing :: Sing 2
sThree = sing :: Sing 3

testList = sZero ::: sTwo ::: sOne ::: Nil

type family Snoc as a where
  Snoc '[]       a = '[a]
  Snoc (x ': xs) a = x ': (Snoc xs a)

neq_sym :: (a /~ b) => Sing a -> Sing b -> Dict (b /~ a)
neq_sym _ _ = unsafeCoerce (Dict :: Dict ())
        
snoc_proof :: (x `NotIn` xs, a /~ x)
           => Sing x -> UniqList xs -> Sing a -> Dict (x `NotIn` (Snoc xs a))
snoc_proof _ Nil        _ = Dict
snoc_proof x (_ ::: ys) a = case snoc_proof x ys a of Dict -> Dict
        
snoc :: (a `NotIn` as) => UniqList as -> Sing a -> UniqList (Snoc as a)
snoc Nil        a = a ::: Nil
snoc (x ::: xs) a = case snoc_proof x xs a of Dict -> x ::: (snoc xs a)

class (False ~ True) => Impossible

class a \/ b
instance a => a \/ b
instance b => a \/ b

type family as `Subset` as' :: Constraint where
  '[] `Subset` as' = ()
  (a ': as) `Subset` as' = (a `In` as', as `Subset` as')

type family a `In` as where
  a `In` '[] = Impossible
  a `In` (x ': xs) = (a ~ x) \/ (a `In` xs)

data UniqList2 :: [k] -> * where
  Nil2   :: UniqList2 as
  (::::) :: (a `NotIn` as) => Sing a -> UniqList2 (a ': as) -> UniqList2 as
infixr 5 ::::
deriving instance (SingKind (KindOfs as), Show (DemoteRep (KindOfs as)))
                    => Show (UniqList2 as)

testList2 :: UniqList2 ('[] :: [Nat])
testList2 = sZero :::: sOne :::: Nil2

snoc2 :: (a `NotIn` as) => UniqList2 as -> Sing a -> UniqList2 as
snoc2 Nil2 a = a :::: Nil2
snoc2 (x :::: xs) a = x :::: (snoc2 xs a)

