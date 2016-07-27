-- Using singletons, etc., to do a "matchable" thing.

{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, DataKinds,
             PolyKinds, GADTs, RankNTypes, MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances,
             FunctionalDependencies, StandaloneDeriving,
             TypeOperators, ScopedTypeVariables, NoMonomorphismRestriction,
             MonadComprehensions, DeriveGeneric, FlexibleContexts,
             GeneralizedNewtypeDeriving, ConstraintKinds,
             LambdaCase, ViewPatterns, -- AllowAmbiguousTypes,
             DefaultSignatures, -- ImpredicativeTypes,
             ImplicitParams, MagicHash, UnboxedTuples,
             ExtendedDefaultRules, PatternSynonyms, EmptyCase,
             DeriveFunctor, OverloadedLists -- , OverlappingInstances,
             -- NullaryTypeClasses
             , TypeInType
 #-}

module Scratch where

data Nat = Zero | Succ Nat
  deriving Show

data T where
  MkT1 :: Nat -> T
  MkT2 :: Bool -> T

data family Sing (a :: k)
data instance Sing (a :: Nat) where
  SZero :: Sing Zero
  SSucc :: Sing n -> Sing (Succ n)

data instance Sing (a :: Bool) where
  SFalse :: Sing False
  STrue  :: Sing True

data instance Sing (a :: T) where
  SMkT1 :: Sing n -> Sing (MkT1 n)
  SMkT2 :: Sing n -> Sing (MkT2 n)

class SingKind k where
  withSomeSing :: k -> (forall (a :: k). Sing a -> r) -> r
  fromSing :: Sing (a :: k) -> k

instance SingKind Nat where
  withSomeSing Zero f = f SZero
  withSomeSing (Succ n) f = withSomeSing n $ \sn -> f (SSucc sn)
  fromSing SZero = Zero
  fromSing (SSucc n) = Succ (fromSing n)

instance SingKind Bool where
  withSomeSing False f = f SFalse
  withSomeSing True f = f STrue
  fromSing SFalse = False
  fromSing STrue = True

instance SingKind T where
  withSomeSing (MkT1 n) f = withSomeSing n $ \sn -> f (SMkT1 sn)
  withSomeSing (MkT2 n) f = withSomeSing n $ \sn -> f (SMkT2 sn)
  fromSing (SMkT1 n) = MkT1 (fromSing n)
  fromSing (SMkT2 n) = MkT2 (fromSing n)

matchT :: forall (ctor :: k -> T).
          (forall (n :: k). Sing n -> Sing (ctor n))
       -> T -> Maybe k
matchT sCtor t
  = withSomeSing t $ \st ->
    case (sCtor undefined, st) of
      (SMkT1 _, SMkT1 sn) -> Just (fromSing sn)
      (SMkT2 _, SMkT2 sn) -> Just (fromSing sn)
      _                   -> Nothing

{-
matchT :: forall a. (a -> T) -> T -> Maybe a
matchT ctor t
  = case (ctor undefined, t) of
      (MkT1 _, MkT1 n) -> Just n
      (MkT2 _, MkT2 n) -> Just n
      _                -> Nothing
-}
