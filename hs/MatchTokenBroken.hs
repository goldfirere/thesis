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
 #-}

module Scratch where

import Data.Singletons.TH
import Data.Singletons.Prelude

$(singletons [d|
  data Nat = Zero | Succ Nat

  data T where
    MkT1 :: Nat -> T
    MkT2 :: Bool -> T
  |])

matchT :: forall (ctor :: k -> T).
          (forall (n :: k). Sing n -> Sing (ctor n))
       -> T -> Maybe (DemoteRep ('KProxy :: KProxy k))
matchT sCtor t
  = withSomeSing t $ \(st :: ST t) ->
    case (sCtor undefined, st) of
      (SMkT1 _, SMkT1 sn) -> Just (fromSing sn)
