{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeInType, TypeFamilies,
             GADTs #-}

module Util.Singletons where

import Data.Singletons

pattern TheSing :: SingKind k => Sing (a :: k) -> DemoteRep k
pattern TheSing x <- (toSing -> SomeSing x) where
  TheSing x = fromSing x
