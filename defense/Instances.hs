{-# LANGUAGE RankNTypes, TypeApplications, GADTs #-}

module Instances where

import Basics

-- Finds Read and Show instances for the example
getReadShowInstances :: TypeRep a
                     -> ((Show a, Read a) => r)
                     -> r
getReadShowInstances tr thing
  | Just HRefl <- eqT tr (typeRep @Int) = thing
  | Just HRefl <- eqT tr (typeRep @Bool) = thing
  | Just HRefl <- eqT tr (typeRep @Char) = thing

  | TyApp list_rep elt_rep <- tr
  , Just HRefl <- eqT list_rep (typeRep @[])
  = getReadShowInstances elt_rep $ thing

  | otherwise = error $ "I don't know how to read or show " ++ show tr
