{-# LANGUAGE GADTs, InstanceSigs, TypeOperators, TypeInType #-}

module Nat where

import Equality
import Basics ( Nat, Π )

-- instance of DEq for unary naturals
instance DEq Nat where

  eq :: Π (x :: Nat) -> Π (y :: Nat) -> Maybe (x :~: y)
  Zero   `eq` Zero   = Just Refl
  Succ _ `eq` Zero   = Nothing
  Zero   `eq` Succ _ = Nothing
  Succ n `eq` Succ m
    | Just Refl <- n `eq` m
    = Just Refl
    | otherwise
    = Nothing
