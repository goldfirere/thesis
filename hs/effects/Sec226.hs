-- Adapted from Brady's ICFP 2013 paper.

{-# LANGUAGE TypeInType, RebindableSyntax #-}

module Sec226 where

import Effects
import Effect.Select
import qualified Prelude as P
import Data.Nat
import Prelude ( Bool(..), abs, (&&), (/=), all, (==), Maybe(..) )

no_attack :: (Nat, Nat) -> (Nat, Nat) -> Bool
no_attack (x, y) (x', y')
  = x /= x' && y /= y' && abs (xi P.- xi') /= abs (yi P.- yi')
  where
    xi  = toInteger x
    xi' = toInteger x'
    yi  = toInteger y
    yi' = toInteger y'

rowsIn :: Nat -> [(Nat, Nat)] -> [Nat]
rowsIn col qs
  = [ x | x <- [1..8], all (no_attack (x, col)) qs ]

addQueens :: Nat -> [(Nat, Nat)] -> Eff m '[SELECT] [(Nat, Nat)]
addQueens 0 qs = return qs
addQueens col qs
  = do row <- select (rowsIn col qs)
       addQueens (col - 1) ((row, col) : qs)

getQueens :: Maybe [(Nat, Nat)]
getQueens = run (() :> Empty) (addQueens 8 [])

allQueens :: [[(Nat, Nat)]]
allQueens = run (() :> Empty) (addQueens 8 [])
