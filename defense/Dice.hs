-- Use algebraic effects to model a dice simulator.

{-# LANGUAGE RebindableSyntax, OverloadedStrings, TypeApplications, TypeInType #-}

module Dice where

import Prelude ( IO, ($), (<$>), (<*>), (++), sum, toRational, (/), Double,
                 fromIntegral, (==), Bool, otherwise )
import qualified Prelude as P
import Effects
import Effect.StdIO
import Effect.Random
import Effect.State
import Data.AChar
import Data.Nat

count :: (a -> Bool) -> [a] -> Nat
count _ [] = 0
count f (x : xs)
  | f x       = 1 + count f xs
  | otherwise = count f xs

replicateE :: Nat -> Eff m xs a -> Eff m xs [a]
replicateE Z _     = return []
replicateE (S n) e = (:) <$> e <*> replicateE n e

main :: IO ()
main = run @'[STDIO, RND] starting_env $ do
  putStr "How many dice will you simulate? "
  numDice <- read <$> getStr
  putStr "How many trials? "
  numTrials <- read <$> getStr
  results <- replicateE numTrials (lift $ throwDice numDice)
  putStrLn $ "Mean value: " ++ show @Double (fromIntegral (sum results) /
                                             fromIntegral numTrials)
  putStrLn $ "Results: " ++ show results
  where
    starting_env = () :> 31 :> Empty

throwDice :: Nat -> Eff m '[RND] Nat
throwDice n = do
  rolls <- replicateE n (rndNat 1 7)  -- upper bound is *exclusive*
  putStrLn (show rolls)
  return (sum rolls)
