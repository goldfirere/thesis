{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Pico.Monad where

import Control.Monad.State

newtype PicoM a = PicoM { unPicoM :: StateT Int Maybe a }
  deriving (Functor, Applicative, Monad)

runPicoM :: PicoM a -> Maybe a
runPicoM m = evalStateT (unPicoM m) 0

getUnique :: PicoM Int
getUnique = PicoM (state $ \x -> (x, x+1))
