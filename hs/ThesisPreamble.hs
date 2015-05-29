{-# LANGUAGE TypeOperators, DataKinds, PolyKinds, TypeFamilies #-}

module ThesisPreamble ( FromNat ) where

import GHC.TypeLits

type family FromNat (n :: Nat) :: k
