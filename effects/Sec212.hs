-- Adapted from Brady's ICFP '13 paper.

{-# LANGUAGE TypeInType, RebindableSyntax, TypeOperators,
             TemplateHaskell, ScopedTypeVariables, TypeFamilies,
             GADTs #-}

module Sec212 where

import Sec211
import Effects
import Effect.State
import Data.Nat
import qualified Prelude as P
import Data.Singletons.Prelude
import Data.Singletons.TH

$(singletons [d| data Vars = Count | Tag |])

tagCount :: Tree a -> Eff m '[ Tag   ::: STATE Nat
                             , Count ::: STATE Nat ] (Tree (Nat, a))
tagCount Leaf
  = do SCount |- update_ (+1)
       return Leaf
tagCount (Node l x r)
  = do l' <- tagCount l
       lbl <- STag |- get_
       STag |- put_ (lbl + 1)
       r' <- tagCount r
       return (Node l' (lbl, x) r')

tagCountFrom :: Nat -> Tree a -> (Nat, Tree (Nat, a))
tagCountFrom x t
  = let (_ :> SCount := leaves :> Empty, tree) =
          runPureEnv (STag := x :> SCount := 0 :> Empty) (tagCount t)
    in
    (leaves, tree)
