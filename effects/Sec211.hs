-- Adapted from Brady's ICFP '13 paper.

{-# LANGUAGE TypeInType, RebindableSyntax #-}

module Sec211 where

import Effects
import Effect.State
import Data.Nat
import Prelude ( Show, Ord(..), otherwise, foldl, flip )

data Tree a = Leaf
            | Node (Tree a) a (Tree a)
  deriving Show

tag :: Tree a -> Eff m '[STATE Nat] (Tree (Nat, a))
tag Leaf = return Leaf
tag (Node l x r)
  = do l' <- tag l
       lbl <- get
       put (lbl + 1)
       r' <- tag r
       return (Node l' (lbl, x) r')

tagFrom :: Nat -> Tree a -> Tree (Nat, a)
tagFrom x t = runPure (x :> Empty) (tag t)

insert :: Ord a => a -> Tree a -> Tree a
insert x Leaf = Node Leaf x Leaf
insert x (Node l x' r)
  | x < x'    = Node (insert x l) x' r
  | otherwise = Node l x' (insert x r)

inserts :: Ord a => [a] -> Tree a -> Tree a
inserts xs tree = foldl (flip insert) tree xs

tree :: Tree Nat
tree = inserts [4, 3, 8, 0, 2, 6, 7] Leaf

taggedTree :: Tree (Nat, Nat)
taggedTree = tagFrom 0 tree
