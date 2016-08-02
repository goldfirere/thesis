module Irrel where

open import Data.Nat
open import Level

data T : Set where
  mkT : .(n : ℕ) → T
data S : T → Set where
  mkS : .(n : ℕ) → S (mkT n)

x : S (mkT 3)
x = mkS 3

y : S (mkT 4)
y = x
