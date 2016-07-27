module Effects where

open import Data.List
open import Level

Effect : Set₁
Effect = Set → Set → Set → Set

data EFFECT : Set₁ where
  MkEff : Set → Effect → EFFECT

data SubList {ℓ : Level} {a : Set ℓ} : List a → List a → Set where
  SubNil : SubList [] []
  Keep   : ∀ {x xs ys} → SubList xs ys → SubList (x ∷ xs) (x ∷ ys)
  Drop   : ∀ {x xs ys} → SubList xs ys → SubList xs       (x ∷ ys)

data Env : (Set → Set) → List EFFECT → Set where
  Empty : ∀ {m} → Env m []
  _:::_ : ∀ {a m xs eff} → a → Env m xs → Env m (MkEff a eff ∷ xs)

updateWith : ∀ {ℓ : Level} {a : Set ℓ} {ys}
           → List a → (xs : List a) → SubList ys xs → List a
updateWith ys       (x ∷ xs) (Drop rest) = x ∷ updateWith ys xs rest
updateWith (y ∷ ys) (_ ∷ xs) (Keep rest) = y ∷ updateWith ys xs rest
updateWith []       []       SubNil      = []
updateWith (y ∷ ys) []       SubNil      = y ∷ ys
updateWith []       (_ ∷ _)  (Keep _)    = []

rebuildEnv : ∀ {m xs ys ys'} → Env m ys' → (prf : SubList ys xs) → Env m xs
           → Env m (updateWith ys' xs prf)
rebuildEnv Empty SubNil env = env
rebuildEnv (x ::: xs) (Keep rest) (_ ::: env) = x ::: rebuildEnv xs rest env
rebuildEnv xs (Drop rest) (y ::: env) = y ::: rebuildEnv xs rest env
rebuildEnv (x ::: xs) SubNil Empty = x ::: xs
rebuildEnv Empty (Keep _) _ = Empty
