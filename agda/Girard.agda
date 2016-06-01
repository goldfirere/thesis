-- An attempt to encode Girard's paradox in Agda, just to see what happens.

module Girard where

open import Level

P : {ℓ : Level} → Set ℓ → Set (suc ℓ)
P {ℓ} s = s → Set ℓ

Bot : {ℓ : Level} → Set (suc ℓ)
Bot {ℓ} = (p : Set ℓ) → p

Not : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Not {ℓ} p = p → Bot {ℓ}

U : {ℓ : Level} → Set (suc (suc ℓ))
U {ℓ} = (x : Set ℓ) → (P {suc ℓ} (P {ℓ} x) → x) → P {suc ℓ} (P {ℓ} x)

tau : {ℓ : Level}
    → P {suc (suc (suc ℓ))} (P {suc (suc ℓ)} (U {ℓ})) -- (U -> Set2) -> Set
    → (X : Set (suc (suc ℓ)))
    → (P {suc (suc (suc ℓ))} (P {suc (suc ℓ)} X) → X)
    → P {suc (suc ℓ)} X
    → Set (suc (suc (suc ℓ)))
tau {ℓ} t = \ (X : Set (suc (suc ℓ)))
              (f : P {suc (suc (suc ℓ))} (P {suc (suc ℓ)} X) → X)
              (p : P {suc (suc ℓ)} X)
          → t (\ (x : U {suc (suc ℓ)}) → {!p (f (x X f))!})
