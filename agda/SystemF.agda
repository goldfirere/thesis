
module SystemF where

open import Data.List
open import Data.Nat
open import Data.Fin as Fin hiding ( compare )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Level using ( Level )

data _∈_ {ℓ : Level} {A : Set ℓ} : A → List A → Set ℓ where
  EZ : ∀ {x xs} → x ∈ (x ∷ xs)
  ES : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

data Ty (n : ℕ) : Set where
  TVar : Fin n → Ty n
  TForall : Ty (suc n) → Ty n
  _:~>_ : Ty n → Ty n → Ty n
infixr 0 _:~>_

data _⇒_ : ℕ → ℕ → Set where
  zero : ∀ {n₁} → n₁ ⇒ suc n₁
  suc  : ∀ {n₁ n₂} → n₁ ⇒ n₂ → (suc n₁) ⇒ (suc n₂)

tshift : ∀ {n} → Ty n → Ty (suc n)
tshift ty = go zero ty
  where
    goVar : ∀ {n₁ n₂} → (n₁ ⇒ n₂) → Fin n₁ → Fin n₂
    goVar zero v               = suc v
    goVar (suc cutoff) zero    = zero
    goVar (suc cutoff) (suc v) = suc (goVar cutoff v)

    go : ∀ {n₁ n₂} → (n₁ ⇒ n₂) → Ty n₁ → Ty n₂
    go cutoff (TVar x) = TVar (goVar cutoff x)
    go cutoff (TForall ty) = TForall (go (suc cutoff) ty)
    go cutoff (ty :~> ty₁) = go cutoff ty :~> go cutoff ty₁

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

tsubst : ∀ {n} → Ty n → Ty (suc n) → Ty n
tsubst {n} ty = go zero
  where
    substVar : ∀ {n} → Ty n → Fin (suc n) → Fin (suc n) → Ty n
    substVar     ty zero zero = ty
    substVar     _  zero (suc f) = TVar f
    substVar {n} _  (suc var) zero with n
    substVar {n} _  (suc var) zero | zero = ⊥-elim (¬Fin0 var)
    substVar {n} _  (suc var) zero | suc n' = TVar zero
    substVar {n} ty (suc var) (suc f) with n
    substVar ty₁ (suc var) (suc f) | zero = ⊥-elim (¬Fin0 var)
    substVar ty₁ (suc var) (suc f) | suc n' = tshift (substVar {!!} {!!} {!!})

    go : Fin (suc n) → Ty (suc n) → Ty n
    go var (TVar x) = substVar ty var x
{-    go var (TVar x) with (var ≤? toℕ x)
    go var (TVar x) | yes p with (var ≟ toℕ x)
    go var (TVar x) | yes p₁ | yes p = ty
    go zero (TVar zero) | yes p | no ¬p = ⊥-elim (¬p refl)
    go zero (TVar (suc x')) | yes p | no ¬p = TVar x'
    go (suc var') (TVar x) | yes p | no ¬p = TVar (reduce≥ {m = 1} x {!!})
    go var (TVar x) | no ¬p = {!!}
-}
    go var (TForall ty₁) = {!!}
    go var (ty₁ :~> ty₂) = {!!}

data Expr {n : ℕ} (ctx : List (Ty n)) : Ty n → Set where
  Var : ∀ {ty : Ty n} → ty ∈ ctx → Expr ctx ty
  Lam : ∀ {arg res} → Expr (arg ∷ ctx) res → Expr ctx (arg :~> res)
  App : ∀ {arg res} → Expr ctx (arg :~> res) → Expr ctx arg → Expr ctx res
  TLam : ∀ {res} → Expr (map tshift ctx) res → Expr ctx (TForall res)
  TApp : ∀ {res} → Expr ctx (TForall res) → (ty : Ty n) → Expr ctx (tsubst ty res)
