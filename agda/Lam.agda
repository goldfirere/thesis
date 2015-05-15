

module Lam where

open import Data.List hiding ( [_] )
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ( subst )
open import Function
open import Level using ( Level )

data Ty : Set where
  Unit : Ty
  _:~>_ : Ty → Ty → Ty
infixr 0 _:~>_

data Elem : ∀ {a : Set} → List a → a → Set1 where
  EZ : ∀ {a} {x : a} {xs : List a} → Elem (x ∷ xs) x
  ES : ∀ {a} {x y : a} {xs : List a} → Elem xs x → Elem (y ∷ xs) x

data Expr : List Ty → Ty → Set1 where
  Var : ∀ {ctx ty} → Elem ctx ty → Expr ctx ty
  Lam : ∀ {arg res ctx} → Expr (arg ∷ ctx) res → Expr ctx (arg :~> res)
  App : ∀ {arg res ctx} → Expr ctx (arg :~> res) → Expr ctx arg → Expr ctx res
  TT  : ∀ {ctx} → Expr ctx Unit

data Val : List Ty → Ty → Set1 where
  LamVal : ∀ {arg res ctx} → Expr (arg ∷ ctx) res → Val ctx (arg :~> res)
  TTVal  : ∀ {ctx} → Val ctx Unit

shift : ∀ {ctx : List Ty} {ty x : Ty} → Expr ctx ty → Expr (x ∷ ctx) ty
shift {ctx} {ty} {x} = go []
  where
    shift_elem : ∀ {y : Ty} (ctx0 : List Ty) → Elem (ctx0 ++ ctx) y → Elem (ctx0 ++ x ∷ ctx) y
    shift_elem [] e = ES e
    shift_elem (_ ∷ _) EZ = EZ
    shift_elem (_ ∷ ctx') (ES e) = ES (shift_elem ctx' e)

    go : ∀ {ty} ctx0 → Expr (ctx0 ++ ctx) ty → Expr (ctx0 ++ x ∷ ctx) ty
    go ctx0 (Var v) = Var (shift_elem ctx0 v)
    go ctx0 (Lam {arg} body) = Lam (go (arg ∷ ctx0) body)
    go ctx0 (App e1 e2) = App (go ctx0 e1) (go ctx0 e2)
    go _    TT          = TT

subst : ∀ {ctx : List Ty} {s ty : Ty} → Expr ctx s → Expr (s ∷ ctx) ty
                                                   → Expr ctx ty
subst {ctx} {s} {ty} e = go []
  where
    subst_var : ∀ {ty : Ty} (ctx0 : List Ty) → Elem (ctx0 ++ s ∷ ctx) ty
                                             → Expr (ctx0 ++ ctx) ty
    subst_var [] EZ = e
    subst_var [] (ES v) = Var v
    subst_var (_ ∷ _) EZ = Var EZ
    subst_var (_ ∷ ctx0) (ES e0) = shift (subst_var ctx0 e0)

    go : ∀ {ty : Ty} (ctx0 : List Ty) → Expr (ctx0 ++ s ∷ ctx) ty
                                      → Expr (ctx0 ++ ctx) ty
    go ctx0 (Var x) = subst_var ctx0 x
    go ctx0 (Lam {arg} body) = Lam (go (arg ∷ ctx0) body)
    go ctx0 (App e1 e2) = App (go ctx0 e1) (go ctx0 e2)
    go ctx0 TT = TT

apply : ∀ {arg res : Ty} {ctx : List Ty} → Val ctx (arg :~> res)
                                         → Expr ctx arg
                                         → Expr ctx res
apply (LamVal body) arg = subst arg body

{-# NO_TERMINATION_CHECK #-}
eval : ∀ {ty : Ty} → Expr [] ty → Val [] ty
eval (Var ())
eval (Lam {t1}{t2}{.[]} e) = LamVal {t1}{t2}{[]} e
eval (App e1 e2) = eval (apply (eval e1) e2)
eval TT = TTVal

x : ∀ { arg res e} -> eval (Lam {arg}{res} e) ≡ LamVal {arg}{res} e
x = refl

data Either : Set1 → Set1 → Set2 where
  Left : ∀ {a b} → a → Either a b
  Right : ∀ {a b} → b → Either a b

val : ∀ {ty : Ty} {ctx : List Ty} → Val ctx ty → Expr ctx ty
val (LamVal body) = Lam body
val TTVal         = TT

evalE : ∀ {ty : Ty} → Either (Expr [] ty) (Val [] ty) → Val [] ty
evalE (Left x) = eval x
evalE (Right x) = x

-- remove if in standard library
cong-app : ∀ {ℓ : Level} {a b : Set ℓ} {f g : a → b}
         → f ≡ g → (x : a) → f x ≡ g x
cong-app refl x = refl


step : ∀ {ty : Ty} → (e : Expr [] ty) → Σ (Either (Expr [] ty) (Val [] ty))
                                          (λ e' → eval e ≡ evalE e')
step (Var ())
step (Lam e) = (Right (LamVal e)) , refl
step (App e e₁) with step e
step (App e e₁) | Left x , eq = Left (App x e₁) , (let eq₁ = cong apply eq in
                                                   let eq₂ = cong-app eq₁ e₁ in
                                                   cong eval eq₂)
step (App e e₁) | Right x , eq = Left (apply x e₁) , (let eq₁ = cong apply eq in
                                                       let eq₂ = cong-app eq₁ e₁ in
                                                      cong eval eq₂)
step TT = Right TTVal , refl

data SameValue {ty : Ty} (e₁ : Expr [] ty) (e₂ : Expr [] ty) : Set1 where
  same : eval e₁ ≡ eval e₂ → SameValue e₁ e₂

step' : ∀ {ty : Ty} → (e : Expr [] ty)
      → Either (Σ (Expr [] ty) (SameValue e))
               (Σ (Val  [] ty) (_≡_ (eval e)))
step' e with step e
step' e | Left x , proj₂ = Left (x , (same proj₂))
step' e | Right x , proj₂ = Right (x , proj₂)
