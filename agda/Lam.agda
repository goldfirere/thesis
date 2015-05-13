module Lam where

open import Data.List
open import Data.Product
open import Relation.Binary.HeterogeneousEquality using ( _≅_; refl )

data Ty : Set where
  Unit : Ty
  _:~>_ : Ty → Ty → Ty
infixr 0 _:~>_

data Elem : ∀ {a} → List a → a → Set1 where
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

eval : ∀ {ty : Ty} → Expr [] ty → Val [] ty
eval (Var ())
eval (Lam e) = LamVal e
eval (App e1 e2) = eval (apply (eval e1) e2)
eval TT = TTVal

data Either : Set1 → Set1 → Set2 where
  Left : ∀ {a b} → a → Either a b
  Right : ∀ {a b} → b → Either a b

val : ∀ {ty : Ty} {ctx : List Ty} → Val ctx ty → Expr ctx ty
val (LamVal body) = Lam body
val TTVal         = TT

evalE : ∀ {ty : Ty} → Either (Expr [] ty) (Val [] ty) → Val [] ty
evalE (Left x) = eval x
evalE (Right x) = eval (val x)

step : ∀ {ty : Ty} → (e : Expr [] ty) → Σ (Either (Expr [] ty) (Val [] ty))
                                          (λ e' → eval e ≅ evalE e')
step (Var ())
step (Lam e) = (Right (LamVal e)) , refl
step (App e e₁) with step e
step (App e e₁) | Left x , refl = {!!} -- (Left (App x e₁)) , {!!}
step (App e e₁) | Right x , proj₂ = {!!}
step TT = {!!}
