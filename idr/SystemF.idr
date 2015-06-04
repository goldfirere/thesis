module SystemF

import Data.Fin
import Data.List

%default total

fpred : (f : Fin (S n)) -> (m : Nat) -> {auto pf : m `cmp` cast f = CmpLT _} -> Fin n
fpred FZ _ {pf = Refl} impossible
fpred (FS f) _ = f

data Ty : Nat -> Type where
  TVar    : Fin n -> Ty n
  TForall : Ty (S n) -> Ty n
  (:~>)   : Ty n -> Ty n -> Ty n
infixr 0 :~>

shiftTy : Ty n -> Ty (S n)
shiftTy = go 0
  where
    go : Nat -> Ty n -> Ty (S n)
    go cutoff (TVar x) = TVar (if (cutoff <= cast x) then FS x else weaken x)
    go cutoff (TForall x) = TForall (go (S cutoff) x)
    go cutoff (x :~> y) = go cutoff x :~> go cutoff y

substTy : Ty n -> Ty (S n) -> Ty n
substTy = go 0
  where
    go : Nat -> Ty n -> Ty (S n) -> Ty n
    go var inner_ty (TVar x) with (var `cmp` cast x)
      | CmpEQ = inner_ty
      | (CmpGT k) = ?s_2 -- TVar (fpred x var)
{-
data Expr : List (Ty n) -> Ty n -> Type where
  Var : Elem ty ctx -> Expr ctx ty
  Abs : Expr (arg :: ctx) res -> Expr ctx (arg :~> res)
  App : Expr ctx (arg :~> res) -> Expr ctx arg -> Expr ctx res
  TAbs : Expr (map shiftTy ctx) res -> Expr ctx (TForall res)
  TApp : Expr ctx (TForall res) -> (ty : Ty n) -> Expr ctx (substTy ty res)
-}
 
 
 
