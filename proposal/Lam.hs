{-# LANGUAGE PolyKinds, DataKinds, TypeOperators, GADTs #-}

module Lam where

-- Simple λ-calculus interpreter. For fuller example with similar
-- ideas, see my package `glambda` at hackage.haskell.org/package/glambda

data Ty :: * where
  Unit  :: Ty
  (:~>) :: Ty -> Ty -> Ty
infixr 0 :~>

-- `Elem xs x` is evidence that `x` is in the list `xs`.
data Elem :: [a] -> a -> * where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

-- `Expr ctx ty` is a well-typed expression, of type `ty`, in a context `ctx`
-- If (e :: Expr ctx ty), then (ctx |- e : ty)
data Expr :: [Ty] -> Ty -> * where
  Var :: Elem ctx ty -> Expr ctx ty
  Lam :: pi arg. forall ctx res.
         Expr (arg ': ctx) res -> Expr ctx (arg ':~> res)
  App :: Expr ctx (arg ':~> res) -> Expr ctx arg -> Expr ctx res
  TT  :: Expr ctx 'Unit

-- `Val ty` is a well-typed value of type `ty` in an empty context
-- If (v :: Val ty), then (empty |- v : ty)
data Val :: Ty -> * where
  LamVal :: Expr '[arg] res -> Val (arg ':~> res)
  TTVal  :: Val 'Unit

-- de Bruijn index shifting... or weakening.
shift :: forall ctx ty x. Expr ctx ty -> Expr (x ': ctx) ty
shift = go []
  where
    go :: forall ty.
          pi (ctx0 :: [Ty]) ->
          Expr (ctx0 '++ ctx) ty ->
          Expr (ctx0 '++ x ': ctx) ty
    go ctx0 (Var v)         = Var (shift_elem ctx0 v)
    go ctx0 (Lam @arg body) = Lam (go (arg : ctx0) body)
    go ctx0 (App e1 e2)     = App (go ctx0 e1) (go ctx0 e2)
    go _    TT              = TT

    shift_elem :: pi (ctx0 :: [Ty]) ->
                  Elem (ctx0 '++ ctx) y ->
                  Elem (ctx0 '++ x ': ctx) y
    shift_elem []       e      = ES e
    shift_elem (_:_)    EZ     = EZ
    shift_elem (_:tys)) (ES e) = ES (shift_elem tys e)

-- Substitution operation... or substitution lemma
subst :: forall ctx s ty. Expr ctx s -> Expr (s ': ctx) ty -> Expr ctx ty
subst e = go []
  where
    go :: forall ty.
          pi (ctx0 :: [Ty]) ->
          Expr (ctx0 '++ s ': ctx) ty ->
          Expr (ctx0 '++ ctx) ty
    go ctx0 (Var v)         = subst_var ctx0 v
    go ctx0 (Lam @arg body) = Lam (go (arg : ctx0) body)
    go ctx0 (App e1 e2)     = App (go ctx0 e1) (go ctx0 e2)
    go _    TT              = TT

    subst_var :: forall ty.
                 pi ctx0 ->
                 Elem (ctx0 '++ s ': ctx) t ->
                 Expr (ctx0 '++ ctx) t
    subst_var []      EZ     = e
    subst_var []      (ES v) = Var v
    subst_var (_:_)   EZ     = Var EZ
    subst_var (_:tys) (ES v) = shift (subst_var tys v)

apply :: Val (arg ':~> res) -> Expr '[] arg -> Expr '[] res
apply (LamVal body) arg = subst arg body

eval :: Expr '[] ty -> Val ty
eval (Var v)     = case v of {}
eval (Lam body)  = LamVal body
eval (App e1 e2) = eval (apply (eval e1) e2)
eval TT          = TTVal

data StepResult :: Expr '[] ty -> * where
  Stepped :: pi (e' :: Expr '[] ty) -> ('eval e ~ 'eval e') => StepResult e
  Value   :: pi (v  :: Val      ty) -> ('eval e ~ v)        => StepResult e

step :: pi (e :: Expr '[] ty) -> StepResult e
step (Var v)     = case v of {}
step (Lam body)  = Value (LamVal body)
step (App e1 e2) = case step e1 of
  Stepped e1' -> Stepped (App e1' e2)
    -- must have (eval (App e1 e2) ~ eval (App e1' e2))
    -- assumption: eval e1 ~ eval e1'
  Value v     -> Stepped (apply v e2)
    -- must have (eval (App e1 e2) ~ eval (apply v e2))
    -- assumption: eval e1 ~ v
step TT          = Value TTVal
