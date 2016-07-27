-- reimplementation of simple lambda-calculus interpreter.
-- July 2016.

{-# LANGUAGE TypeInType, TypeOperators, ScopedTypeVariables,
             GADTs, EmptyCase, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wunticked-promoted-constructors #-}

module Lam2 where

import Data.Kind
import Data.Singletons.Prelude ( Sing(SNil), (:++), If )
import Data.Proxy
import GHC.Exts ( Any )
import GHC.TypeLits ( TypeError, ErrorMessage(..) )

type Π = Sing

data Ty = Unit | Ty :~> Ty
infixr 0 :~>

data Elem :: [a] -> a -> Type where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

data Expr :: [Ty] -> Ty -> Type where
  Var :: Elem ctx ty -> Expr ctx ty
  Lam :: Expr (arg ': ctx) res -> Expr ctx (arg ':~> res)
  App :: Expr ctx (arg ':~> res) -> Expr ctx arg -> Expr ctx res
  TT :: Expr ctx 'Unit

data Val :: Ty -> Type where
  LamVal :: Expr '[arg] res -> Val (arg ':~> res)
  TTVal :: Val 'Unit

data Length :: [k] -> Type where
  LZ :: Length '[]
  LS :: Length xs -> Length (x ': xs)

shift :: forall ctx ty x. Expr ctx ty -> Expr (x ': ctx) ty
shift = go_shift (Proxy :: Proxy x) (Proxy :: Proxy ctx) LZ

go_shift :: forall ty ctx0 ctx x. Proxy x -> Proxy ctx -> Length ctx0 -> Expr (ctx0 :++ ctx) ty -> Expr (ctx0 :++ x ': ctx) ty
go_shift p p2 ctx0 (Var v) = Var (shift_elem p p2 ctx0 v)
go_shift p p2 ctx0 (Lam body) = Lam (go_shift p p2 (LS ctx0) body)
go_shift p p2 ctx0 (App e1 e2) = App (go_shift p p2 ctx0 e1) (go_shift p p2 ctx0 e2)
go_shift _ _ _    TT          = TT

shift_elem :: Proxy x -> Proxy ctx -> Length ctx0 -> Elem (ctx0 :++ ctx) y -> Elem (ctx0 :++ x ': ctx) y
shift_elem _ _ LZ e = ES e
shift_elem _ _ (LS _) EZ = EZ
shift_elem p p2 (LS l) (ES e) = ES (shift_elem p p2 l e)

type family IsEZ (e :: Elem xs (x :: k)) :: Bool where
  IsEZ 'EZ = 'True
  IsEZ _   = 'False

type family Shift_elem (x :: k) (ctx :: [k]) (len :: Length ctx0) (e :: Elem (ctx0 :++ ctx) y) :: Elem (ctx0 :++ x ': ctx) y where
  Shift_elem _ _ 'LZ e = 'ES e
  Shift_elem _ _ ('LS _) ez = If (IsEZ ez) 'EZ (TypeError ('Text "Shift_elem"))
--  Shift_elem _ _ ('LS l) ('ES e) = Any -- 'ES (Shift_elem x ctx l e)
{-
subst :: forall ctx s ty. Expr ctx s -> Expr (s ': ctx) ty -> Expr ctx ty
subst e = go LZ
  where
    go :: forall ctx0 ty. Length ctx0 -> Expr (ctx0 :++ s ': ctx) ty
                                      -> Expr (ctx0 :++ ctx) ty
    go len (Var v) = subst_var len v
    go len (Lam body) = Lam (go (LS len) body)
    go len (App e1 e2) = App (go len e1) (go len e2)
    go _ TT = TT

    subst_var :: forall ctx0 ty. Length ctx0 -> Elem (ctx0 :++ s ': ctx) ty
                                             -> Expr (ctx0 :++ ctx) ty
    subst_var LZ EZ = e
    subst_var LZ (ES v) = Var v
    subst_var (LS _) EZ = Var EZ
    subst_var (LS len) (ES v) = shift (subst_var len v)

apply :: Val (arg ':~> res) -> Expr '[] arg -> Expr '[] res
apply (LamVal body) arg = subst arg body

eval :: Expr '[] ty -> Val ty
eval (Var v) = case v of {}
eval (Lam body) = LamVal body
eval (App e1 e2) = eval (apply (eval e1) e2)
eval TT = TTVal
{-
data StepResult :: Expr '[] ty -> Type where
  Stepped :: (Eval e ~ Eval e') => Sing e' -> StepResult e
  Value   :: (Eval e ~ v)       => Sing v  -> StepResult e
-}
-}
