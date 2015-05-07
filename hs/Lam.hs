{-# LANGUAGE TypeOperators, EmptyCase, DataKinds, PolyKinds, TypeFamilies,
             GADTs #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Lam where

import Prelude ()
import Data.Proxy

data Ty :: * where
  Unit  :: Ty
  (:~>) :: Ty -> Ty -> Ty
infixr 0 :~>

data Elem :: [a] -> a -> * where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

data Expr :: [Ty] -> Ty -> * where
  Var :: Elem ctx ty -> Expr ctx ty
  Lam :: Expr (arg ': ctx) res -> Expr ctx (arg ':~> res)
  App :: Expr ctx (arg ':~> res) -> Expr ctx arg -> Expr ctx res
  TT  :: Expr ctx 'Unit

id :: Expr '[] ('Unit ':~> 'Unit)
id = Lam (Var EZ)

type Bool x = x ':~> x ':~> x

tru :: Expr '[] (Bool x)
tru = Lam (Lam (Var (ES EZ)))

fls :: Expr '[] (Bool x)
fls = Lam (Lam (Var EZ))

iff :: Expr '[] (Bool x ':~> x ':~> x ':~> x)
iff = Lam (Lam (Lam (App (App (Var (ES (ES EZ))) (Var (ES EZ))) (Var EZ))))

infixr 5 ++
type family xs ++ ys where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

data LengthEv :: [a] -> * where
  LEZ :: LengthEv '[]
  LES :: LengthEv xs -> LengthEv (x ': xs)

shiftElem :: Proxy y -> Proxy xs2 -> LengthEv xs1
          -> Elem (xs1 ++ xs2) x -> Elem (xs1 ++ y ': xs2) x
shiftElem _ _ LEZ e = ES e
shiftElem _ _ (LES _) EZ = EZ
shiftElem p1 p2 (LES l) (ES e) = ES (shiftElem p1 p2 l e)

shift :: Proxy x -> Proxy ts2 -> LengthEv ts1
      -> Expr (ts1 ++ ts2) ty -> Expr (ts1 ++ x ': ts2) ty
shift p1 p2 len (Var v)    = Var (shiftElem p1 p2 len v)
shift p1 p2 len (Lam body) = Lam (shift p1 p2 (LES len) body)
shift p1 p2 len (App e1 e2) = App (shift p1 p2 len e1) (shift p1 p2 len e2)
shift _ _ _ TT = TT

substVar :: LengthEv ts1 -> Expr ts2 s -> Elem (ts1 ++ s ': ts2) t -> Expr (ts1 ++ ts2) t
substVar LEZ e EZ = e
substVar LEZ _ (ES v) = Var v
substVar (LES _) _ EZ = Var EZ
substVar (LES len) e (ES v) = shift Proxy Proxy LEZ (substVar len e v)

subst :: LengthEv ts1 -> Expr ts2 s -> Expr (ts1 ++ s ': ts2) t -> Expr (ts1 ++ ts2) t
subst len e (Var v) = substVar len e v
subst len e (Lam body) = Lam (subst (LES len) e body)
subst len e (App e1 e2) = App (subst len e e1) (subst len e e2)
subst _ _ TT = TT

data Val :: [Ty] -> Ty -> * where
  TTVal  :: Val ctx 'Unit
  LamVal :: Expr (arg ': ctx) res -> Val ctx (arg ':~> res)

apply :: Val ctx (arg ':~> res) -> Expr ctx arg -> Expr ctx res
apply (LamVal body) arg = subst LEZ arg body

data Either a b = Left a | Right b

step :: Expr '[] t -> Either (Expr '[] t) (Val '[] t)
step (Var v) = case v of {}
step (Lam body) = Right (LamVal body)
step (App fun arg) = case step fun of
  Left fun' -> Left (App fun' arg)
  Right (LamVal body) -> Left (subst LEZ arg body)
step TT = Right TTVal

eval' :: Expr '[] t -> Val '[] t
eval' expr = case step expr of
  Left expr' -> eval' expr'
  Right val  -> val
