{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

-- Richard's "Pyrotechnic" version of Conor's file

module Part5 where

import Prelude ( Bool(..), undefined, return )
import GHC.TypeLits ( type (-) )
import Data.Type.Equality
import GHC.Exts
import Data.Type.Bool
import Data.Proxy

import Singletons

data instance Sing (t :: *) where
  SNat  :: Sing Nat
  SBool :: Sing Bool


data TyFun :: * -> * -> *
type a ~> b = TyFun a b -> *

data Expr :: * -> * where
  Val  :: t -> Expr t
  Plus :: Expr Nat -> Expr Nat -> Expr Nat
  If   :: Expr Bool -> Expr t -> Expr t -> Expr t

data instance Sing (e :: Expr t) where
  SVal  :: Sing t -> Sing ('Val t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b)
  SIf   :: Sing b -> Sing t -> Sing f -> Sing ('If b t f)

type SExpr (e :: Expr t) = Sing e

eval :: Expr t -> t
eval (Val n)        = n
eval (e1 `Plus` e2) = eval e1 + eval e2
eval (If e0 e1 e2)  = if eval e0 then eval e1 else eval e2

type family Eval (x :: Expr t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 :+ Eval e2
  Eval ('If e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

sEval :: SExpr e -> Sing (Eval e)
sEval (SVal n) = n
sEval (e1 `SPlus` e2) = sEval e1 %:+ sEval e2
sEval (SIf e0 e1 e2) = sIf (sEval e0) (sEval e1) (sEval e2)

type family U n where
  U 0 = 'Zero
  U n = 'Succ (U (n-1))

type Rel i = i -> i -> *

data List (x :: Rel i) :: Rel i where
  Nil   :: List x i i
  (:::) :: x i j -> List x j k -> List x i k
infixr 5 :::

(++) :: List x i j -> List x j k -> List x i k
Nil ++ ys = ys
(x ::: xs) ++ ys = x ::: (xs ++ ys)
infixr 5 ++

type SC = [*]

data Elt :: Rel SC where
  E :: t -> Elt (t ': ts) ts

type Stk i = List Elt i '[]

data StkSym0 :: SC ~> *
type family (f :: a ~> b) @@ (x :: a) :: b
type instance StkSym0 @@ x = Stk x


$(return [])

type family SingletonCtor (x :: k) :: Sing x
type instance SingletonCtor Nat = 'SNat
type instance SingletonCtor Bool = 'SBool

data instance Sing (a :: Sing b) where
  Sing :: Sing (SingletonCtor x)

data Sg (s :: *) (t :: s ~> *) :: * where
  (:&) :: forall (s :: *) (t :: s ~> *) (fst :: s).
          Sing (fst :: s) -> t @@ fst -> Sg s t

data Inst :: Rel (Sg SC StkSym0) where
  PUSH :: forall (t :: *) (st :: Sing t) (ts :: [*]) (sts :: Sing ts)
                 (v :: t) (vs :: Stk ts).
          Sing v -> Inst (sts ':& vs) ((st '`SCons` sts) ':& ('E v '::: vs))

  ADD  :: forall (ts :: [*]) (sts :: Sing ts) (y :: Nat) (x :: Nat) (vs :: Stk ts).
          Inst (('SNat '`SCons` 'SNat '`SCons` sts) ':& ('E y '::: 'E x '::: vs))
               (('SNat '`SCons` sts) ':& ('E (x :+ y) '::: vs))

  IFPOP :: List Inst (sts ':& vs) (sts' ':& vst)
        -> List Inst (sts ':& vs) (sts' ':& vsf)
        -> Inst (('SBool '`SCons` sts) ':& ('E b '::: vs))
                (sts' ':& If b vst vsf)

fact :: forall (ty :: *)
               (sc :: SC) (b :: Bool) (t :: ty) (f :: ty) (s :: Stk sc).
        Sing b -> Sing t -> Sing f -> Proxy s
     -> ('E (If b t f) '::: s) :~: (If b ('E t '::: s) ('E f '::: s))
fact STrue  _ _ _ = Refl
fact SFalse _ _ _ = Refl

compile :: forall (t :: *) (st :: Sing t) (e :: Expr t) (ts :: [*]) (sts :: Sing ts)
                  (vs :: Stk ts).
           Sing e -> Sing st -> List Inst (sts ':& vs) ((st '`SCons` sts) ':& ('E (Eval e) '::: vs))
compile (SVal y)        _ = PUSH y ::: Nil
compile (e1 `SPlus` e2) Sing = compile e1 Sing ++ compile e2 Sing ++ ADD ::: Nil
compile (SIf e0 e1 e2)  ev = case fact (sEval e0) (sEval e1) (sEval e2) (Proxy :: Proxy vs) of
  Refl -> compile e0 Sing ++ IFPOP (compile e1 ev) (compile e2 ev) ::: Nil
