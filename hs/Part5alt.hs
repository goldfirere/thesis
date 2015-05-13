{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Part5 where

import Prelude ( Bool(..), undefined, return )
import GHC.TypeLits ( type (-) )
import Data.Type.Equality
import GHC.Exts
import Data.Type.Bool
import Data.Proxy

-- standard definition of natural numbers and their
-- singletons
data Nat :: * where
  Zero :: Nat
  Succ :: Nat -> Nat

data family Sing (a :: k)

data instance Sing (n :: Nat) where
  SZero :: Sing 'Zero
  SSucc :: Sing n -> Sing ('Succ n)

data instance Sing (t :: *) where
  SNat  :: Sing Nat
  SBool :: Sing Bool

(+) :: Nat -> Nat -> Nat
Zero   + m = m
Succ n + m = Succ (n + m)
infixl 6 +

type family a :+ b where
  'Zero :+ m = m
  'Succ n :+ m = 'Succ (n :+ m)

(%:+) :: Sing a -> Sing b -> Sing (a :+ b)
SZero %:+ m = m
SSucc n %:+ m = SSucc (n %:+ m)

-- standard singletons for lists and booleans
data instance Sing (a :: [k]) where
  SNil :: Sing '[]
  SCons :: Sing h -> Sing t -> Sing (h ': t)
infixr 5 `SCons`

data instance Sing (a :: Bool) where
  SFalse :: Sing 'False
  STrue :: Sing 'True

sIf :: Sing a -> Sing b -> Sing c -> Sing (If a b c)
sIf SFalse _ c = c
sIf STrue  b _ = b


-- The actual start of the example

-- being Haskell, we'll index our expression type
-- by ACTUAL types. 

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

-- Plan: Index by final and initial stack configuration

type Rel i = i -> i -> *

data List (x :: Rel i) :: Rel i where
  Nil   :: List x i i
  (:::) :: x i j -> List x k j -> List x k i
infixr 5 :::

(++) :: List x j i -> List x k j -> List x k i 
Nil ++ ys = ys
(x ::: xs) ++ ys = x ::: (xs ++ ys)
infixr 5 ++

type SC = [*]

data Elt :: Rel SC where
  E :: t -> Elt (t ': ts) ts

-- note that this is not a real type-level lambda
                 
type Stk = List Elt '[] 


-- a sigma type. Second component depends on the first
-- according to some type function

data Sg (s :: *) (t :: s -> *) :: * where
  And :: forall (s :: *) (t :: s -> *) (fst :: s).
          t fst -> Sg s t

data Inst :: Rel (Sg SC Stk) where
  PUSH :: forall (t :: *) (ts :: [*]) 
                 (v :: t) (vs :: Stk ts).
          Sing v -> Inst ('And vs) ('And ('E v '::: vs))


  ADD  :: forall (ts :: [*]) (y :: Nat) (x :: Nat) (vs :: Stk ts).
          Inst ('And ('E y '::: 'E x '::: vs))
               ('And ('E (x :+ y) '::: vs))

  IFPOP :: List Inst ('And vst) ('And vs) 
        -> List Inst ('And vsf) ('And vs) 
        -> Inst ('And ('E b '::: vs))
                ('And (If b vst vsf))

fact :: forall (ty :: *)
               (sc :: SC) (b :: Bool) (t :: ty) (f :: ty) (s :: Stk sc).
        Sing b -> Sing t -> Sing f -> Proxy s
     -> ('E (If b t f) '::: s) :~: (If b ('E t '::: s) ('E f '::: s))
fact STrue  _ _ _ = Refl
fact SFalse _ _ _ = Refl

compile :: forall (t :: *) 
           (e :: Expr t)
           (ts :: [*]) (vs :: Stk ts).
           Sing e -> 
           List Inst  ('And ('E (Eval e) '::: vs)) ('And vs)
compile (SVal y)        = PUSH y ::: Nil
compile (e1 `SPlus` e2) = compile e1 ++ compile e2 ++ ADD ::: Nil
compile (SIf e0 e1 e2)  = case fact (sEval e0) (sEval e1) (sEval e2) (Proxy :: Proxy vs) of
  Refl -> compile e0 ++ IFPOP (compile e1) (compile e2) ::: Nil

