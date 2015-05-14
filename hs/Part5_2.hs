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


data Univ = U | K * | I

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
  SNil  :: Sing '[]
  SCons :: Sing h -> Sing t -> Sing (h ': t)
infixr 5 `SCons`

data instance Sing (a :: Bool) where
  SFalse :: Sing 'False
  STrue :: Sing 'True

-- If type family from Data.Type.Bool
sIf :: Sing a -> Sing b -> Sing c -> Sing (If a b c)
sIf SFalse _ c = c
sIf STrue  b _ = b


-- The actual start of the example

-- being Haskell, we'll index our expression type
-- by ACTUAL types. 

data Expr :: * -> * where
  Val  :: t -> Expr t
  Plus :: Expr Nat -> Expr Nat -> Expr Nat
  Cond   :: Expr Bool -> Expr t -> Expr t -> Expr t

data instance Sing (e :: Expr t) where
  SVal  :: Sing t -> Sing ('Val t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b)
  SCond   :: Sing b -> Sing t -> Sing f -> Sing ('Cond b t f)

type SExpr (e :: Expr t) = Sing e

eval :: Expr t -> t
eval (Val n)        = n
eval (e1 `Plus` e2) = eval e1 + eval e2
eval (Cond e0 e1 e2)  = if eval e0 then eval e1 else eval e2

type family Eval (x :: Expr t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 :+ Eval e2
  Eval ('Cond e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

sEval :: SExpr e -> Sing (Eval e)
sEval (SVal n) = n
sEval (e1 `SPlus` e2) = sEval e1 %:+ sEval e2
sEval (SCond e0 e1 e2) = sIf (sEval e0) (sEval e1) (sEval e2)

-- Plan: Index by final and initial stack configuration

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

-- data Elt :: Rel SC where
--  E :: t -> Elt (t ': ts) ts

-- a stack is a list of values, indexed by a list of types. 
-- basically a heterogeneous list           

data Stk (ts :: [*]) where
  StkNil  :: Stk '[]
  StkCons :: t -> Stk ts -> Stk (t ': ts)

                                 
data instance Sing (vs :: Stk ts) where
  SStkNil  :: Sing 'StkNil
  SStkCons :: Sing v -> Sing vs -> Sing ('StkCons v vs)


-- a sigma type. Second component depends on the first
-- according to some type function

data Sg (t :: s -> *) :: * where
  And :: -- forall (s :: *) (t :: s -> *) (fst :: s).
         t fst -> Sg t

type HList = Sg Stk

data Inst :: Stk ts -> Stk ts' -> *  where
  PUSH :: -- forall (t :: *) (ts :: [*]) (v :: t) (vs :: Stk ts).
          Sing v -> Inst vs ('StkCons v vs)


  ADD  :: -- forall (ts :: [*]) (y :: Nat) (x :: Nat) (vs :: Stk ts).
          Inst ('StkCons y ('StkCons x vs))
               ('StkCons (x :+ y) vs)

  IFPOP :: List Inst  ('And vs) ('And vst) 
        -> List Inst  ('And vs) ('And vsf)
        -> Inst ('StkCons b vs)
                (If b vst vsf)


fact :: -- forall (ty :: *)(sc :: SC) (b :: Bool) (t :: ty) (f :: ty) (s :: Stk sc).
        Sing b -> Proxy t -> Proxy f -> Proxy s
     -> ('StkCons (If b t f) s) :~: (If b ('StkCons t s) ('StkCons f s))
fact STrue  _ _ _ = Refl
fact SFalse _ _ _ = Refl

compile :: -- forall (t :: *) (e :: Expr t) (ts :: [*]) (vs :: Stk ts).  -- cannot remove. Need vs in proxy.
           forall t e ts vs.
           Sing e -> List Inst vs ('StkCons (Eval e) vs) 
compile (SVal y)        = PUSH y ::: Nil
compile (e1 `SPlus` e2) = compile e1 ++ compile e2 ++ ADD ::: Nil
compile (SCond se0 (se1 :: Sing e1) (se2 :: Sing e2))  =
  case fact (sEval se0) (Proxy :: Proxy (Eval e1)) (Proxy :: Proxy (Eval e2)) (Proxy :: Proxy vs) of
   Refl -> compile se0 ++ IFPOP (compile se1) (compile se2) ::: Nil


-- The run function. The type of the list of instructions tells you exactly what should happen
-- when you run the machine. Conor's stack overflow version is not as strongly typed as the one
-- below.
-- http://stackoverflow.com/questions/14288569/agda-run-function-for-conors-stack-example
   

run :: -- forall (ts :: [*]) (ts' :: [*]) (vs :: Stk ts) (vs' :: Stk ts'). 
         List Inst vs vs'  -> Sing vs -> Sing vs'
run Nil vs = vs  
run (PUSH v ::: is) vs                             = run is (SStkCons v vs)
run (ADD    ::: is) (v2 `SStkCons` (v1 `SStkCons` vs)) = run is ((v1 %:+ v2) `SStkCons` vs)
run (IFPOP is1 is2 ::: is) (STrue `SStkCons` vs)     = run is (run is1 vs)
run (IFPOP is1 is2 ::: is) (SFalse `SStkCons` vs)    = run is (run is2 vs)



