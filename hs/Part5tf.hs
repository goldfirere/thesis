{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

-- Stephanie's version: uses the type families and proxies in the Sigma to keep the list arguments in the
-- correct order.

module Part5 where

import Prelude ( Bool(..), undefined, return )
import GHC.TypeLits ( type (-) )
import Data.Type.Equality
import GHC.Exts
import Data.Type.Bool
import Data.Proxy


import Singletons

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

data Elt :: Rel SC where
  E :: t -> Elt (t ': ts) ts

type Stk i = List Elt i '[]

data TyFun :: * -> * -> *
type a ~> b = TyFun a b -> *
data StkSym0 :: SC ~> *
type family (f :: a ~> b) @@ (x :: a) :: b
type instance StkSym0 @@ x = Stk x


$(return [])

-- a sigma type. Second component depends on the first
-- according to some type function

data Sg (t :: s ~> *) :: * where
  And :: Proxy fst -> t @@ fst -> Sg t

data Inst :: Rel (Sg StkSym0) where
  PUSH :: forall (t :: *) (ts :: [*]) (v :: t) (vs :: Stk ts).
          Sing v -> Inst ('And ('Proxy :: Proxy ts) vs) 
                         ('And ('Proxy :: Proxy (t ': ts)) ('E v '::: vs))

  ADD  :: forall (ts :: [*]) (y :: Nat) (x :: Nat) (vs :: Stk ts).
          Inst ('And ('Proxy :: Proxy (Nat ': Nat ': ts)) ('E y '::: 'E x '::: vs))
               ('And ('Proxy :: Proxy (Nat ': ts))        ('E (x :+ y) '::: vs))

  IFPOP :: forall ts ts' vs vst vsf b.
           List Inst ('And ('Proxy :: Proxy ts) vs) 
                     ('And ('Proxy :: Proxy ts') vst) 
        -> List Inst ('And ('Proxy :: Proxy ts) vs) 
                     ('And ('Proxy :: Proxy ts') vsf) 
        -> Inst ('And ('Proxy :: Proxy (Bool ': ts)) ('E b '::: vs))
                ('And ('Proxy :: Proxy ts') (If b vst vsf))

-- SCW: switched t and f arguments to proxies so that it is clear that compilation of if
-- doesn't need to evaluate them
fact :: -- forall (ty :: *)(sc :: SC) (b :: Bool) (t :: ty) (f :: ty) (s :: Stk sc).
        Sing b -> Proxy t -> Proxy f -> Proxy s
     -> ('E (If b t f) '::: s) :~: (If b ('E t '::: s) ('E f '::: s))
fact STrue  _ _ _ = Refl
fact SFalse _ _ _ = Refl

compile :: -- forall (t :: *) (e :: Expr t) (ts :: [*]) (vs :: Stk ts).  
           forall t e ts vs.
           Sing e -> List Inst ('And ('Proxy :: Proxy ts) vs) 
                               ('And ('Proxy :: Proxy (t ': ts)) ('E (Eval e) '::: vs)) 
compile (SVal y)        = PUSH y ::: Nil
compile (e1 `SPlus` e2) = compile e1 ++ compile e2 ++ ADD ::: Nil
compile (SCond se0 (se1 :: Sing e1) (se2 :: Sing e2))  =
  case fact (sEval se0) (Proxy :: Proxy (Eval e1)) (Proxy :: Proxy (Eval e2)) (Proxy :: Proxy vs) of
   Refl -> compile se0 ++ IFPOP (compile se1) (compile se2) ::: Nil


-- The run function. The type of the list of instructions tells you exactly what should happen
-- when you run the machine. Conor's stack overflow version is not as strongly typed as the one
-- below.
-- http://stackoverflow.com/questions/14288569/agda-run-function-for-conors-stack-example
   

data SStk (vs :: Stk ts) where
  SSNil  :: SStk 'Nil
  SSCons :: Sing v -> SStk vs -> SStk ('E v '::: vs)


run :: -- forall (ts :: [*]) (ts' :: [*]) (vs :: Stk ts) (vs' :: Stk ts'). 
         List Inst ('And ('Proxy :: Proxy ts) vs) ('And ('Proxy :: Proxy ts') vs') -> SStk vs -> SStk vs'
run Nil vs = vs  
run (PUSH v ::: is) vs                             = run is (SSCons v vs)
run (ADD    ::: is) (v2 `SSCons` (v1 `SSCons` vs)) = run is ((v1 %:+ v2) `SSCons` vs)
run (IFPOP is1 is2 ::: is) (STrue `SSCons` vs)     = run is (run is1 vs)
run (IFPOP is1 is2 ::: is) (SFalse `SSCons` vs)    = run is (run is2 vs)




