{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}

module Wg28current where

{-

   Towards Dependently-typed Haskell 

   Stephanie Weirich, University of Pennsylvania
   joint work with Richard Eisenberg

   this code compiles using GHC 7.8.3

-}

import Control.Monad.List

import Data.Type.Bool (If)
import GHC.TypeLits
import Data.Singletons.Prelude 
import Data.Singletons.TypeLits


{- Part I: Dynamic Typing in a Statically Typed Language -}

data Dynamic where
   Dyn :: TypeRep a -> a -> Dynamic

data Tycon (a :: k) where
  TBool :: Tycon Bool
  TInt  :: Tycon Int
  TFun  :: Tycon (->)
  TProd :: Tycon (,)
  
data TypeRep (a :: k) where
  TCon :: Tycon a -> TypeRep a
  TApp :: TypeRep a -> TypeRep b -> TypeRep (a b)


dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn TBool True) t _   = t
dynIf (Dyn TBool False) _ f  = f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TFun t1 t2) f) (Dyn t3 x)
  | Just Refl <- eqT t1 t3 = Dyn t2 (f x)
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TProd t1 _) (x1,_)) = Dyn t1 x1
dynFst (Dyn _ _) = error "runtime type error"

data (a :: k) :~: (b :: k) where
  Refl :: (a ~ b) => a :~: b

eqT :: TypeRep a -> TypeRep b -> Maybe (a :~: b)
eqT TBool TBool = Just Refl
eqT (TFun a1 b1) (TFun a2 b2) = case eqT a1 a2 of 
  Just Refl -> case eqT b1 b2 of
     Just Refl -> Just Refl
     Nothing -> Nothing
  Nothing -> Nothing
eqT (TProd a1 b1) (TProd a2 b2) = case eqT a1 a2 of 
  Just Refl -> case eqT b1 b2 of
     Just Refl -> Just Refl
     Nothing -> Nothing
  Nothing -> Nothing
eqT _ _ = Nothing

cast :: TypeRep a -> TypeRep b -> Maybe (a -> b)
cast t1 t2 = case eqT t1 t2 of
  Just Refl -> Just id
  Nothing -> Nothing










{- Part II: DTH? -}

-- A type safe evaluator and optimizer

-- first parameter is the type of literal numbers, second is the type of the
-- entire expression
data Expr (n :: *) :: * -> * where
  Val  :: t -> Expr n t
  Plus :: Expr n n -> Expr n n -> Expr n n 
  Cond :: Expr n Bool -> Expr n t -> Expr n t -> Expr n t
  
eval :: Num n => Expr n t -> t
eval (Val n)         = n
eval (e1 `Plus` e2)  = eval e1 + eval e2
eval (Cond e0 e1 e2) = if eval e0 then eval e1 else eval e2

-- constant folding function. The type index tells us that it preserves types.
optimize :: (Eq n, Num n) => Expr n t -> Expr n t
optimize (Val x) = Val x
optimize (Cond (Val True) e1 _) = optimize e1
optimize (Cond (Val False) _ e2) = optimize e2
optimize (Cond e1 e2 e3) = Cond (optimize e1) (optimize e2) (optimize e3)
optimize (Plus (Val 0) e) = optimize e
optimize (Plus e (Val 0)) = optimize e
optimize (Plus e1 e2) = Plus (optimize e1) (optimize e2)


{-
type family Eval (x :: Expr Nat t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 + Eval e2
  Eval ('Cond e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

-- a Singleton for that promoted GADT (i.e. a GADT indexed by a GADT)        
-- Sing is a data family for singleton types        
data instance Sing (e :: Expr Nat t) where
  SVal  :: Sing (u :: t) -> Sing ('Val u :: Expr Nat t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b :: Expr Nat Nat)
  SCond :: Sing a -> Sing b -> Sing c -> Sing ('Cond a b c :: Expr Nat t)
-}
