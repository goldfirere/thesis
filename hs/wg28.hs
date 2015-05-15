{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors -fprint-explicit-kinds #-}

module Wg28 where

{-

   Towards Dependently-typed Haskell 

   joint work with Richard Eisenberg

   in fact, this code requires Richard's
   fork of GHC

   https://github.com/goldfirere/ghc


-}

import Prelude ( Bool(..), Maybe(..), error, undefined, return )
import Data.Type.Equality 
import GHC.Exts
import Data.Type.Bool
import Data.Proxy
import Singletons

{- Part I: Dynamic Typing in a Statically Typed Language -}

-- Old and (somewhat) boring

{-

dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn TBool True) t _ = t
dynIf (Dyn TBool False) _ f = f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TFun t1 t2) f) (Dyn t3 x) = case eqtype t1 t3 of
  Just Refl -> Dyn t2 (f x)
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TProd t1 t2) (x1,_)) = Dyn t1 x1
dynFst (Dyn _ _) = error "runtime type error"

data Dynamic where
   Dyn :: Typerep a -> a -> Dynamic

data Typerep (a :: *) where
  TBool  :: Typerep Bool
  TFun   :: Typerep t1 -> Typerep t2 -> Typerep (t1 -> t2)
  TProd  :: Typerep t1 -> Typerep t2 -> Typerep (t1, t2)
  TMaybe :: Typerep t1 -> Typerep (Maybe t1)
  -- let's get fancy!
  TDynamic :: Typerep Dynamic
  TTyperep :: Typerep a -> Typerep (Typerep a)
  -- Note: can't do ReaderT r m a 
  -- TReaderT :: Typerep r -> Typerep m -> Typerep a -> Typerep (ReaderT r m a)

eqtype :: Typerep a -> Typerep b -> Maybe (a :~: b)
eqtype TBool TBool = Just Refl
eqtype (TFun a1 b1) (TFun a2 b2) = case eqtype a1 a2 of 
  Just Refl -> case eqtype b1 b2 of
     Just Refl -> Just Refl
     Nothing -> Nothing
  Nothing -> Nothing
eqtype (TProd a1 b1) (TProd a2 b2) = case eqtype a1 a2 of 
  Just Refl -> case eqtype b1 b2 of
     Just Refl -> Just Refl
     Nothing -> Nothing
  Nothing -> Nothing
eqtype (TMaybe a1) (TMaybe a2) = case eqtype a1 a2 of 
  Just Refl -> Just Refl
  Nothing -> Nothing
eqtype TDynamic TDynamic = Just Refl
eqtype (TTyperep a1) (TTyperep a2) = case eqtype a1 a2 of 
  Just Refl -> Just Refl
  Nothing -> Nothing
eqtype _ _ = Nothing

-}


-- New! Improved!  And quite crazy.

-- Watch for: kind-indexed GADT,  star :: star


dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn (TCon TBool) True) t _ = t
dynIf (Dyn (TCon TBool) False) _ f = f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TApp (TApp (TCon TFun) t1) t2) f) (Dyn t3 x) = case eqtype t1 t3 of
  Just HRefl -> Dyn t2 (f x)
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TApp (TApp (TCon TProd) t1) t2) (x1,_)) = Dyn t1 x1
dynFst (Dyn _ _) = error "runtime type error"

data Dynamic where
   Dyn :: Typerep a -> a -> Dynamic

data Tycon (a :: k) where
  TBool    :: Tycon Bool
  TFun     :: Tycon (->)
  TProd    :: Tycon (,)
  TMaybe   :: Tycon Maybe
  TDynamic :: Tycon Dynamic
  -- Note: typerep is kind-polymorphic. We'll represent the instances
  TTyperep :: Typerep k -> Tycon (Typerep :: k -> *)
  TStar    :: Tycon *
  
data Typerep (a :: k) where
  TCon  :: Tycon c -> Typerep c
  TApp  :: Typerep a -> Typerep b -> Typerep (a b)

d1 :: Dynamic
d1 = Dyn (TApp (TCon (TTyperep (TCon TStar))) (TCon TBool)) (TCon TBool)

data ((a :: k1) :~~: (b :: k2)) where
  HRefl :: a :~~: a  

eqtycon :: Tycon a -> Tycon b -> Maybe (a :~~: b)
eqtycon TBool TBool       = Just HRefl
eqtycon TFun  TFun        = Just HRefl
eqtycon TProd TProd       = Just HRefl
eqtycon TMaybe TMaybe     = Just HRefl
eqtycon TDynamic TDynamic = Just HRefl
eqtycon (TTyperep k1) (TTyperep k2) = case eqtype k1 k2 of
  Just HRefl -> Just HRefl
  Nothing    -> Nothing 
eqtycon TStar TStar       = Just HRefl  
eqtycon _ _ = Nothing

eqtype :: Typerep a -> Typerep b -> Maybe (a :~~: b)
eqtype (TCon c1) (TCon c2) = eqtycon c1 c2
eqtype (TApp a1 b1) (TApp a2 b2) = case eqtype a1 a2 of 
  Just HRefl -> case eqtype b1 b2 of
     Just HRefl -> Just HRefl
     Nothing -> Nothing
  Nothing -> Nothing
eqtype _ _ = Nothing


{- Part II: DTH-curious? -}

-- Old and (somewhat) boring

data Expr :: * -> * where
  Val  :: t -> Expr t
  Plus :: Expr Nat -> Expr Nat -> Expr Nat
  Cond :: Expr Bool -> Expr t -> Expr t -> Expr t
  
eval :: Expr t -> t
eval (Val n)        = n
eval (e1 `Plus` e2) = eval e1 + eval e2
eval (Cond e0 e1 e2)  = if eval e0 then eval e1 else eval e2

optimize :: Expr t -> Expr t
optimize (Val x) = Val x
optimize (Plus (Val Zero) e) = optimize e
optimize (Plus e (Val Zero)) = optimize e
optimize (Plus e1 e2) = Plus (optimize e1) (optimize e2)
optimize (Cond (Val True) e1 e2) = optimize e1
optimize (Cond (Val False) e1 e2) = optimize e2
optimize (Cond e1 e2 e3) = Cond (optimize e1) (optimize e2) (optimize e3)

-- New! Improved!  (Promoted GADT)

type family Eval (x :: Expr t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 :+ Eval e2
  Eval ('Cond e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

-- and somewhat crazy (GADT indexed by a GADT)
        
data instance Sing (e :: Expr t) where
  SVal  :: Sing t -> Sing ('Val t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b)
  SCond :: Sing b -> Sing t -> Sing f -> Sing ('Cond b t f)

sEval :: Sing e -> Sing (Eval e)
sEval (SVal n) = n
sEval (e1 `SPlus` e2) = (sEval e1) %:+ (sEval e2)
sEval (SCond e0 e1 e2) = sIf (sEval e0) (sEval e1) (sEval e2)                                                 

data Equivalent e where
  Result :: Sing e' -> (Eval e :~: Eval e') -> Equivalent e


lemma :: Sing n -> (n :+ 'Zero) :~: n
lemma SZero = Refl
lemma (SSucc x) = case lemma x of
  Refl -> Refl


-- these two lemmas require "allow ambiguous types"
lemma2 :: (Eval e1 ~ Eval e1', Eval e2 ~ Eval e2')
          => Eval (Plus e1 e2) :~: Eval (Plus e1' e2')
lemma2 = Refl

lemma3 :: (Eval e0 ~ Eval e0', Eval e1 ~ Eval e1', Eval e2 ~ Eval e2')
          => Eval (Cond e0 e1 e2) :~: Eval (Cond e0' e1' e2')
lemma3 = Refl


sOpt :: Sing e -> Equivalent e
sOpt (SVal x) = Result (SVal x) Refl
sOpt (SPlus (SVal SZero) se) = case sOpt se of
  Result se' Refl -> Result se' Refl
-- this lemma is super annoying  
-- sOpt (SPlus se (SVal SZero)) = case (sOpt se) of
--  (Result se' Refl) -> case lemma (sEval se') of
--                          Refl -> Result se' Refl
-- why is this next case an error?                          
sOpt (SPlus e0 e1) = case (sOpt e0, sOpt e1) of
   (Result e0' Refl, Result e1' Refl) -> Result (SPlus e0' e1') Refl
                          
sOpt (SCond (SVal STrue)  e1 e2) = Result e1 Refl
sOpt (SCond (SVal SFalse) e1 e2) = Result e2 Refl
sOpt (SCond e0 e1 e2) = case (sOpt e0, sOpt e1, sOpt e2) of
  (Result e0' Refl, Result e1' Refl, Result e2' Refl) -> Result (SCond e0' e1' e2') Refl


{- Part III: What's next -}
