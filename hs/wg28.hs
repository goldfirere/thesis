{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors -fprint-explicit-kinds #-}


module Wg28 where

{-

   Towards Dependently-typed Haskell 

   joint work with Richard Eisenberg

   this code requires Richard's fork of GHC

   https://github.com/goldfirere/ghc


-}


import Data.Type.Equality 
import GHC.Exts
import Data.Type.Bool
import Data.Proxy
import Singletons
import GHC.TypeLits

{- Part I: Dynamic Typing in a Statically Typed Language -}

-- Old and (somewhat) boring

{-



data Dynamic where
   Dyn :: Typerep a -> a -> Dynamic

data Typerep (a :: *) where
  TBool  :: Typerep Bool
  TFun   :: Typerep t1 -> Typerep t2 -> Typerep (t1 -> t2)
  TProd  :: Typerep t1 -> Typerep t2 -> Typerep (t1, t2)
  -- let's get fancy!
  TDynamic :: Typerep Dynamic
  TTyperep :: Typerep a -> Typerep (Typerep a)
  -- Note: can't do ReaderT r m a 
  -- TReaderT :: Typerep r -> Typerep m -> Typerep a -> Typerep (ReaderT r m a)

dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn TBool True) t _   = t
dynIf (Dyn TBool False) _ f  = f
dynIf (Dyn TDynamic d) t f   = dynIf d t f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TFun t1 t2) f) (Dyn t3 x) = case eqtype t1 t3 of
  Just Refl -> Dyn t2 (f x)
dynApply (Dyn TDynamic d1) d2 = dynApply d1 d2
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TProd t1 t2) (x1,_)) = Dyn t1 x1
dynFst (Dyn TDynamic d1) d2 = dynFst d1 d2
dynFst (Dyn _ _) = error "runtime type error"

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

{-
data Tycon (a :: k) where
  TBool    :: Tycon Bool
  TFun     :: Tycon (->)
  TProd    :: Tycon (,)
  TMaybe   :: Tycon Maybe
  TDynamic :: Tycon Dynamic
  -- Note: typerep is now kind-polymorphic. We'll represent the instances
  TTyperep :: Typerep k -> Tycon (Typerep :: k -> *)
  TStar    :: Tycon *
  
data Typerep (a :: k) where
  TCon  :: Tycon c -> Typerep c
  TApp  :: Typerep a -> Typerep b -> Typerep (a b)

d1 :: Dynamic
d1 = Dyn (TApp (TCon (TTyperep (TCon TStar))) (TCon TBool)) (TCon TBool)


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
-}

{- Part II: DTH-curious? -}

-- Old and (somewhat) boring

-- first parameter is the type of literal numbers, second is the type of the
-- entire expression
data Expr :: * -> * -> * where
  Val  :: t -> Expr a t
  Plus :: Expr a a -> Expr a a -> Expr a a 
  Cond :: Expr a Bool -> Expr a t -> Expr a t -> Expr a t
  
eval :: Expr Integer t -> t
eval (Val n)        = n
eval (e1 `Plus` e2) = eval e1 + eval e2
eval (Cond e0 e1 e2)  = if eval e0 then eval e1 else eval e2

-- constant folding function. GADT tells us that it preserves types.
optimize :: Expr Integer t -> Expr Integer t
optimize (Val x) = Val x
optimize (Plus (Val 0) e) = optimize e
optimize (Plus e (Val 0)) = optimize e
optimize (Plus e1 e2) = Plus (optimize e1) (optimize e2)
optimize (Cond (Val True) e1 e2) = optimize e1
optimize (Cond (Val False) e1 e2) = optimize e2
optimize (Cond e1 e2 e3) = Cond (optimize e1) (optimize e2) (optimize e3)

-- New! Improved!  (Type family for a promoted GADT)

-- When we promote this datatype, we'll use GHC.TypeLit's Nat type for numbers
type family Eval (x :: Expr Nat t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 + Eval e2
  Eval ('Cond e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

-- a Singleton for that GADT (i.e. a GADT indexed by a GADT)

data instance Sing (e :: Expr Nat t) where
  SVal  :: Sing (u :: t) -> Sing ('Val u :: Expr Nat t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b :: Expr Nat Nat)
  SCond :: Sing a -> Sing b -> Sing c -> Sing ('Cond a b c :: Expr Nat t)

                                       
sEval :: Sing e -> Sing (Eval e)
sEval (SVal n) = n
sEval (e1 `SPlus` e2) = (sEval e1) %:+ (sEval e2)
sEval (SCond e0 e1 e2) = sIf (sEval e0) (sEval e1) (sEval e2)                                                 

data Equivalent e where
  Result :: Sing e' -> (Eval e :~: Eval e') -> Equivalent e

sOpt :: Sing e -> Equivalent e
sOpt (SVal x) = Result (SVal x) Refl

-- uses TypeNat equality (0 + n) ~ n
sOpt e@(SPlus (SVal (SNat :: Sing n0)) se) =
  case sameNat (Proxy :: Proxy n0) (Proxy :: Proxy 0) of
     Just Refl -> case sOpt se of
       Result se' Refl -> Result se' Refl
     Nothing   -> Result e Refl
     
-- uses TypeNat equality (n + 0) ~ n
sOpt e@(SPlus se (SVal (SNat :: Sing n0))) =
  case sameNat (Proxy :: Proxy n0) (Proxy :: Proxy 0) of
     Just Refl -> case sOpt se of
       Result se' Refl -> Result se' Refl
     Nothing   -> Result e Refl

sOpt (SPlus e0 e1) = case (sOpt e0, sOpt e1) of
   (Result e0' Refl, Result e1' Refl) -> Result (SPlus e0' e1') Refl
                          
sOpt (SCond (SVal STrue)  e1 e2) = Result e1 Refl
sOpt (SCond (SVal SFalse) e1 e2) = Result e2 Refl
sOpt (SCond e0 e1 e2) = case (sOpt e0, sOpt e1, sOpt e2) of
  (Result e0' Refl, Result e1' Refl, Result e2' Refl) -> Result (SCond e0' e1' e2') Refl


{- Part III: What's next -}

-- Pi!
  
-- replace  "forall e. Sing e ->"  with "pi e -> " in types
  
-- no need for type family as eval/Eval available from single definition
-- no need for sEval, pi does both


{-  
data Equivalent e where
  Result :: pi e' -> (Eval e :~: Eval e') -> Equivalent e

opt :: pi e -> Equivalent e
opt (Val x) = Result (Val x) Refl
opt (Plus (Val 0) e) = case opt e of
  Result e' Refl -> Result e' Refl
opt (Plus e (Val 0)) = case (opt e) of
  (Result e' Refl) ->  Result e' Refl
opt (Plus e0 e1) = case (opt e0, opt e1) of
   (Result e0' Refl, Result e1' Refl) -> Result (Plus e0' e1') Refl                          
opt (Cond (Val True)  e1 e2) = Result e1 Refl
opt (Cond (Val False) e1 e2) = Result e2 Refl
opt (Cond e0 e1 e2) = case (opt e0, opt e1, opt e2) of
  (Result e0' Refl, Result e1' Refl, Result e2' Refl) -> Result (Cond e0' e1' e2') Refl

-}
