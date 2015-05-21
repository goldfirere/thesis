{-# LANGUAGE GADTs, PolyKinds, TypeOperators, TemplateHaskell,
             DataKinds, TypeFamilies, UndecidableInstances,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors -Wall -fprint-explicit-kinds #-}


module Wg28 where

{-

   Towards Dependently-typed Haskell 

   Stephanie Weirich, University of Pennsylvania
   joint work with Richard Eisenberg

   this code requires Richard's fork of GHC

   https://github.com/goldfirere/ghc


-}


import Data.Type.Equality ((:~:)(..))
import Data.Type.Bool (If)
import GHC.TypeLits

import Singletons (Sing(..), (%:+), sIf, SingI(..), sEqNat)

-- ROAD MAP:
--    


{- Part I: Dynamic Typing in a Statically Typed Language -}

-- Old and (somewhat) boring

{-
data Dynamic where
   Dyn :: TypeRep a -> a -> Dynamic

data TypeRep (a :: *) where
  TBool  :: TypeRep Bool
  TFun   :: TypeRep t1 -> TypeRep t2 -> TypeRep (t1 -> t2)
  TProd  :: TypeRep t1 -> TypeRep t2 -> TypeRep (t1, t2)
  -- let's get fancy!
  TDynamic :: TypeRep Dynamic
  TTypeRep :: TypeRep a -> TypeRep (TypeRep a)
  -- Note: can't do MaybeT m a 
  -- TMaybeT :: TypeRep m -> TypeRep a -> TypeRep (MaybeT m a)

dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn TBool True) t _   = t
dynIf (Dyn TBool False) _ f  = f
dynIf (Dyn TDynamic d) t f   = dynIf d t f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TFun t1 t2) f) (Dyn t3 x) = case eqT t1 t3 of
  Just Refl -> Dyn t2 (f x)
  Nothing   -> error "runtime type error"
dynApply (Dyn TDynamic d1) d2 = dynApply d1 d2
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TProd t1 _) (x1,_)) = Dyn t1 x1
dynFst (Dyn TDynamic d1) = dynFst d1
dynFst (Dyn _ _) = error "runtime type error"

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
eqT TDynamic TDynamic = Just Refl
eqT (TTypeRep a1) (TTypeRep a2) = case eqT a1 a2 of 
  Just Refl -> Just Refl
  Nothing -> Nothing
eqT _ _ = Nothing

-}


-- New! Improved!  And quite crazy.

-- Watch for: kind-indexed GADT,  star :: star


data Tycon (a :: k) where
  TBool    :: Tycon Bool
  TFun     :: Tycon (->)
  TProd    :: Tycon (,)
  TMaybe   :: Tycon Maybe
  TDynamic :: Tycon Dynamic
  -- Note: typerep is now kind-polymorphic. We'll represent the instances
  TTypeRep :: TypeRep k -> Tycon (TypeRep :: k -> *)
  TStar    :: Tycon *
  
data TypeRep (a :: k) where
  TCon  :: Tycon c -> TypeRep c
  TApp  :: TypeRep a -> TypeRep b -> TypeRep (a b)

d1 :: Dynamic
d1 = Dyn (TApp (TCon (TTypeRep (TCon TStar))) (TCon TBool)) (TCon TBool)


dynIf :: Dynamic -> a -> a -> a
dynIf (Dyn (TCon TBool) True) t _ = t
dynIf (Dyn (TCon TBool) False) _ f = f
dynIf (Dyn _ _) _ _ = error "runtime type error"

dynApply :: Dynamic -> Dynamic -> Dynamic
dynApply (Dyn (TApp (TApp (TCon TFun) t1) t2) f) (Dyn t3 x)
  | Just HRefl <- eqT t1 t3 = Dyn t2 (f x)
dynApply (Dyn _ _) _ = error "runtime type error"

dynFst :: Dynamic -> Dynamic
dynFst (Dyn (TApp (TApp (TCon TProd) t1) _) (x1,_)) = Dyn t1 x1
dynFst (Dyn _ _) = error "runtime type error"

data Dynamic where
   Dyn :: TypeRep a -> a -> Dynamic


data ((a :: k1) :~~: (b :: k2)) where
  HRefl :: a :~~: a  

eqtycon :: Tycon a -> Tycon b -> Maybe (a :~~: b)
eqtycon TBool TBool       = Just HRefl
eqtycon TFun  TFun        = Just HRefl
eqtycon TProd TProd       = Just HRefl
eqtycon TMaybe TMaybe     = Just HRefl
eqtycon TDynamic TDynamic = Just HRefl
eqtycon (TTypeRep k1) (TTypeRep k2) = case eqT k1 k2 of
  Just HRefl -> Just HRefl
  Nothing    -> Nothing 
eqtycon TStar TStar       = Just HRefl  
eqtycon _ _ = Nothing

eqT :: TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqT (TCon c1) (TCon c2) = eqtycon c1 c2
eqT (TApp a1 b1) (TApp a2 b2) = case eqT a1 a2 of 
  Just HRefl -> case eqT b1 b2 of
     Just HRefl -> Just HRefl
     Nothing -> Nothing
  Nothing -> Nothing
eqT _ _ = Nothing


{- Part II: DTH-curious? -}

-- Old and (somewhat) boring

-- first parameter is the type of literal numbers, second is the type of the
-- entire expression
data Expr :: * -> * -> * where
  Val  :: t -> Expr n t
  Plus :: Expr n n -> Expr n n -> Expr n n 
  Cond :: Expr n Bool -> Expr n t -> Expr n t -> Expr n t
  
eval :: Num n => Expr n t -> t
eval (Val n)         = n
eval (e1 `Plus` e2)  = eval e1 + eval e2
eval (Cond e0 e1 e2) = if eval e0 then eval e1 else eval e2

-- constant folding function. GADT tells us that it preserves types.
optimize :: (Eq n, Num n) => Expr n t -> Expr n t
optimize (Val x) = Val x
optimize (Cond (Val True) e1 _) = optimize e1
optimize (Cond (Val False) _ e2) = optimize e2
optimize (Cond e1 e2 e3) = Cond (optimize e1) (optimize e2) (optimize e3)
optimize (Plus (Val 0) e) = optimize e
optimize (Plus e (Val 0)) = optimize e
optimize (Plus e1 e2) = Plus (optimize e1) (optimize e2)

-- New! Improved!  (Type family for a promoted GADT)

-- When we promote this datatype, we'll use GHC.TypeLit's Nat type for numbers
type family Eval (x :: Expr Nat t) :: t where
  Eval ('Val n) = n
  Eval ('Plus e1 e2) = Eval e1 + Eval e2
  Eval ('Cond e0 e1 e2) = If (Eval e0) (Eval e1) (Eval e2)

-- a Singleton for that promoted GADT (i.e. a GADT indexed by a GADT)
-- Sing is a data family for singleton types
        
-- NOTE that GHC.TypeLits uses Integers as the runtime representation
-- of type-level Nats        
data instance Sing (e :: Expr Nat t) where
  SVal  :: Sing (u :: t) -> Sing ('Val u :: Expr Nat t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b :: Expr Nat Nat)
  SCond :: Sing a -> Sing b -> Sing c -> Sing ('Cond a b c :: Expr Nat t)

-- An evaluator for the singletons; in lock-step with the type level
sEval :: Sing e -> Sing (Eval e)
sEval (SVal n) = n
sEval (e1 `SPlus` e2) = (sEval e1) %:+ (sEval e2)
sEval (SCond e0 e1 e2) = sIf (sEval e0) (sEval e1) (sEval e2)                                                 


---------------------------------------------------------
-- The optimizer should produce an equivalent expression

data Equivalent e where
  Result :: (Eval e ~ Eval e') => Sing e' -> Equivalent e

sOpt :: Sing e -> Equivalent e
sOpt (SVal x) = Result (SVal x) 

sOpt (SCond (SVal STrue)  e1 _) = Result e1
sOpt (SCond (SVal SFalse) _ e2) = Result e2
sOpt (SCond e0 e1 e2) = case (sOpt e0, sOpt e1, sOpt e2) of
  (Result e0', Result e1', Result e2') -> Result (SCond e0' e1' e2')

-- uses TypeNat equality (0 + n) ~ n
sOpt e@(SPlus (SVal sn) se) =
  case sEqNat sn (sing :: Sing 0) of
     Just Refl -> case sOpt se of
       Result se' -> Result se' 
     Nothing   -> Result e
     
-- uses TypeNat equality (n + 0) ~ n
sOpt e@(SPlus se (SVal sn)) =
  case sEqNat sn (sing :: Sing 0) of
     Just Refl -> case sOpt se of
       Result se' -> Result se'
     Nothing   -> Result e

sOpt (SPlus e0 e1) = case (sOpt e0, sOpt e1) of
   (Result e0', Result e1') -> Result (SPlus e0' e1')





{- Part III: What's next -}

-- Pi!
  
-- replace  "forall e. Sing e ->"  with "pi e -> " in types
  
-- no need for type family as eval/Eval available from single definition

{-
data Equivalent e where
  Result :: pi e' -> (Eval e ~ Eval e') => Equivalent e

opt :: pi e -> Equivalent e
opt (Val x) = Result (Val x) 
opt (Plus e0 e1) = case (opt e0, opt e1) of
   (Result e0', Result e1') -> Result (Plus e0' e1')                           
opt (Cond (Val True)  e1 e2) = Result e1 
opt (Cond (Val False) e1 e2) = Result e2 
opt (Cond e0 e1 e2) = case (opt e0, opt e1, opt e2) of
  (Result e0', Result e1' , Result e2') -> Result (Cond e0' e1' e2') 
opt (Plus (Val 0) e) = case opt e of
  Result e' -> Result e' 
opt (Plus e (Val 0)) = case (opt e) of
  (Result e') ->  Result e' 

-}


-- Sigma! 

-- Equivalent e is a (refined) Sigma type.
-- What if we had such types without having to predeclare them?
-- i.e. something like  { e' | Eval e ~ Eval e' }

{-
opt :: pi e -> { e' | Eval e ~ Eval e' }
opt (Val x) = (Val x) 
opt (Plus e0 e1) = Plus e0' e1' where
  e0' = opt e0
  e1' = opt e1
opt (Cond (Val True)  e1 e2) = e1
opt (Cond (Val False) e1 e2) = e2
opt (Cond e0 e1 e2) = Cond e0' e1' e2' where
  e0' = opt e0
  e1' = opt e1
  e2' = opt e2
opt (Plus (Val 0) e) = e' where
  e' = opt e
opt (Plus e (Val 0)) = e' where
  e' = opt e 
-}

{- Part IV: References -}

{-   

Available from http://www.cis.upenn.edu/~eir/pubs.html

Kind equalities, theory and practice:

Stephanie Weirich, Justin Hsu, and Richard A. Eisenberg.
System FC with explicit kind equality. In Proceedings of The 18th
ACM SIGPLAN International Conference on Functional Programming,
ICFP '13, pages 275-286, Boston, MA, September 2013.

An overabundance of equality: Implementing kind equalities into
Haskell. Richard A. Eisenberg.
Submitted to Haskell Symposium.

Singletons:

Dependently Typed Programming with Singletons. Richard A. Eisenberg and
Stephanie Weirich. Haskell Symposium 2012, Copenhagen, Denmark.

Promoting Functions to Type Families in Haskell. Richard A. Eisenberg and Jan
Stolarek. Haskell Symposium 2014, Gothenburg, Sweden.


-}
