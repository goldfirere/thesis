{-# LANGUAGE GADTs, PolyKinds, TypeOperators, 
             DataKinds, TypeFamilies, ImpredicativeTypes,
             RankNTypes, ScopedTypeVariables,
             UndecidableInstances, FlexibleContexts, 
             FlexibleInstances #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}


module Wg28 where

{-

   Towards Dependently Typed Haskell 
   =================================

   Stephanie Weirich, University of Pennsylvania
   joint work with Richard Eisenberg


   this code is available on github:
   https://github.com/goldfirere/thesis/hs/wg28.hs

   however, it requires Richard's fork of GHC to compile:
   https://github.com/goldfirere/ghc


-}

import Data.Type.Equality
import GHC.TypeLits
import Data.Type.Bool (If)
import Singletons (Sing(..), (%:+), sIf, SingI(..), sEqNat)


{-

GOAL:

   GHC can act like a dependently-typed language using a
   number of features such as:

        GADTs, type families, datatype promotion,
        kind polymorphism

   These features are based on two key ideas:

     - Type-level computation: Making the type-level like a
       functional programming language

     - Equality constraint abstraction: ( tau1 ~ tau2 ) => tau3 
       and existential quantification. 

-}





{-

  But there is a key limitation: equality constraints are only
  between types, not kinds. 

     - GADTs only indexed by types, not kinds

     - only vanilla ADTs can be promoted, not GADTs

-}





{-

Solution:  combine types and kinds together!

Today: two(?) examples showing why you might want to do this.

-}






{- Part 0: Trivial examples -}

-- types with kind signatures
type W = (Int :: *)

-- type level numbers
type X = (0 :: Nat)

-- type level list
type Y = ([Int, Bool, Nat] :: [*])

type W1 = (* :: *)

type Y1 = [Int, *, * -> *, forall (a :: *). a -> a]











{- Part 1: Dynamic Typing in a Statically Typed Language -}

-- see wg28current.hs first







data Dynamic where
   Dyn :: TypeRep a -> a -> Dynamic

data Tycon (a :: k) where
  TBool    :: Tycon Bool
  TFun     :: Tycon (->)
  TProd    :: Tycon (,)
  
data TypeRep (a :: k) where
  TCon  :: Tycon c -> TypeRep c
  TApp  :: TypeRep a -> TypeRep b -> TypeRep (a b)

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



data ((a :: k1) :~~: (b :: k2)) where
  HRefl :: (k1 ~ k2, a ~ b) => a :~~: b  


eqtycon :: Tycon a -> Tycon b -> Maybe (a :~~: b)
eqtycon TBool TBool       = Just HRefl
eqtycon TFun  TFun        = Just HRefl
eqtycon TProd TProd       = Just HRefl
eqtycon _ _ = Nothing


eqT :: TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqT (TCon c1) (TCon c2) = eqtycon c1 c2
eqT (TApp a1 b1) (TApp a2 b2) = case eqT a1 a2 of 
  Just HRefl -> case eqT b1 b2 of
     Just HRefl -> Just HRefl
     Nothing -> Nothing
  Nothing -> Nothing 
eqT _ _ = Nothing


{- Part 2: DTH -}

-- Old version (works with GHC 7.8.3)

-- first parameter is the type for numbers, second is the type of the
-- entire expression
data Expr (g :: [*]) (n :: *) :: * -> * where
  Val  :: t -> Expr g n t
  Plus :: Expr g n n -> Expr g n n -> Expr g n n 
  Cond :: Expr g n Bool -> Expr g n t -> Expr g n t -> Expr g n t
  Var  :: Var g t -> Expr g n t

data Var :: [*] -> * -> * where
  VZ   :: Var (t ': ts) t
  VS   :: Var ts u -> Var (t ': ts) u


data Env ( g :: [*] ) :: * where
  EZ   :: Env '[]
  ES   :: t -> Env ts -> Env (t ': ts)

                         
vlookup :: Var g t -> Env g -> t
vlookup VZ (ES x _) = x
vlookup (VS v) (ES _ xs) = vlookup v xs


                          
eval :: Num n =>  Expr g n t -> Env g -> t
eval (Val n)         r = n
eval (e1 `Plus` e2)  r = eval e1 r + eval e2 r
eval (Cond e0 e1 e2) r = if eval e0 r then eval e1 r else eval e2 r
eval (Var x)         r = vlookup x r


-- constant folding function. GADT tells us that it preserves types.
optimize :: (Eq n, Num n) => Expr g n t -> Expr g n t
optimize (Val x) = Val x
optimize (Cond (Val True) e1 _) = optimize e1
optimize (Cond (Val False) _ e2) = optimize e2
optimize (Cond e1 e2 e3) = Cond (optimize e1) (optimize e2) (optimize e3)
optimize (Plus (Val 0) e) = optimize e
optimize (Plus e (Val 0)) = optimize e
optimize (Plus e1 e2) = Plus (optimize e1) (optimize e2)
optimize (Var x) = Var x


-- New! Type family for a promoted GADT

-- We promote this datatype using GHC.TypeLit's "Nat" kind for type-level
-- numbers

type family VLookup (v :: Var g t) (e :: Env g) :: t where
  VLookup 'VZ ('ES x xs) = x
  VLookup ('VS v) ('ES x xs) = VLookup v xs

type family Eval (x :: Expr g Nat t) (r :: Env g) :: t where
  Eval ('Val n) r = n
  Eval ('Plus e1 e2) r = Eval e1 r + Eval e2 r
  Eval ('Cond e0 e1 e2) r = If (Eval e0 r) (Eval e1 r) (Eval e2 r)
  Eval ('Var x) r = VLookup x r
  -- Eval ('Abs t) r = \x -> Eval t (x ': r)
  

-- a Singleton for that promoted GADT (i.e. a GADT indexed by a GADT)
-- Sing is a data family for singleton types
        
-- NOTE that we have defined (Sing u :: Nat) to use Integers as the
-- runtime representation of type-level Nats (see singletons.hs)


data instance Sing (e :: Expr g Nat t) where
  SVal  :: Sing (u :: t) -> Sing ('Val u :: Expr g Nat t)
  SPlus :: Sing a -> Sing b -> Sing ('Plus a b :: Expr g Nat Nat)
  SCond :: Sing a -> Sing b -> Sing c -> Sing ('Cond a b c :: Expr g Nat t)
  SVar  :: Sing v -> Sing ('Var v :: Expr g Nat t)

data instance Sing (v :: Var g t) where
  SVZ   :: Sing ('VZ :: Var (t ': ts) t)
  SVS   :: Sing (vs  :: Var ts u) -> Sing ('VS vs :: Var (t ': ts) u)

data instance Sing (r :: Env g) where
  SEZ   :: Sing ('EZ :: Env '[])
  SES   :: Sing (u :: t) -> Sing (us :: Env ts)
            -> Sing (ES u us :: Env (t ': ts))
                                                                      

sLookup :: Sing (v :: Var g t) -> Sing (r :: Env g) -> Sing (VLookup v r)
sLookup SVZ (SES sx _) = sx
sLookup (SVS sv) (SES _ sxs) = sLookup sv sxs


                                     
-- An evaluator for the singletons; in lock-step with the type level
sEval :: Sing e -> Sing g -> Sing (Eval e g)
sEval (SVal n) r = n
sEval (e1 `SPlus` e2) r = (sEval e1 r) %:+ (sEval e2 r)
sEval (SCond e0 e1 e2) r = sIf (sEval e0 r) (sEval e1 r) (sEval e2 r)
sEval (SVar x) r = sLookup x r


---------------------------------------------------------
-- The optimizer should produce an equivalent expression

data Equivalent e where
  -- Result :: (forall r. Eval e r ~ Eval e' r) => Sing e' -> Equivalent e
  Result :: (forall r. Sing r -> Eval e r :~: Eval e' r) -> Sing e' -> Equivalent e


sOpt :: Sing e -> Equivalent e
sOpt (SVal x) = Result (\ _ -> Refl) (SVal x) 

sOpt (SCond (SVal STrue)  e1 _) = Result (\ _ -> Refl) e1
sOpt (SCond (SVal SFalse) _ e2) = Result (\ _ -> Refl) e2
sOpt (SCond e0 e1 e2) = case (sOpt e0, sOpt e1, sOpt e2) of
  (Result p0 e0', Result p1 e1', Result p2 e2') ->
    Result (\ r -> case (p0 r, p1 r, p2 r) of
                    (Refl, Refl, Refl) -> Refl) (SCond e0' e1' e2')

-- uses TypeNat equality (0 + n) ~ n
sOpt e@(SPlus (SVal sn) se) =
  case sEqNat sn (sing :: Sing 0) of
     Just Refl -> case sOpt se of
       Result p se' -> Result (\r -> case p r of
                                      Refl -> Refl) se' 
     Nothing   -> Result (\_ -> Refl) e

-- uses TypeNat equality (n + 0) ~ n
sOpt e@(SPlus se (SVal sn)) =
  case sEqNat sn (sing :: Sing 0) of
     Just Refl -> case sOpt se of
       Result p se' -> Result (\r -> case p r of
                                      Refl -> Refl) se'
     Nothing   -> Result (\_ -> Refl) e


sOpt (SPlus e0 e1) = case (sOpt e0, sOpt e1) of
   (Result p0 e0', Result p1 e1') ->
     Result (\r -> case (p0 r, p1 r) of
                    (Refl, Refl) -> Refl) (SPlus e0' e1')

sOpt (SVar x) = Result (\_ -> Refl) (SVar x)



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
