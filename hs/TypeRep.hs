{- Copyright (c) 2016 Richard Eisenberg
 -}

{-# LANGUAGE TypeOperators, TypeFamilies, TypeApplications,
             ExplicitForAll, ScopedTypeVariables, GADTs, TypeFamilyDependencies,
             TypeInType, ConstraintKinds, UndecidableInstances,
             FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleContexts, StandaloneDeriving, InstanceSigs,
             RankNTypes, UndecidableSuperClasses, AllowAmbiguousTypes #-}

module Basics where

import Data.Type.Bool
import Data.Type.Equality
import GHC.TypeLits
import Data.Proxy
import GHC.Exts
import Data.Kind
import Unsafe.Coerce

-------------------------------
-- Utilities

-- Heterogeneous propositional equality
data (a :: k1) :~~: (b :: k2) where
  HRefl :: a :~~: a

-- Type-level inequality
type a /= b = Not (a == b)

-- append type-level lists (schemas)
type family s1 ++ s2 where
  '[]       ++ s2 = s2
  (s ': s1) ++ s2 = s ': (s1 ++ s2)

-- This is needed in order to prove disjointness, because GHC can't
-- handle inequality well.
assumeEquality :: forall a b r. ((a ~ b) => r) -> r
assumeEquality thing = case unsafeCoerce Refl :: a :~: b of
  Refl -> thing

-- Shorter name for shorter example
eq :: TestEquality f => f a -> f b -> Maybe (a :~: b)
eq = testEquality

-------------------------------
-- Singleton lists

-- Unlike in the singletons paper, we now have injective type
-- families, so we use that to model singletons; it's a bit
-- cleaner than the original approach
type family Sing = (r :: k -> Type) | r -> k

-- Cute type synonym.
type Π = Sing

-- Really, just singleton lists. Named Schema for better output
-- during example.
data Schema :: forall k. [k] -> Type where
  Nil :: Schema '[]
  (:>>) :: Sing h -> Schema t -> Schema (h ': t)
infixr 5 :>>
type instance Sing = Schema

-- Append singleton lists
(%:++) :: Schema a -> Schema b -> Schema (a ++ b)
Nil %:++ x = x
(a :>> b) %:++ c = a :>> (b %:++ c)

--------------------------------
-- Type-indexed type representations
-- Based on "A reflection on types"

data TyCon (a :: k) where
  Int :: TyCon Int
  Bool :: TyCon Bool
  Char :: TyCon Char
  List :: TyCon []
  Maybe :: TyCon Maybe
  Arrow :: TyCon (->)
  TYPE  :: TyCon TYPE
  RuntimeRep :: TyCon RuntimeRep
  PtrRepLifted' :: TyCon 'PtrRepLifted
  -- If extending, add to eqTyCon too

eqTyCon :: TyCon a -> TyCon b -> Maybe (a :~~: b)
eqTyCon Int Int = Just HRefl
eqTyCon Bool Bool = Just HRefl
eqTyCon Char Char = Just HRefl
eqTyCon List List = Just HRefl
eqTyCon Maybe Maybe = Just HRefl
eqTyCon Arrow Arrow = Just HRefl
eqTyCon TYPE TYPE = Just HRefl
eqTyCon RuntimeRep RuntimeRep = Just HRefl
eqTyCon PtrRepLifted' PtrRepLifted' = Just HRefl
eqTyCon _ _ = Nothing

-- Check whether or not a type is really a plain old tycon;
-- necessary to avoid warning in kindRep
type family Primitive (a :: k) :: Constraint where
  Primitive (_ _) = ('False ~ 'True)
  Primitive _     = (() :: Constraint)

data TypeRep (a :: k) where
  TyCon :: forall (a :: k). (Primitive a, Typeable k) => TyCon a -> TypeRep a
  TyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)

-- Equality on TypeReps
eqT :: TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqT (TyCon tc1) (TyCon tc2) = eqTyCon tc1 tc2
eqT (TyApp f1 a1) (TyApp f2 a2) = do
  HRefl <- eqT f1 f2
  HRefl <- eqT a1 a2
  return HRefl
eqT _ _ = Nothing


--------------------------------------
-- Existentials

data TyConX where
  TyConX :: forall (a :: k). (Primitive a, Typeable k) => TyCon a -> TyConX

instance Read TyConX where
  readsPrec _ "Int" = [(TyConX Int, "")]
  readsPrec _ "Bool" = [(TyConX Bool, "")]
  readsPrec _ "List" = [(TyConX List, "")]
  readsPrec _ _ = []

-- This variant of TypeRepX allows you to specify an arbitrary
-- constraint on the inner TypeRep
data TypeRepX :: (forall k. k -> Constraint) -> Type where
  TypeRepX :: forall k (c :: forall k'. k' -> Constraint) (a :: k).
              c a => TypeRep a -> TypeRepX c

-- This constraint is always satisfied
class ConstTrue (a :: k) -- needs the :: k to make it a specified tyvar
instance ConstTrue a

instance forall (c :: forall k. k -> Constraint). Show (TypeRepX c) where
  show (TypeRepX tr) = show tr

-- Just enough functionality to get through example. No parentheses
-- or other niceties.
instance Read (TypeRepX ConstTrue) where
  readsPrec p s = do
    let tokens = words s
    tyreps <- mapM read_token tokens
    return (foldl1 mk_app tyreps, "")

    where
      read_token "String" = return (TypeRepX $ typeRep @String)
      read_token other = do
        (TyConX tc, _) <- readsPrec p other
        return (TypeRepX (TyCon tc))

      mk_app :: TypeRepX ConstTrue -> TypeRepX ConstTrue -> TypeRepX ConstTrue
      mk_app (TypeRepX f) (TypeRepX a) = case kindRep f of
        TyCon Arrow `TyApp` k1 `TyApp` _
          | Just HRefl <- k1 `eqT` kindRep a -> TypeRepX (TyApp f a)
        _ -> error "ill-kinded type"

-- instance Read (TypeRepX ((~~) Type))  RAE: need (~~) :: forall k1. k1 -> forall k2. k2 -> Constraint
-- RAE: need kind signatures on classes

-- TypeRepX ((~~) Type)
-- (~~) :: forall k1 k2. k1 -> k2 -> Constraint
-- I need: (~~) :: forall k1. k1 -> forall k2. k2 -> Constraint

class k ~~ Type => IsType (x :: k)
instance k ~~ Type => IsType (x :: k)

instance Read (TypeRepX IsType) where
  readsPrec p s = case readsPrec @(TypeRepX ConstTrue) p s of
    [(TypeRepX tr, "")]
      | Just HRefl <- eqT (kindRep tr) (typeRep @Type)
      -> [(TypeRepX tr, "")]
    _ -> error "wrong kind"

data TypeRepXX where
  TRXX :: TypeRep a -> TypeRepXX

instance Read TypeRepXX where
  readsPrec p s = do
    let tokens = words s
    tyreps <- mapM read_token tokens
    return (foldl1 mk_app tyreps, "")

    where
      read_token "String" = return (TRXX $ typeRep @String)
      read_token other = do
        (TyConX tc, _) <- readsPrec p other
        return (TRXX (TyCon tc))

      mk_app :: TypeRepXX -> TypeRepXX -> TypeRepXX
      mk_app (TRXX f) (TRXX a) = case kindRep f of
        TyCon Arrow `TyApp` k1 `TyApp` _
          | Just HRefl <- k1 `eqT` kindRep a -> TRXX (TyApp f a)
        _ -> error "ill-kinded type"

-----------------------------
-- Get the kind of a type

kindRep :: TypeRep (a :: k) -> TypeRep k
kindRep (TyCon _) = typeRep
kindRep (TyApp (f :: TypeRep (tf :: k1 -> k)) _) = case kindRep f :: TypeRep (k1 -> k) of
  TyApp _ res -> res

-- Convert an explicit TypeRep into an implicit one. Doesn't require unsafeCoerce
-- in Core
withTypeable :: forall a r. TypeRep a -> (Typeable a => r) -> r
withTypeable tr thing = unsafeCoerce (Don'tInstantiate thing :: DI a r) tr
newtype DI a r = Don'tInstantiate (Typeable a => r)

-----------------------------
-- Implicit TypeReps (Typeable)

class (Primitive a, Typeable k) => TyConAble (a :: k) where
  tyCon :: TyCon a

instance TyConAble Int       where tyCon = Int
instance TyConAble Bool      where tyCon = Bool
instance TyConAble Char      where tyCon = Char
instance TyConAble []        where tyCon = List
instance TyConAble Maybe     where tyCon = Maybe
instance TyConAble (->)      where tyCon = Arrow
instance TyConAble TYPE      where tyCon = TYPE
instance TyConAble 'PtrRepLifted   where tyCon = PtrRepLifted'
instance TyConAble RuntimeRep    where tyCon = RuntimeRep

-- Can't just define Typeable the way we want, because the instances
-- overlap. So we have to mock up instance chains via closed type families.
class Typeable' (a :: k) (b :: Bool) where
  typeRep' :: TypeRep a

type family CheckPrim a where
  CheckPrim (_ _) = 'False
  CheckPrim _     = 'True

-- NB: We need the ::k and the ::Constraint so that this has a CUSK, allowing
-- the polymorphic recursion with TypeRep. See also #9200, though the requirement
-- for the constraints is correct.
type Typeable (a :: k) = (Typeable' a (CheckPrim a) :: Constraint)

instance TyConAble a => Typeable' a 'True where
  typeRep' = TyCon tyCon

instance (Typeable a, Typeable b) => Typeable' (a b) 'False where
  typeRep' = TyApp typeRep typeRep

typeRep :: forall a. Typeable a => TypeRep a
typeRep = typeRep' @_ @_ @(CheckPrim a) -- RAE: #11512 says we need the extra @_.

-----------------------------
-- Useful instances

instance Show (TypeRep a) where
  show (TyCon tc) = show tc
  show (TyApp tr1 tr2) = show tr1 ++ " " ++ show tr2

deriving instance Show (TyCon a)

instance TestEquality TypeRep where
  testEquality tr1 tr2
    | Just HRefl <- eqT tr1 tr2
    = Just Refl
    | otherwise
    = Nothing

---------------------------
-- More singletons

-- a TypeRep really is a singleton
type instance Sing = (TypeRep :: Type -> Type)

data SSymbol :: Symbol -> Type where
  SSym :: KnownSymbol s => SSymbol s
type instance Sing = SSymbol

instance TestEquality SSymbol where
  testEquality :: forall s1 s2. SSymbol s1 -> SSymbol s2 -> Maybe (s1 :~: s2)
  testEquality SSym SSym = sameSymbol @s1 @s2 Proxy Proxy

instance Show (SSymbol name) where
  show s@SSym = symbolVal s
