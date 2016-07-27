-- As used in motivation.

{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, DataKinds,
             PolyKinds, GADTs, RankNTypes, MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances,
             FunctionalDependencies, StandaloneDeriving,
             TypeOperators, ScopedTypeVariables, NoMonomorphismRestriction,
             MonadComprehensions, DeriveGeneric, FlexibleContexts,
             GeneralizedNewtypeDeriving, ConstraintKinds,
             LambdaCase, ViewPatterns, AllowAmbiguousTypes,
             DefaultSignatures, -- ImpredicativeTypes,
             ImplicitParams, MagicHash, UnboxedTuples,
             ExtendedDefaultRules, PatternSynonyms,
             DeriveFunctor, OverloadedLists -- , OverlappingInstances,
             -- NullaryTypeClasses
 #-}

module Scratch where

data (a :: k1) :~: (b :: k2) where
  Refl :: a :~: a

data TyCon (a :: k) where
  TInt    :: TyCon  Int
  TBool   :: TyCon  Bool
  TMaybe  :: TyCon  Maybe
  TArrow  :: TyCon  (->)

data TypeRep (a :: k) where
  TyCon :: TyCon a -> TypeRep a
  TyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)

eqTc :: TyCon a -> TyCon b -> Maybe (a :~: b)
eqTc TInt    TInt    = Just Refl
eqTc TBool   TBool   = Just Refl
eqTc TMaybe  TMaybe  = Just Refl
eqTc TArrow  TArrow  = Just Refl
eqTc _ _ = Nothing


eqT :: TypeRep a -> TypeRep b -> Maybe (a :~: b)
eqT (TyCon t1) (TyCon t2) = eqTc t1 t2
eqT (TyApp a1 b1) (TyApp a2 b2)
  | Just Refl <- eqT a1 a2
  , Just Refl <- eqT b1 b2
  = Just Refl
eqT _ _ = Nothing


data Dyn where
  Dyn :: TypeRep a -> a -> Dyn

dynApply :: Dyn -> Dyn -> Maybe Dyn
dynApply (Dyn (TyApp (TyApp (TyCon tarrow) targ) tres) fun) (Dyn targ' arg)
  | Just Refl <- eqTc tarrow TArrow
  , Just Refl <- eqT targ targ'
  = Just (Dyn tres (fun arg))
dynApply _ _ = Nothing
