{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Pico.Util where

import Data.List

import Pico.Syn

findSigADT :: Sig -> ADT -> Maybe AdtKind
findSigADT sig t = do
  SigBnd_ADT _ kind <- find is_t sig
  return kind
  where
    is_t (SigBnd_ADT t' _) = t' == t
    is_t _                 = False

findSigDataCon :: Sig -> DataCon -> Maybe ConType
findSigDataCon sig k = do
  SigBnd_Con _ conty <- find is_t sig
  return conty
  where
    is_t (SigBnd_Con k' _) = k' == k
    is_t _                 = False

findCtx :: Context -> Var -> Maybe Bnd
findCtx ctx a = find is_a ctx
  where
    is_a (Bnd_Type a' _ _)   = a' == a
    is_a (Bnd_Coercion a' _) = a' == a

dom :: Context -> [Var]
dom = map dom1
  where
    dom1 (Bnd_Type v _ _)   = v
    dom1 (Bnd_Coercion v _) = v

removeMapping :: Unique -> [Argument] -> [Var] -> ([Argument], [Var])
removeMapping u rng dom
  = unzip [ (arg, v)
          | (arg, v@(Var _ u')) <- rng `zip` dom
          , u /= u' ]

freshen :: Data a => a -> a
freshen = everywhere' (mkT fresh)
  where
    mkT :: Var -> Var
    mkT

class Substable a where
  subst :: a -> [Argument] -> [Var] -> a

instance Substable Context where
  subst [] _ _ = []
  subst (Bnd_Type v@(Var _ u) rel kind : cxt) rng dom
    = let (rng', dom') = removeMapping u rng dom in
      Bnd_Type v rel (subst kind rng dom) : subst cxt rng' dom'
  subst (Bnd_Coercion v@(Var _ u) prop : cxt) rng dom
    = let (rng', dom') = removeMapping u rng dom in
      Bnd_Coercion v (subst prop rng dom) : subst cxt rng' dom'

instance Substable Type where
  subst (Type_Var v@(Var _ u)) rng dom
    | Just arg <- findInSubst u rng dom
    = case arg of
        Arg_Ty ty -> freshen ty
