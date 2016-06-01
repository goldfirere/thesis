module Pico.Rules where

import Pico.Syn
import Pico.Util

tc_ :: Sig -> Tycon -> Maybe (Telescope, Telescope, Tycon)
tc_ sig (TyCon_ADT t) = do
  AdtKi_Vars vars_tys <- findSigADT sig t
  let (vars, kinds) = unzip vars_tys
  return ([], zipWith (flip Bnd_Type Rel_Rel) vars kinds, TyCon_Type)

tc_ sig (TyCon_DataCon k) = do
  ConTy_Pair d (TyCon_ADT t) <- findSigDataCon sig k
  AdtKi_Vars vars_tys <- findSigADT sig t
  let (vars, kinds) = unzip vars_tys
  return (zipWith (flip Bnd_Type Rel_Irrel) vars kinds, d, TyCon_ADT t)

tc_ _ TyCon_Type = return ([], [], TyCon_Type)

ty_ :: Sig -> Context -> Type -> Maybe Kind
ty_ sig ctx (Type_Var a) = do
  ctx_ sig ctx
  Bnd_Type _ Rel_Rel k <- findCtx ctx a
  return k

ty_ sig ctx (Type_TyCon h ts) = do
  (d1, d2, h') <- tc_ sig h
  ctx_ sig ctx
  vec_ sig (rel ctx) ts (rel d1)
  return (foldr (Type_Pi Pi_Matchable) (foldl Type_App (Type_TyCon h') (map Arg_Ty ts)) (subst d2 ts (dom d1)))

ctx_ :: Sig -> Context -> Maybe ()
ctx_ = undefined
