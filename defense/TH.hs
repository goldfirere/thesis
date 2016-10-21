{-# LANGUAGE TemplateHaskellQuotes, TypeApplications, FlexibleContexts,
             RankNTypes, ScopedTypeVariables #-}

module TH where

import DB2

import Prelude hiding ( pred, head )
import Language.Haskell.TH.Syntax
import Data.Maybe
import Data.Proxy
import GHC.TypeLits
import Basics

-- wrapper for checkIn that uses proxy. Necessary only because Template Haskell
-- does not yet support visible type application
checkInProxy :: (KnownSymbol name, Typeable ty) => Proxy name -> Proxy ty
             -> Sing sch -> (In name ty sch => r) -> r
checkInProxy (_ :: Proxy name) (_ :: Proxy ty) sch thing
  = checkIn (SSym @name) (typeRep @ty) sch thing

-- `checkSchema 'db_fun ['sch1, 'sch2]` calls the function `db_fun` on `sch1`
-- and `sch2` after establishing the constraints on `db_fun`s type, to the
-- best of `checkSchema`'s ability.
checkSchema :: Name   -- name of function that will consume the schemas
            -> [Name] -- names of the variables that hold the schemas
            -> Q Exp
checkSchema fun_name sch_names = do
  VarI _ (ForallT _ cxt inner_ty) _ <- reify fun_name
  let sch_ty_names = map getSchemaTypeName (fst $ splitFunTys inner_ty)
      calls = mapMaybe (processPred (zip sch_ty_names sch_names)) cxt
  return (foldr AppE (foldl AppE (VarE fun_name) (map VarE sch_names)) calls)

-- association list from type-level schema names to term-level schema names
type SchemaMapping = [(Name, Name)]

processPred :: SchemaMapping
            -> Pred            -- predicate to process
            -> Maybe Exp       -- an function call used to establish the constraint
                               -- has type ((pred => r) -> r)
processPred sch_name_pairs pred
  | ConT cls <- head
  , cls == ''In
  , [name, ty, sch_ty] <- args
  = Just $
    VarE 'checkInProxy `AppE` (ConE 'Proxy `SigE` (ConT ''Proxy `AppT` name))
                       `AppE` (ConE 'Proxy `SigE` (ConT ''Proxy `AppT` ty))
                       `AppE` schemaExpression sch_ty sch_name_pairs
  | ConT cls <- head
  , cls == ''AllSchemaTys
  , [ConT mapped_class, sch_ty] <- args
  , mapped_class == ''Show
  = Just $ VarE 'checkShowSchema `AppE` schemaExpression sch_ty sch_name_pairs

  | ConT cls <- head
  , cls == ''AllSchemaTys
  , [ConT mapped_class, sch_ty] <- args
  , mapped_class == ''Read
  = Just $ VarE 'checkReadSchema `AppE` schemaExpression sch_ty sch_name_pairs

  | EqualityT <- head
  , [left, right] <- args
  , (ConT disjoint, [sch_ty1, sch_ty2]) <- splitAppTys left
  , disjoint == ''Disjoint
  , ConT true <- right
  , true == 'True   -- NB: just one quote!
  = Just $ VarE 'checkDisjoint `AppE` schemaExpression sch_ty1 sch_name_pairs
                               `AppE` schemaExpression sch_ty2 sch_name_pairs

  | otherwise
  = Nothing

  where
    (head, args) = splitAppTys pred

-- convert a type `sch` to an expression of type `Schema sch`.
schemaExpression :: Type -> SchemaMapping -> Exp
schemaExpression (SigT ty _) pairs = schemaExpression ty pairs
schemaExpression (VarT sch_ty) pairs
  | Just sch_term <- lookup sch_ty pairs
  = VarE sch_term
schemaExpression (ConT append `AppT` sch_ty1 `AppT` sch_ty2) pairs
  | append == ''(++)
  = InfixE (Just (schemaExpression sch_ty1 pairs)) (VarE '(%:++))
           (Just (schemaExpression sch_ty2 pairs))
schemaExpression sch_ty _ = error $ "No expression for " ++ show sch_ty

-- extract the sch from (Schema sch)
getSchemaTypeName :: Type -> Name
getSchemaTypeName (_ `AppT` VarT sch_ty_name) = sch_ty_name
getSchemaTypeName ty = error ("invalid type: " ++ show ty)

-- given `t a b c`, returns (t, [a,b,c])
splitAppTys :: Type -> (Type, [Type])
splitAppTys ty = go [] ty
  where
    go args (AppT fun arg) = go (arg:args) fun
    go args head           = (head, args)

-- given `a -> b -> c`, returns ([a,b], c)
splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = go [] ty
  where
    go args (AppT (AppT ArrowT arg) res) = go (arg:args) res
    go args res                          = (reverse args, res)
