{-# LANGUAGE NoImplicitPrelude, TypeOperators, PolyKinds, GADTs,
             RankNTypes #-}

module Equality where

data (a :: k1) :~: (b :: k2) where
  Refl :: a :~: a

data Maybe a = Just a | Nothing

join :: Maybe (Maybe a) -> Maybe a
join Nothing = Nothing
join (Just Nothing) = Nothing
join (Just (Just x)) = Just x

data Proxy a = Proxy

data TypeRep :: k -> * where
  TyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)
  TyCon :: TypeRep a

eqT :: TypeRep a -> TypeRep b -> Maybe (a :~: b)
eqT = eqT

typeRep :: Proxy a -> TypeRep a
typeRep = typeRep

splitTypeRep :: TypeRep ab
             -> (forall a (b :: m). (ab ~ a b) => TypeRep a -> TypeRep b -> r)
             -> Maybe r
splitTypeRep (TyApp x y) f = Just (f x y)
splitTypeRep _           _ = Nothing

splitFun :: TypeRep f
         -> (forall x y. (f ~ (x -> y)) => TypeRep x -> TypeRep y -> r)
         -> Maybe r
splitFun t k
  = join (join (
    splitTypeRep t (\tarr_x ty ->
    splitTypeRep tarr_x (\tarr tx ->
    case eqT tarr (typeRep (Proxy :: Proxy (->))) of
      Just Refl -> Just (k tx ty)
      Nothing   -> Nothing ))))

data Dynamic where
  Dyn :: TypeRep a -> a -> Dynamic

dynApply :: Dynamic -> Dynamic -> Maybe Dynamic
dynApply (Dyn tx x) (Dyn ty y)
  = join (
    splitFun tx (\targ tres ->
    case eqT targ ty of
      Just Refl -> Just (Dyn tres (x y))
      Nothing   -> Nothing ))
      
