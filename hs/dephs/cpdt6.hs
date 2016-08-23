{-# LANGUAGE TemplateHaskell, PolyKinds, DataKinds, GADTs, TypeFamilies,
             RankNTypes, TypeOperators, LambdaCase, TypeHoles, EmptyCase #-}

import Prelude hiding (Maybe(..))
import Data.Singletons

$(singletons [d|
  data Nat = Zero | Succ Nat deriving Show
  
  data Exp :: * where
    ENat :: Nat -> Exp
    EPlus :: Exp -> Exp -> Exp
    EBool :: Bool -> Exp
    EAnd :: Exp -> Exp -> Exp

  data Type = TNat | TBool

  |])

data HasType :: Exp -> Type -> * where
  HtNat :: HasType (ENat n) TNat
  HtPlus :: HasType e1 TNat -> HasType e2 TNat -> HasType (EPlus e1 e2) TNat
  HtBool :: HasType (EBool b) TBool
  HtAnd :: HasType e1 TBool -> HasType e2 TBool -> HasType (EAnd e1 e2) TBool

data a :~: b where
  Refl :: a :~: a

data False
absurd :: False -> a
absurd = \case {}

type Refuted a = a -> False

type EqTypeDec t1 t2 = Either (Refuted (t1 :~: t2)) (t1 :~: t2)
eqTypeDec :: SType t1 -> SType t2 -> EqTypeDec t1 t2
eqTypeDec STNat STNat = Right Refl
eqTypeDec STNat STBool = Left (\case {})
eqTypeDec STBool STNat = Left (\case {})
eqTypeDec STBool STBool = Right Refl

data Maybe :: (k -> *) -> * where
  Unknown :: Maybe p
  Found :: Sing a -> p a -> Maybe p

data Or :: (k -> *) -> * where
  Holds :: Sing a -> p a -> Or p
  DoesntHold :: (forall a. Sing a -> Refuted (p a)) -> Or p

bind :: Maybe p -> (forall a. Sing a -> p a -> Maybe p') -> Maybe p'
bind e1 e2 = case e1 of
  Unknown -> Unknown
  Found x pf -> e2 x pf

obind :: Or p -> ((forall a. Sing a -> Refuted (p a)) -> Or p')
      -> (forall a. Sing a -> p a -> Or p') -> Or p'
obind e1 no yes = case e1 of
  Holds x pf -> yes x pf
  DoesntHold pf -> no pf

bind' :: EqTypeDec t1 t2 -> (t1 ~ t2 => Maybe p) -> Maybe p
bind' e1 e2 = case e1 of
  Right pf -> case pf of Refl -> e2
  Left _ -> Unknown

obind' :: EqTypeDec t1 t2 -> (Refuted (t1 :~: t2) -> Or p)
       -> (t1 ~ t2 => Or p) -> Or p
obind' e1 no yes = case e1 of
  Right pf -> case pf of Refl -> yes
  Left pf -> no pf

infixr 6 `bind'`
infixr 6 `obind'`

typeCheck :: SExp e -> Maybe (HasType e)
typeCheck e = case e of
  { SENat _ -> Found STNat HtNat
  ; SEPlus e1 e2 ->
      typeCheck e1 `bind` \t1 pf1 ->
      typeCheck e2 `bind` \t2 pf2 ->
      eqTypeDec t1 STNat `bind'`
      eqTypeDec t2 STNat `bind'`
      Found STNat (HtPlus pf1 pf2)
  ; SEBool _ -> Found STBool HtBool
  ; SEAnd e1 e2 ->
      typeCheck e1 `bind` \t1 pf1 ->
      typeCheck e2 `bind` \t2 pf2 ->
      eqTypeDec t1 STBool `bind'`
      eqTypeDec t2 STBool `bind'`
      Found STBool (HtAnd pf1 pf2) }

extractType :: HasType e t -> SType t
extractType HtNat = STNat
extractType (HtPlus _ _) = STNat
extractType HtBool = STBool
extractType (HtAnd _ _) = STBool

otypeCheck :: SExp e -> Or (HasType e)
otypeCheck e = case e of
  { SENat _ -> Holds STNat HtNat
  ; SEPlus e1 e2 ->
      obind (otypeCheck e1) (\contra -> DoesntHold (\a ht -> 
        case ht of { HtPlus t1 _ -> contra a t1 }
      )) $ \t1 pf1 ->
      obind (otypeCheck e2) (\contra -> DoesntHold (\a ht ->
        case ht of
          HtPlus _ t2 -> contra a t2
      )) $ \t2 pf2 ->
      case eqTypeDec t1 STNat of
      { Left contra -> case extractType pf1 of
          { STNat -> absurd $ contra Refl
          ; STBool -> DoesntHold $ \_ ht -> case ht of
            { HtPlus ht1 _ -> case ht1 of { } } }
      ; Right pf -> case pf of { Refl ->
      case eqTypeDec t2 STNat of
      { Left contra -> case pf2 of
        { HtNat -> absurd $ contra Refl
        ; HtPlus _ _ -> absurd $ contra Refl
        ; HtBool -> DoesntHold $ \_ ht -> case ht of
          { HtPlus ht1 _ -> case ht1 of { } }
        ; HtAnd _ _ -> DoesntHold $ \_ ht -> case ht of
          { HtPlus ht1 _ -> case ht1 of { } }
        }
      ; Right pf -> case pf of { Refl ->
      Holds STNat (HtPlus pf1 pf2)
      }}}}
  ; SEBool _ -> Holds STBool HtBool
  ; SEAnd e1 e2 ->
      obind (otypeCheck e1) (\contra -> DoesntHold (\a ht ->
        case ht of
          HtAnd t1 _ -> contra a t1
      )) $ \t1 pf1 ->
      obind (otypeCheck e2) (\contra -> DoesntHold (\a ht ->
        case ht of
          HtAnd _ t2 -> contra a t2
      )) $ \t2 pf2 ->
      case eqTypeDec t1 STBool of
      { Left contra -> case pf1 of
        { HtNat -> DoesntHold $ \_ ht -> case ht of
          { HtAnd ht1 _ -> case ht1 of { } }
        ; HtPlus _ _ -> DoesntHold $ \_ ht -> case ht of
          { HtAnd ht1 _ -> case ht1 of { } }
        ; HtBool -> absurd $ contra Refl
        ; HtAnd _ _ -> absurd $ contra Refl
        }
      ; Right pf -> case pf of { Refl ->
      case eqTypeDec t2 STBool of
      { Left contra -> case pf2 of
        { HtNat -> DoesntHold $ \_ ht -> case ht of
          { HtAnd ht1 _ -> case ht1 of { } }
        ; HtPlus _ _ -> DoesntHold $ \_ ht -> case ht of
          { HtAnd ht1 _ -> case ht1 of { } }
        ; HtBool -> absurd $ contra Refl
        ; HtAnd _ _ -> absurd $ contra Refl
        }
      ; Right pf -> case pf of { Refl ->
      Holds STBool (HtAnd pf1 pf2) }}}}}