
module FromPaper where

data TyRep :: k -> * where
  TyInt   :: TyRep Int
  TyMaybe :: TyRep Maybe
  TyApp   :: TyRep a -> TyRep b -> TyRep (a b)

zero :: forall (a :: *). TyRep a -> a
zero TyInt             = 0
zero (TyApp TyMaybe _) = Nothing

------------

data Kind = Star | Arr Kind Kind

data Ty :: Kind -> * where
  TInt   :: Ty Star
  TMaybe :: Ty (Arr Star Star)
  TApp   :: Ty (Arr k1 k2) -> Ty k1 -> Ty k2

data TyRep (k :: Kind) :: Ty k -> * where
  TyInt   :: TyRep Star TInt
  TyMaybe :: TyRep (Arr Star Star) TMaybe
  TyApp   :: TyRep (Arr k1 k2) a -> TyRep k1 b -> TyRep k2 (TApp a b)

type family IK k where
  IK Star = *
  IK (Arr k1 k2) = IK k1 -> IK k2

type family I (t :: Ty k) :: IK k where
  I TInt = Int
  I TMaybe = Maybe
  I (TApp a b) = (I a) (I b)

zero :: forall (a :: Ty Star). TyRep Star a -> I a
zero TyInt = 0
zero (TyApp TyMaybe _) = Nothing
