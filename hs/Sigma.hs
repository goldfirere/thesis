-- An attempt to write a Sigma type.
-- Fails because we can't have a type family application to the
-- left on a type family equation.

{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, GADTs, TypeOperators,
             ScopedTypeVariables, TemplateHaskell, FlexibleInstances,
             ConstraintKinds, UndecidableInstances, TypeInType #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Sigma where

import Data.Type.Equality
import Data.Proxy
import GHC.Exts
import Data.Kind

data family Sing (a :: k)

data Dict c where
  Dict :: c => Dict c

class SingKind k where
  type FromSing (s :: Sing (x :: k)) :: k
  type ToSing (a :: k) :: Sing a
  fromSing :: Sing (x :: k) -> k
  fromSingCorrect :: forall (x :: k) (s :: Sing x). Sing s -> (FromSing s :~: x)

class SingKind1 (t :: k -> *) where
  singKind :: forall (x :: k). Proxy (t x) -> Dict (SingKind (t x))

data Sigma (s :: *) (t :: s -> *) where
  (:&:) :: Sing (fst :: s) -> t fst -> Sigma s t

data instance Sing (x :: Sigma s t) where
  (:%&:) :: forall (s :: *) (t :: s -> *) (fst :: s) (snd :: t fst)
            (sfst :: Sing fst).
            Sing sfst -> Sing snd -> Sing (sfst ':&: snd)

data instance Sing (x :: Sing b) where
  Sing :: Sing x -> Sing (ToSing x)

data Nat = Zero | Succ Nat

data instance Sing (n :: Nat) where
  SZero :: Sing 'Zero
  SSucc :: Sing n -> Sing ('Succ n)

data instance Sing (x :: Maybe k) where
  SNothing :: Sing 'Nothing
  SJust    :: Sing a -> Sing ('Just a)

$(return [])

type family FromSingNat (n :: Sing (k :: Nat)) :: Nat where
  FromSingNat 'SZero = 'Zero
  FromSingNat ('SSucc x) = 'Succ (FromSingNat x)

type family ToSingNat (n :: Nat) :: Sing n where
  ToSingNat 'Zero = 'SZero
  ToSingNat ('Succ x) = 'SSucc (ToSingNat x)

instance SingKind Nat where
  type FromSing n = FromSingNat n
  type ToSing n = ToSingNat n

  fromSing SZero = Zero
  fromSing (SSucc x) = Succ (fromSing x)

  fromSingCorrect (Sing SZero) = Refl
  fromSingCorrect (Sing (SSucc x)) = case fromSingCorrect (Sing x) of
    Refl -> Refl

type family FromSingMaybe (n :: Sing (k :: Maybe k')) :: Maybe k' where
  FromSingMaybe 'SNothing = 'Nothing
  FromSingMaybe ('SJust x) = 'Just (FromSing x)

type family ToSingMaybe (x :: Maybe k) :: Sing x where
  ToSingMaybe 'Nothing = 'SNothing
  ToSingMaybe ('Just x) = 'SJust (ToSing x)

instance SingKind k => SingKind (Maybe k) where
  type FromSing x = FromSingMaybe x
  type ToSing x = ToSingMaybe x

  fromSing SNothing = Nothing
  fromSing (SJust x) = Just (fromSing x)

  fromSingCorrect (Sing SNothing) = Refl
  fromSingCorrect (Sing (SJust x)) = case fromSingCorrect (Sing x) of
    Refl -> Refl

instance SingKind k => SingKind (Sing (a :: k)) where
  type FromSing ('Sing x) = x

{-
instance (SingKind s, SingKind1 t) => SingKind (Sigma s t) where
  type FromSing (a ':%&: b) = FromSing a ':&: FromSing b
  type ToSing (a ':&: b) = ToSing a ':%&: ToSing b
  fromSing (a :%&: b) = fromSing a :&: fromSing b
  fromSingCorrect = undefined


proj1 :: SingKind s => Sigma s t -> s
proj1 (a :&: _) = fromSing a

type family Proj1 (x :: Sigma s t) :: s where
  Proj1 (a ':&: b) = FromSing a

proj2 :: forall (s :: *) (t :: s -> *) (sig :: Sigma s t).
         (SingKind s, SingKind1 t) =>
         Sing (sig :: Sigma s t) -> t (Proj1 sig)
proj2 (SAnd Sing a b)
  = case fromSingCorrect a Sing of
      Refl -> case singKind (Proxy :: Proxy (t (Proj1 sig))) of
        Dict -> fromSing b
-}
