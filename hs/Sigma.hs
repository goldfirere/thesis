{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds, GADTs, TypeOperators,
             ScopedTypeVariables, TemplateHaskell, FlexibleInstances,
             ConstraintKinds, UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module Sigma where

import Data.Type.Equality
import Data.Proxy
import GHC.Exts

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

instance SingKind Nat where
  type FromSing 'SZero = 'Zero
  type FromSing ('SSucc x) = 'Succ (FromSing x)

  type ToSing 'Zero = 'SZero
  type ToSing ('Succ x) = 'SSucc (ToSing x)

  fromSing SZero = Zero
  fromSing (SSucc x) = Succ (fromSing x)

  fromSingCorrect (Sing SZero) = Refl
  fromSingCorrect (Sing (SSucc x)) = case fromSingCorrect (Sing x) of
    Refl -> Refl

instance SingKind k => SingKind (Maybe k) where
  type FromSing 'SNothing = 'Nothing
  type FromSing ('SJust x) = 'Just (FromSing x)

  type ToSing 'Nothing = 'SNothing
  type ToSing ('Just x) = 'SJust (ToSing x)

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
