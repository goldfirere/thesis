-- Attempt at using injectivity to prove false. It fails because
-- GADT pattern matching in types is wobbly.

{-# LANGUAGE TypeOperators, GADTs, UnicodeSyntax, TypeInType,
             TypeFamilies, ScopedTypeVariables, AllowAmbiguousTypes,
             TypeFamilyDependencies, NoImplicitPrelude,
             UndecidableInstances, TemplateHaskell,
             TypeApplications #-}
{-# OPTIONS_GHC -Wunticked-promoted-constructors #-}

module Injectivity where

import Prelude ( return )
import Data.Kind
-- import Data.Proxy
-- import Data.Type.Equality

type family Any :: k

bot :: ∀ a. a
bot = bot

data TyFun a b
type a ~> b = TyFun a b → *

type family (f :: a ~> b) @@ (x :: a) :: b

type family Sing (a :: k) = (r :: *) | r -> k

data a ≡ b where
  Refl :: a ≡ a

data SEq :: ∀ k (a :: k) (b :: k). a ≡ b → * where
  SRefl :: SEq 'Refl

cast :: a ≡ b → a → b
cast Refl x = x

type family Cast (p :: a ≡ b) (x :: a) :: b where
  Cast 'Refl x = x

data HEq (a :: k1) (b :: k2) where
  HRefl :: HEq a a

mkHet :: ∀ k1 k2 (p :: k1 ≡ k2) (a :: k1).
         SEq p -> HEq a (Cast p a)
mkHet SRefl = HRefl

data SING :: (* ~> *) → * where
  Sing :: SING f

thm :: ∀ (f :: * ~> *) (g :: * ~> *) (a :: SING f) (b :: SING g).
       HEq a b → f ≡ g
thm HRefl = Refl

singInj :: ∀ (f :: * ~> *) (g :: * ~> *). SING f ≡ SING g → f ≡ g
singInj Refl = Refl

data Either a b where
  Inl :: a -> Either a b
  Inr :: b -> Either a b

data SEither :: Either a b -> * where
  SInl :: Sing a -> SEither ('Inl a)
  SInr :: Sing a -> SEither ('Inr a)

data Inv a where
  InvK :: ∀ (a :: *) (f :: * ~> *). SING f ≡ a → Inv a

data Void

type Not a = a → Void

em :: Either a (Not a)
em = bot

type family Em a :: Either a (Not a)

sEm :: ∀ a (e :: Either a (Not a)). SEither e
sEm = bot

type family Cantor' a (x :: Either (Inv a) (Not (Inv a))) :: * where
  Cantor' a ('Inl ('InvK (pf :: SING f ≡ a))) = Not (f @@ a)
  Cantor' a ('Inr x) = ()

type Cantor a = Cantor' a (Em (Inv a))

data CantorSym0 :: * ~> *
type instance CantorSym0 @@ a = Cantor a

type C = SING CantorSym0

-- ic :: Inv C
type IC = ('InvK ('Refl :: C ≡ C) :: Inv C)

cast' :: SING f ≡ SING g → Not (f @@ C) → Not (g @@ C)
cast' Refl x = x

type family Cast' (eq :: SING f ≡ SING g) (x :: Not (f @@ C)) :: Not (g @@ C) where
  Cast' 'Refl x = x

$(return [])
{-
type family Diag (c :: Cantor C) :: Void where
  Diag c = Diag1 c (Em (Inv C))

type family Diag1 (c :: Cantor C) (e :: Either (Inv C) (Not (Inv C)))
                  (dep :: e ≡ Em (Inv C)) :: Void where
  Diag1 c ('Inl ('InvK eq)) 'Refl = Cast' eq c c
   -- This doesn't work, of course, because type families in GHC 8 can't
   -- really assume equalities.
-}

diag :: Not (Cantor C)
diag c = case sEm @(Inv C) of
  SInl (InvK eq) -> cast' eq c c
