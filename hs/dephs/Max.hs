{-# LANGUAGE TemplateHaskell, PolyKinds, DataKinds, TypeFamilies, GADTs,
             ScopedTypeVariables, TypeOperators, UndecidableInstances,
             FlexibleContexts, MultiParamTypeClasses, EmptyCase,
             RankNTypes, ConstraintKinds, ImpredicativeTypes #-}

module Max where

import Prelude hiding (max)
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Type.Equality
import GHC.Exts

$(singletons [d|
  data Nat = Zero | Succ Nat
  |])


$(singletonsOnly [d|
  elem :: Eq a => a -> [a] -> Bool
  elem _ [] = False
  elem x (x' : xs) = (x == x') || elem x xs

  (>=) :: Nat -> Nat -> Bool
  _ >= Zero = True
  Zero >= (Succ _) = False
  (Succ n) >= (Succ m) = n >= m

  gtList :: Nat -> [Nat] -> Bool
  gtList _ [] = True
  gtList x (n:ns) = x >= n && gtList x ns
  |])

data ElemPf :: Nat -> [Nat] -> * where
  ElemHere :: ElemPf n (n ': ns)
  ElemThere :: ElemPf n ns -> ElemPf n (n' ': ns)

class ElemC n ns where
  elemPf :: ElemPf n ns

data Ge :: Nat -> Nat -> * where
  GeZero :: Ge n Zero
  GeSucc :: Ge m n -> Ge (Succ m) (Succ n)

data GeListPf :: Nat -> [Nat] -> * where
  GeNil :: GeListPf n '[]
  GeCons :: Ge m n -> GeListPf m ns -> GeListPf m (n ': ns)

class GeListC n ns where
  geListPf :: GeListPf n ns

elemSingleton :: forall n singleton p1 p2. ElemC n '[singleton] => p1 n -> p2 '[singleton]
              -> n :~: singleton
elemSingleton _ _ = case elemPf :: ElemPf n '[singleton] of
                      ElemHere -> Refl
                      ElemThere pf -> case pf of {}
{-
max :: forall n ns. (ElemC n ns, GeListC n ns) => SList ns -> SNat n
max list@(SCons x SNil) = gcastWith (elemSingleton (Proxy :: Proxy n) list) x
max (SCons x xs) = let rest = max xs in
                   sIf (x %:>= rest) x rest
-}

type family NotNil ns where
  NotNil '[] = (True ~ False)
  NotNil (x ': xs) = (() :: Constraint)

data Ex :: (k -> *) -> * where
  MkEx :: a b -> Ex a

max :: forall (ns :: [Nat]). NotNil ns => SList ns -> Ex (Sing :: Nat -> *)
max (SCons x SNil) = MkEx x
{-
max = go SZero
  where
    go :: SNat m -> SList ms -> SNat m'
    go x SNil = x
    go x (n:ns) = go (sIf (x %:>= n) x n) ns
-}