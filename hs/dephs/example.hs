{-# LANGUAGE GADTs, DataKinds, PolyKinds, TemplateHaskell, TypeFamilies,
             ConstraintKinds #-}

import Data.Singletons

data Nat = O | S Nat

data Fin :: Nat -> * where
  First :: Fin (S n)
  Next :: Fin n -> Fin (S n)

data Vec :: * -> Nat -> * where
  VNil :: Vec a O
  VCons :: a -> Vec a n -> Vec a (S n)

type family Lookup (n :: Fin length) (v :: Vec a length) :: a
type instance Lookup First (VCons h t) = h
type instance Lookup (Next n') (VCons h t) = Lookup n' t

data Principal :: Vec Bool (S (S (S (S O)))) -> * where
  MkP :: String -> Principal caps

type CreateCap = First
type ReadCap = Next First
type UpdateCap = Next (Next First)
type DeleteCap = Next (Next (Next First))

type CanCreate caps = (Lookup CreateCap caps ~ True)
type CanRead caps = (Lookup ReadCap caps ~ True)
type CanUpdate caps = (Lookup UpdateCap caps ~ True)
type CanDelete caps = (Lookup DeleteCap caps ~ True)

data DbHandle
data DbData

readDb :: CanRead caps => Principal caps -> DbHandle -> IO DbData
readDb = undefined

updateDb :: CanUpdate caps => Principal caps -> DbHandle -> DbData -> IO ()
updateDb = undefined

readOnlyDb :: (Lookup CreateCap caps ~ False, Lookup UpdateCap caps ~ False,
               Lookup DeleteCap caps ~ False) => Principal caps -> IO a -> IO a
readOnlyDb = undefined

readUpdDb p handle = do
  dat <- readDb p handle
  updateDb p handle dat
--  readOnlyDb p undefined

