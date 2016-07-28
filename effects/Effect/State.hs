-- adapted from Idris's algebraic effects library

{-# LANGUAGE TypeInType, TypeOperators, GADTs, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies, ScopedTypeVariables,
             InstanceSigs, TypeApplications, RebindableSyntax,
             AllowAmbiguousTypes, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Effect.State where

import Effects
import Data.Singletons

data State :: Effect where
  Get :: State a a a
  Put :: b -> State a b ()

data instance Sing (e :: State a b c) where
  SGet :: Sing Get
  SPut :: Sing x -> Sing (Put x)

instance (Good a, Good b, Good c) => SingKind (State a b c) where
  type DemoteRep (State a b c) = State a b c

  fromSing SGet = Get
  fromSing (SPut x) = Put (fromSing x)

  toSing Get = SomeSing SGet
  toSing (Put x) = case toSing x of SomeSing x' -> SomeSing (SPut x')

instance Handler State m where
  handle Get     st k = k st st
  handle (Put n) _  k = k n ()

type STATE t = MkEff t State

get_ :: forall m x. Good x => Eff m '[STATE x] x
get_ = Effect SHere SGet

get :: forall x xs prf m.
       (SingI (prf :: SubList '[STATE x] xs), Good x)
    => EffM m xs (UpdateWith '[STATE x] xs prf) x
get = lift @_ @_ @prf get_

put_ :: forall x m. Good x => x -> Eff m '[STATE x] ()
put_ v = case toSing v of
  SomeSing v' -> Effect SHere (SPut v')

put :: forall x xs prf m.
       (SingI (prf :: SubList '[STATE x] xs), Good x)
    => x -> EffM m xs (UpdateWith '[STATE x] xs prf) ()
put v = lift @_ @_ @prf (put_ v)

putM_ :: forall x y m. (Good x, Good y) => y -> EffM m '[STATE x] '[STATE y] ()
putM_ val = case toSing val of
  SomeSing val' -> Effect SHere (SPut val')

putM :: forall x xs prf y m.
        (SingI (prf :: SubList '[STATE x] xs), Good x, Good y)
     => y -> EffM m xs (UpdateWith '[STATE y] xs prf) ()
putM y = lift @_ @_ @prf (putM_ y)

update_ :: Good x => (x -> x) -> Eff m '[STATE x] ()
update_ f = do x <- get
               put_ (f x)

update :: forall x xs prf m.
          (SingI (prf :: SubList '[STATE x] xs), Good x)
       => (x -> x) -> EffM m xs (UpdateWith '[STATE x] xs prf) ()
update f = lift @_ @_ @prf (update_ f)

updateM_ :: (Good x, Good y) => (x -> y) -> EffM m '[STATE x] '[STATE y] ()
updateM_ f = do x <- get
                putM_ (f x)

updateM :: forall x xs prf y m.
           (SingI (prf :: SubList '[STATE x] xs), Good x, Good y)
        => (x -> y) -> EffM m xs (UpdateWith '[STATE y] xs prf) ()
updateM f = lift @_ @_ @prf (updateM_ f)

locally_ :: (Good x, Good y) => x -> Eff m '[STATE x] t -> Eff m '[STATE y] t
locally_ newst prog = do st <- get_
                         putM_ newst
                         val <- prog
                         putM_ st
                         return val

locally :: forall y xs prf x m t.
           (SingI (prf :: SubList '[STATE y] xs), Good x, Good y)
        => x -> Eff m '[STATE x] t -> EffM m xs (UpdateWith '[STATE y] xs prf) t
locally newst prog = lift @_ @_ @prf (locally_ newst prog)
