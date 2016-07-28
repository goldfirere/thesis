-- Adapted from Brady's ICFP '13 paper.

{-# LANGUAGE TypeInType, GADTs, FlexibleInstances, MultiParamTypeClasses,
             TypeFamilies, ScopedTypeVariables, AllowAmbiguousTypes,
             TypeApplications, FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors
                -Wno-orphans #-}
module Effect.Exception where

import Effects
import Data.Kind
import Data.Singletons
import Control.Catchable

data Exception :: Type -> Effect where
  Raise :: a -> Exception a () () b

data instance Sing (e :: Exception a b c d) where
  SRaise :: Sing x -> Sing (Raise x)

instance (Good a, Good b, Good c, Good d) => SingKind (Exception a b c d) where
  type DemoteRep (Exception a b c d) = Exception a b c d

  fromSing (SRaise x) = Raise (fromSing x)

  toSing (Raise x) = case toSing x of SomeSing x' -> SomeSing (SRaise x')

instance Handler (Exception a) Maybe where
  handle (Raise _) _ _ = Nothing

instance Show a => Handler (Exception a) IO where
  handle (Raise e) _ _ = ioError (userError (show e))

instance Handler (Exception a) (Either a) where
  handle (Raise e) _ _ = Left e

type EXCEPTION t = MkEff () (Exception t)

raise_ :: (Good a, Good b) => a -> Eff m '[EXCEPTION a] b
raise_ x = case toSing x of SomeSing x' -> Effect SHere (SRaise x')

raise :: forall a xs prf b m.
         (SingI (prf :: SubList '[EXCEPTION a] xs), Good a, Good b)
      => a -> EffM m xs (UpdateWith '[EXCEPTION a] xs prf) b
raise x = lift @_ @_ @prf (raise_ x)

instance ( Good s
         , Catchable m s
         , SFindableSubList '[EXCEPTION s] xs
         , xs' ~ UpdateWith '[EXCEPTION s] xs (SubListProof :: SubList '[EXCEPTION s] xs))
           => Catchable (EffM m xs xs') s where
  throw t = raise t
  catch e k = Catch e k
