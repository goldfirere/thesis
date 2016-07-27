-- based on implementation in Idris's standard library

{-# LANGUAGE TypeInType, TypeOperators, MultiParamTypeClasses,
             AllowAmbiguousTypes, FlexibleInstances, TypeFamilies #-}

module Control.Catchable where

import Data.Singletons
import Data.Kind
import Data.AChar
import Prelude hiding ( String, show )
import System.IO.Error

class Catchable (m :: Type ~> Type) t where
  throw :: (DemoteRep a ~ a, SingKind a) => t -> m @@ a
  catch :: m @@ a -> (t -> m @@ a) -> m @@ a

instance Catchable (TyCon1 Maybe) () where
  catch Nothing  h = h ()
  catch (Just x) _ = Just x

  throw () = Nothing

instance Catchable (TyCon1 (Either a)) a where
  catch (Left err) h = h err
  catch (Right x)  _ = Right x

  throw x = Left x

instance Catchable (TyCon1 []) () where
  catch [] h = h ()
  catch xs _ = xs

  throw () = []

instance Catchable (TyCon1 IO) String where
  throw s = ioError (userError (toString s))
  catch io k = catchIOError io (\err -> k (show err))
