-- Adapted from Brady's implementation in Idris

{-# LANGUAGE TypeInType, RebindableSyntax, GADTs, TypeFamilies,
             FlexibleInstances, MultiParamTypeClasses,
             LambdaCase, OverloadedStrings, ScopedTypeVariables,
             InstanceSigs, FlexibleContexts, TypeApplications,
             AllowAmbiguousTypes #-}

module Effect.StdIO where

import Data.AChar
import Data.Kind
import qualified Prelude as P
import Data.Singletons
import Effects

data StdIO :: Type -> Type -> Type -> Type where
  PutStr :: String -> StdIO () () ()
  GetStr :: StdIO () () String

data instance Sing (x :: StdIO a b c) where
  SPutStr :: Sing s -> Sing (PutStr s)
  SGetStr :: Sing GetStr

instance (Good a, Good b, Good c) => SingKind (StdIO a b c) where
  type DemoteRep (StdIO a b c) = StdIO a b c

  fromSing (SPutStr s) = PutStr (fromSing s)
  fromSing SGetStr = GetStr

  toSing (PutStr s) = case toSing s of SomeSing s' -> SomeSing (SPutStr s')
  toSing GetStr = SomeSing SGetStr

instance Handler (TyCon3 StdIO) (TyCon1 P.IO) where
  handle (PutStr s) () k = P.putStr (toString s) P.>>
                           k () ()
  handle GetStr     () k = P.getLine P.>>= \ s ->
                           k () (fromString s)

data IOStream a = MkStream ([String] -> (a, [String]))

instance Handler (TyCon3 StdIO) (TyCon1 IOStream) where
  handle :: forall a res res' t.
            StdIO res res' t -> res -> (res' -> t -> IOStream a) -> IOStream a
  handle (PutStr s) () k
    = MkStream (\x -> case k () () of
                        MkStream f -> let (res, str) = f x in
                                      (res, s : str))
  handle GetStr () k
    = MkStream (\case []     -> cont "" []
                      t : ts -> cont t ts)
    where
      cont :: String -> [String] -> (a, [String])
      cont t ts = case k () t of
        MkStream f -> f ts

type STDIO = MkEff () (TyCon3 StdIO)

putStr_ :: Handler (TyCon3 StdIO) e => String -> Eff e '[STDIO] ()
putStr_ s = case toSing s of SomeSing s' -> effect SHere (SPutStr s')

putStr :: forall xs prf e.
          (SingI (prf :: SubList '[STDIO] xs), Handler (TyCon3 StdIO) e)
       => String -> EffM e xs (UpdateWith '[STDIO] xs prf) ()
putStr s = lift @_ @_ @prf (putStr_ s)

putStrLn_ :: Handler (TyCon3 StdIO) e => String -> Eff e '[STDIO] ()
putStrLn_ s = case toSing (s P.++ [Cnewline]) of
                SomeSing s' -> effect SHere (SPutStr s')

putStrLn :: forall xs prf e.
          (SingI (prf :: SubList '[STDIO] xs), Handler (TyCon3 StdIO) e)
       => String -> EffM e xs (UpdateWith '[STDIO] xs prf) ()
putStrLn s = lift @_ @_ @prf (putStrLn_ s)

getStr_ :: Handler (TyCon3 StdIO) e => Eff e '[STDIO] String
getStr_ = effect SHere SGetStr

getStr :: forall xs prf e.
          (SingI (prf :: SubList '[STDIO] xs), Handler (TyCon3 StdIO) e)
       => EffM e xs (UpdateWith '[STDIO] xs prf) String
getStr = lift @_ @_ @prf getStr_

mkStrFn :: forall a xs.
           Env (TyCon1 IOStream) xs
        -> Eff (TyCon1 IOStream) xs a
        -> [String] -> (a, [String])
mkStrFn env p input = case mkStrFn' of MkStream f -> f input
  where
    injStream :: a -> IOStream a
    injStream v = MkStream (\_ -> (v, []))

    mkStrFn' :: IOStream a
    mkStrFn' = runWith injStream env p

type Stdio = TyCon3 StdIO
