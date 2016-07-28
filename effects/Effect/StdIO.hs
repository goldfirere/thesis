-- Adapted from Brady's implementation in Idris

{-# LANGUAGE TypeInType, RebindableSyntax, GADTs, TypeFamilies,
             FlexibleInstances, MultiParamTypeClasses,
             LambdaCase, OverloadedStrings, ScopedTypeVariables,
             InstanceSigs, FlexibleContexts, TypeApplications,
             AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Effect.StdIO where

import Data.AChar
import qualified Prelude as P
import Data.Singletons
import Effects

data StdIO :: Effect where
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

instance Handler StdIO P.IO where
  handle (PutStr s) () k = P.putStr (toString s) P.>>
                           k () ()
  handle GetStr     () k = P.getLine P.>>= \ s ->
                           k () (fromString s)

data IOStream a = MkStream ([String] -> (a, [String]))

instance Handler StdIO IOStream where
  handle (PutStr s) () k
    = MkStream (\x -> case k () () of
                        MkStream f -> let (res, str) = f x in
                                      (res, s : str))
  handle GetStr () k
    = MkStream (\case []     -> cont "" []
                      t : ts -> cont t ts)
    where
      cont t ts = case k () t of
        MkStream f -> f ts

type STDIO = MkEff () StdIO

putStr_ :: String -> Eff e '[STDIO] ()
putStr_ s = case toSing s of SomeSing s' -> Effect SHere (SPutStr s')

putStr :: forall xs prf e.
          SingI (prf :: SubList '[STDIO] xs)
       => String -> EffM e xs (UpdateWith '[STDIO] xs prf) ()
putStr s = lift @_ @_ @prf (putStr_ s)

putStrLn_ :: String -> Eff e '[STDIO] ()
putStrLn_ s = case toSing (s P.++ [Cnewline]) of
                SomeSing s' -> Effect SHere (SPutStr s')

putStrLn :: forall xs prf e.
            SingI (prf :: SubList '[STDIO] xs)
         => String -> EffM e xs (UpdateWith '[STDIO] xs prf) ()
putStrLn s = lift @_ @_ @prf (putStrLn_ s)

getStr_ :: Eff e '[STDIO] String
getStr_ = Effect SHere SGetStr

getStr :: forall xs prf e.
          SingI (prf :: SubList '[STDIO] xs)
       => EffM e xs (UpdateWith '[STDIO] xs prf) String
getStr = lift @_ @_ @prf getStr_

mkStrFn :: forall a xs.
           Env IOStream xs
        -> Eff IOStream xs a
        -> [String] -> (a, [String])
mkStrFn env p input = case mkStrFn' of MkStream f -> f input
  where
    injStream :: a -> IOStream a
    injStream v = MkStream (\_ -> (v, []))

    mkStrFn' :: IOStream a
    mkStrFn' = runWith injStream env p
