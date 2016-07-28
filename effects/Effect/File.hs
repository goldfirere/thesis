-- Based on Idris's algebraic effects library

{-# LANGUAGE TypeInType, GADTs, FlexibleInstances, MultiParamTypeClasses,
             TemplateHaskell, ScopedTypeVariables, TypeFamilies,
             FlexibleContexts, TypeApplications, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Effect.File where

import Effects
import System.IO
import System.IO.Error
import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.AChar
import Prelude ( Either(..), Bool(..), IO )

$(singletons [d| data Mode = Read | Write |])

toIOMode :: Mode -> IOMode
toIOMode Read = ReadMode
toIOMode Write = WriteMode

data OpenFile :: Mode -> Type where
  FH :: Handle -> OpenFile m

data FileIO :: Type -> Type -> Type -> Type where
  OpenRead :: String -> FileIO () (Either () (OpenFile Read)) Bool
  OpenWrite :: String -> FileIO () (Either () (OpenFile Write)) Bool
  Close :: FileIO (OpenFile m) () ()
  ReadLine :: FileIO (OpenFile Read) (OpenFile Read) String
  WriteLine :: String -> FileIO (OpenFile Write) (OpenFile Write) ()
  EOF :: FileIO (OpenFile Read) (OpenFile Read) Bool

data instance Sing (x :: FileIO a b c) where
  SOpenRead :: Sing s -> Sing (OpenRead s)
  SOpenWrite :: Sing s -> Sing (OpenWrite s)
  SClose :: Sing Close
  SReadLine :: Sing ReadLine
  SWriteLine :: Sing s -> Sing (WriteLine s)
  SEOF :: Sing EOF

instance SingKind (FileIO a b c) where
  type DemoteRep (FileIO a b c) = FileIO a b c

  fromSing (SOpenRead s) = OpenRead (fromSing s)
  fromSing (SOpenWrite s) = OpenWrite (fromSing s)
  fromSing SClose = Close
  fromSing SReadLine = ReadLine
  fromSing (SWriteLine s) = WriteLine (fromSing s)
  fromSing SEOF = EOF

  toSing (OpenRead s) = case toSing s of SomeSing s' -> SomeSing (SOpenRead s')
  toSing (OpenWrite s) = case toSing s of SomeSing s' -> SomeSing (SOpenWrite s')
  toSing Close = SomeSing SClose
  toSing ReadLine = SomeSing SReadLine
  toSing (WriteLine s) = case toSing s of SomeSing s' -> SomeSing (SWriteLine s')
  toSing EOF = SomeSing SEOF

handleOpen :: FilePath -> Sing (m :: Mode)
           -> (Either () (OpenFile m) -> Bool -> IO r)
           -> IO r
handleOpen fname mode k = do e_h <- tryIOError (openFile fname (toIOMode (fromSing mode)))
                             case e_h of
                               Left _err -> k (Left ()) False
                               Right h   -> k (Right (FH h)) True

instance Handler FileIO IO where
  handle (OpenRead s) () k = handleOpen (toString s) SRead k
  handle (OpenWrite s) () k = handleOpen (toString s) SWrite k

  handle Close (FH h) k = do hClose h
                             k () ()
  handle ReadLine (FH h) k = do str <- hGetLine h
                                k (FH h) (fromString str)
  handle (WriteLine str) (FH h) k = do hPutStrLn h (toString str)
                                       k (FH h) ()
  handle EOF (FH h) k = do b <- hIsEOF h
                           k (FH h) b

type FILE_IO t = MkEff t FileIO

open_ :: String -> Sing (m :: Mode)
      -> EffM e '[FILE_IO ()] '[FILE_IO (Either () (OpenFile m))] Bool
open_ f SRead = case toSing f of SomeSing f' -> Effect SHere (SOpenRead f')
open_ f SWrite = case toSing f of SomeSing f' -> Effect SHere (SOpenWrite f')

open :: forall xs prf m e.
        (SingI (prf :: SubList '[FILE_IO ()] xs))
     => String -> Sing (m :: Mode)
     -> EffM e xs (UpdateWith '[FILE_IO (Either () (OpenFile m))] xs prf) Bool
open s m = lift @_ @_ @prf (open_ s m)

close_ :: EffM e '[FILE_IO (OpenFile m)] '[FILE_IO ()] ()
close_ = Effect SHere SClose

close :: forall xs m prf e.
         SingI (prf :: SubList '[FILE_IO (OpenFile m)] xs)
      => EffM e xs (UpdateWith '[FILE_IO ()] xs prf) ()
close = lift @_ @_ @prf close_

readLine_ :: Eff e '[FILE_IO (OpenFile Read)] String
readLine_ = Effect SHere SReadLine

readLine :: forall xs prf e.
            SingI (prf :: SubList '[FILE_IO (OpenFile Read)] xs)
         => EffM e xs (UpdateWith '[FILE_IO (OpenFile Read)] xs prf) String
readLine = lift @_ @_ @prf readLine_

writeLine_ :: String -> Eff e '[FILE_IO (OpenFile Write)] ()
writeLine_ s = case toSing s of SomeSing s' -> Effect SHere (SWriteLine s')

writeLine :: forall xs prf e.
             SingI (prf :: SubList '[FILE_IO (OpenFile Write)] xs)
          => String
          -> EffM e xs (UpdateWith '[FILE_IO (OpenFile Write)] xs prf) ()
writeLine s = lift @_ @_ @prf (writeLine_ s)

eof_ :: Eff e '[FILE_IO (OpenFile Read)] Bool
eof_ = Effect SHere SEOF

eof :: forall xs prf e.
       SingI (prf :: SubList '[FILE_IO (OpenFile Read)] xs)
    => EffM e xs (UpdateWith '[FILE_IO (OpenFile Read)] xs prf) Bool
eof = lift @_ @_ @prf eof_
