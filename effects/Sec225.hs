-- Adapted from Brady's ICFP 2013 paper

{-# LANGUAGE TypeInType, RebindableSyntax, FlexibleContexts,
             OverloadedStrings, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Sec225 where

import Effects
import Effect.File
import Effect.StdIO
import Effect.Exception
import Control.Catchable
import qualified Prelude as P
import Prelude ( IO, not, reverse, (++), ($), FilePath
               , mapM_, map, length )
import Data.AChar
import Data.Singletons
import Util.If

readLines_ :: Eff IO '[FILE_IO (OpenFile Read)] [String]
readLines_ = readAcc []
  where
    -- readAcc :: [String] -> Eff IO '[FILE_IO (OpenFile Read)] [String]
    -- Haskell doesn't need this signature. :)
    readAcc acc = do e <- eof
                     if (not e)
                        then do str <- readLine
                                readAcc (str : acc)
                        else return (reverse acc)

readLines :: forall xs prf.
             SingI (prf :: SubList '[FILE_IO (OpenFile Read)] xs)
          => EffM IO xs (UpdateWith '[FILE_IO (OpenFile Read)] xs prf) [String]
readLines = lift @_ @_ @prf readLines_

readFile :: String -> Eff IO '[FILE_IO (), STDIO, EXCEPTION String] [String]
readFile path = catch (do _ <- open path SRead
                          Test SHere (raise ("Cannot open file: " ++ path)) $
                            do lines <- readLines
                               close @Read
                               putStrLn (show (length lines))
                               return lines)
                      (\ err -> do putStrLn ("Failed: " ++ err)
                                   return [])

printFile :: FilePath -> IO ()
printFile filepath
  = run (() :> () :> () :> Empty) (readFile (fromString filepath)) P.>>= \ls ->
    mapM_ P.putStrLn (map toString ls)
