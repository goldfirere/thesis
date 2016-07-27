-- produces the source code to paste into Data.AChar

module Util.MkChar where

import Control.Monad

allChars = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['_']

mkCon :: Char -> IO ()
mkCon c = putStrLn ("| C" ++ [c])

mkCons :: IO ()
mkCons =  mapM_ mkCon allChars

mkToChar :: IO ()
mkToChar =
  forM_ allChars $ \c -> putStrLn ("toChar C" ++ c : " = '" ++ c : "'")

mkFromChar :: IO ()
mkFromChar =
  forM_ allChars $ \c -> putStrLn ("fromChar '" ++ c : "' = C" ++ [c])
