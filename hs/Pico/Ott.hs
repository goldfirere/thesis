{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-pattern-binds #-}

module Pico.Ott where

import Data.Char
import Data.List

import Language.Haskell.TH

-- Deal with ott's list output
app :: [a] -> [a] -> [a]
app = (++)

cons :: a -> [a] -> [a]
cons = (:)

nil :: [a]
nil = []

-- trim spaces off literals
trim :: String -> String
trim = dropWhileEnd isSpace .
       dropWhile isSpace

list :: String  -- prefix of function names
     -> Q Type  -- type of element
     -> Q [Dec]
list prefix ty = do
  let one  = mkName (prefix ++ "_One")
      many = mkName (prefix ++ "_Many")
      nil  = mkName (prefix ++ "_Nil")

  ty_one  <- [t| $ty -> [$ty] |]
  ty_many <- [t| [[$ty]] -> [$ty] |]
  ty_nil  <- [t| [$ty] |]

  value_decs <- [d| $(varP one) = (:[])
                    $(varP many) = concat
                    $(varP nil)  = [] |]

  return ( SigD one  ty_one
         : SigD many ty_many
         : SigD nil  ty_nil
         : value_decs )
