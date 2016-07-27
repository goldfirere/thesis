module Util.If where

ifThenElse :: Bool -> a -> a -> a
ifThenElse b t f = if b then t else f
