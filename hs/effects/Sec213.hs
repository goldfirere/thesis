-- Adapted from Brady's ICFP '13 paper.

{-# LANGUAGE TypeInType, RebindableSyntax, OverloadedStrings,
             FlexibleContexts #-}

module Sec213 where

import qualified Prelude as P
import Data.AChar
import Data.Nat
import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO
import Effects
import Prelude ( Maybe(..), (++), lookup, (<$>), (<*>) )

type Vars = [(String, Nat)]

data Expr = Val Nat | Add Expr Expr | Var String | Random Nat

eval :: Expr -> Eff m '[EXCEPTION String, RND, STATE Vars] Nat
eval (Val x) = return x
eval (Var x) = do vs <- get
                  case lookup x vs of
                    Nothing  -> raise ("Unknown var: " ++ x)
                    Just val -> return val
eval (Add l r) = (+) <$> eval l <*> eval r
eval (Random upper) = rndNat 0 upper

eval' :: Handler Stdio e
      => Expr -> Eff e '[EXCEPTION String, STDIO, RND, STATE Vars] Nat
eval' (Val x) = return x
eval' (Var x) = do vs <- get
                   case lookup x vs of
                     Nothing  -> raise ("Unknown var: " ++ x)
                     Just val -> return val
eval' (Add l r) = (+) <$> eval' l <*> eval' r
eval' (Random upper) = do num <- rndNat 0 upper
                          putStrLn ("Random value: " P.++ show num)
                          return num

runEval :: Vars -> Expr -> Maybe Nat
runEval env expr = run (() :> 123 :> env :> Empty) (eval expr)

runEval' :: Vars -> Expr -> P.IO Nat
runEval' env expr = run (() :> () :> 123 :> env :> Empty) (eval' expr)

vars :: Vars
vars = [("x", 13), ("y", 5)]

go :: Expr -> Maybe Nat
go = runEval vars

go' :: Expr -> P.IO Nat
go' = runEval' vars

expr1 :: Expr
expr1 = Val 42

expr2 :: Expr
expr2 = Val 2 `Add` Val 5

expr3 :: Expr
expr3 = Var "x"

expr4 :: Expr
expr4 = Var "z"

expr5 :: Expr
expr5 = Random 10

expr6 :: Expr
expr6 = Val 100 `Add` Random 10 `Add` Random 10
