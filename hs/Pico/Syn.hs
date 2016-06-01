-- An implementation of Pico.
-- Copyright (c) 2016 Richard Eisenberg

{-# LANGUAGE StandaloneDeriving, TemplateHaskell #-}

module Pico.Syn where

import Pico.Ott

type Unique = Int
data Var = Var String Unique
  deriving Show
            -- negative Uniques are wired-in
            -- non-negative ones are generated

instance Eq Var where
  Var _ u1 == Var _ u2 = u1 == u2

a, a0, a1, a2, a3, b, b1, b2, b3, x, x0, x1, x2, x3 :: Var
a = Var "a"     (-1)
a0 = Var "a0"   (-2)
a1 = Var "a1"   (-3)
a2 = Var "a2"   (-4)
a3 = Var "a3"   (-5)
b = Var "b"     (-6)
b0 = Var "b0"   (-7)
b1 = Var "b1"   (-8)
b2 = Var "b2"   (-9)
b3 = Var "b3"   (-10)
x = Var "x"     (-11)
x0 = Var "x0"   (-12)
x1 = Var "x1"   (-13)
x2 = Var "x2"   (-14)
x3 = Var "x3"   (-15)

type CoVar = Var
c, c0, c1, c2, c3 :: CoVar
c = Var "c"     (-16)
c0 = Var "c0"   (-17)
c1 = Var "c1"   (-18)
c2 = Var "c2"   (-19)
c3 = Var "c3"   (-20)

data ADT = ADT_Lit String
  deriving (Show, Eq)

data DataCon = DataCon_Lit String
  deriving (Show, Eq)

data Tycon = TyCon_ADT ADT
           | TyCon_DataCon DataCon
           | TyCon_Type
  deriving Show

data AdtKind = AdtKi_Vars [(Var,Type)]
  deriving Show

data ConType = ConTy_Pair Telescope Tycon
  deriving Show

data Relevance = Rel_Rel | Rel_Irrel
  deriving Show

data Bnd = Bnd_Type Var Relevance Type
         | Bnd_Coercion Var Prop
  deriving Show

data PI = Pi_Matchable | Pi_Unmatchable
  deriving Show

data Type = Type_Var Var
          | Type_TyCon Tycon [Type]
          | Type_App Type Argument
          | Type_Pi PI Bnd Type
          | Type_Cast Type Coercion
          | Type_Case Kind Type [Alt]
          | Type_Lam Bnd Type
          | Type_Fix Type
          | Type_Absurd Coercion Type
  deriving Show
type Kind = Type

data Alt = Alt_Alt Pat Type
  deriving Show

data Pat = Pat_Con Tycon
         | Pat_Default
  deriving Show

data Prop = Phi_Equality Type Kind Kind Type
  deriving Show

data Coercion = Co_Var Var
              | Co_Refl Type
              | Co_Sym Coercion
              | Co_Trans Coercion Coercion
              | Co_Coherence Type Coercion Type
              | Co_Con Tycon [Coercion]
              | Co_App Coercion CoArg
              | Co_PiTy PI Var Relevance Coercion Coercion
              | Co_PiCo PI CoVar Coercion Coercion Coercion
              | Co_Case Coercion Coercion [CAlt]
              | Co_Lam Var Relevance Coercion Coercion
              | Co_CLam CoVar Coercion Coercion Coercion
              | Co_Fix Coercion
              | Co_Absurd Coercion Coercion Coercion
              | Co_ArgK Coercion
              | Co_CArgK Int Coercion
              | Co_Res Int Coercion
              | Co_Inst Coercion CoArg
              | Co_InstLam Coercion CoArg
              | Co_Nth Int Coercion
              | Co_Kind Coercion
              | Co_Step Type
  deriving Show

data CAlt = CAlt_Alt Pat Coercion
  deriving Show

data Argument = Arg_Ty Type
              | Arg_IrrelTy Type
              | Arg_Co Coercion
  deriving Show

data CoArg = CoArg_Ty Coercion
           | CoArg_TyIrrel Coercion
           | CoArg_Co Coercion Coercion
  deriving Show

data SigBnd = SigBnd_ADT ADT AdtKind
            | SigBnd_Con DataCon ConType
  deriving Show

type Sig = [SigBnd]

type Context = [Bnd]
type Telescope = Context

data Subst = Subst_TyVar Type Var
           | Subst_CoVar Coercion CoVar
  deriving Show

list "vars"      [t| Var |]
list "mixedVars" [t| Var |]
list "types"     [t| Type |]
list "alts"      [t| Alt |]
list "cos"       [t| Coercion |]
list "calts"     [t| CAlt |]
list "args"      [t| Argument |]
list "coargs"    [t| CoArg |]
list "sig"       [t| SigBnd |]
list "ctx"       [t| Bnd |]
