-- adapted from Brady's ICFP 2013 paper

{-# LANGUAGE TypeInType, RebindableSyntax, TypeFamilies, GADTs,
             TypeOperators, ScopedTypeVariables, UndecidableInstances,
             TypeFamilyDependencies, FlexibleContexts,
             ConstraintKinds, TypeApplications #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors
                -Wno-name-shadowing #-}

module Sec4 where

import Data.Kind
import Data.Nat
import Prelude ( Bool(..), (<$>), (<*>), IO, ($), (==) )
import Effects
import Effect.Random
import Effect.State
import Data.Singletons.Prelude
import Effect.StdIO
import Data.AChar

data Ty = TyNat | TyBool | TyUnit

type family InterpTy (t :: Ty) = (r :: Type) | r -> t where
  InterpTy TyNat = Nat
  InterpTy TyBool = Bool
  InterpTy TyUnit = ()

data Vect :: Type -> Nat -> Type where
  Nil  :: Vect a Z
  (:&) :: a -> Vect a n -> Vect a (S n)
infixr 5 :&

type GoodTy t = Good (InterpTy t)

type family GoodCtx (g :: Vect Ty n) :: Constraint where
  GoodCtx Nil          = ()
  GoodCtx (ty :& rest) = (GoodTy ty, GoodCtx rest)

data HasType :: forall n. Nat -> Vect Ty n -> Ty -> Type where
  HTZ :: HasType (U 0) (ty :& g) ty
  HTS :: HasType n g ty -> HasType (S n) (ty' :& g) ty

data Expr :: Vect Ty n -> Ty -> Type where
  Val :: InterpTy a -> Expr g a
  Var :: HasType i g t -> Expr g t
  Rnd :: Nat -> Expr g TyNat
  Op  :: (InterpTy a -> InterpTy b -> InterpTy c)
      -> Expr g a -> Expr g b -> Expr g c

data Vars :: forall n. Vect Ty n -> Type where
  VNil :: Vars Nil
  (:^) :: InterpTy a -> Vars g -> Vars (a :& g)
infixr 5 :^

data instance Sing (x :: Vars y) where
  SVNil  :: Sing VNil
  SVCons :: Sing a -> Sing b -> Sing (a :^ b)

instance GoodCtx g => SingKind (Vars g) where
  type DemoteRep (Vars g) = Vars g

  fromSing SVNil = VNil
  fromSing (a `SVCons` b) = fromSing a :^ fromSing b

  toSing VNil = SomeSing SVNil
  toSing (a :^ b)
    = case toSing a of
        SomeSing a' -> case toSing b of
          SomeSing b' -> SomeSing (SVCons a' b')

lookup :: HasType i g t -> Vars g -> InterpTy t
lookup HTZ     (x :^ _) = x
lookup (HTS i) (_ :^ g) = lookup i g

eval :: GoodCtx g
     => Expr g t
     -> Eff m '[RND, STATE (Vars g)] (InterpTy t)
eval (Val x) = return x
eval (Var i) = do vars <- get
                  return (lookup i vars)
eval (Rnd upper) = rndNat 0 upper
eval (Op op x y) = op <$> eval x <*> eval y

data Imp :: forall n. Vect Ty n -> Ty -> Type where
  Let :: GoodTy t => Expr g t -> Imp (t :& g) u -> Imp g u
  (::=) :: HasType i g t -> Expr g t -> Imp g t
  Print :: Expr g TyNat -> Imp g TyUnit
  (:>>=) :: GoodTy a => Imp g a -> (InterpTy a -> Imp g b) -> Imp g b
  Return :: Expr g t -> Imp g t

(>>>) :: GoodTy a => Imp g a -> Imp g b -> Imp g b
p1 >>> p2 = p1 :>>= \_ -> p2

updateVar :: HasType i g t -> Vars g -> InterpTy t -> Vars g
updateVar HTZ     (_ :^ vars) x = x :^ vars
updateVar (HTS i) (a :^ vars) x = a :^ updateVar i vars x

interp :: forall g t. (GoodCtx g, GoodTy t)
       => Imp g t
       -> Eff IO '[STDIO, RND, STATE (Vars g)] (InterpTy t)
interp (Let (e :: Expr g t') sc)
  = do e' <- lift (eval e)
       vars <- get @(Vars g)
       putM @(Vars g) (e' :^ vars)
       res <- interp sc
       (_ :^ vars') <- get @(Vars (t' :& g))
       putM @(Vars (t' :& g)) vars'
       return res
interp (v ::= val)
  = do val' <- lift (eval val)
       update (\vars -> updateVar v vars val')
       return val'
interp (Print x)
  = do e <- lift (eval x)
       putStrLn (show e)
interp (prog :>>= k)
  = do x <- interp prog
       interp (k x)
interp (Return e)
  = lift (eval e)

prog :: Imp Nil TyUnit
prog = Let (Val 3) $
       Let (Val True) $
       Print (Var (HTS HTZ)) >>>
       (HTS HTZ ::= Op (+) (Var (HTS HTZ)) (Val 5)) >>>
       Print (Var (HTS HTZ)) >>>
       Print (Op (\() -> boolean) (Val ()) (Var HTZ)) >>>
       (HTS HTZ ::= Rnd 10) >>>
       Print (Var (HTS HTZ)) >>>
       Print (Var (HTS HTZ)) >>>
       (HTS HTZ ::= Rnd 9) >>>
       Print (Var (HTS HTZ)) >>>
       (HTZ ::= Op (\() -> isZero) (Val ()) (Var (HTS HTZ))) >>>
       Print (Op (\() -> boolean) (Val ()) (Var HTZ))
  where
    boolean :: Bool -> Nat
    boolean False = 0
    boolean True  = 1

    isZero 0 = True
    isZero _ = False

main :: IO ()
main = run (() :> 31 :> VNil :> Empty) (interp prog)
