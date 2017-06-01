{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeOperators, TypeFamilies,
             UndecidableInstances, ScopedTypeVariables, TypeInType #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module SystemF where

import Data.Kind
import Data.Type.Bool
import GHC.Exts ( Any )
import Data.Type.Equality

type family a ++ b where
  '[] ++ xs2 = xs2
  (x ': xs1) ++ xs2 = x ': (xs1 ++ xs2)
infixr 5 ++

data Nat = Zero | Succ Nat

type family Pred n where
  Pred ('Succ n) = n

data Fin n where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

type family (a :: x) <= (f :: Fin n) :: Bool where
  'Zero <= x       = 'True
  'FZ <= x         = 'True

  x  <= 'FZ         = 'False

  'Succ a <= 'FS b = a <= b
  'FS a   <= 'FS b = a <= b

type family (a :: Nat) `NPlus` (b :: Nat) where
  'Zero `NPlus` b = b
  'Succ a `NPlus` b = 'Succ (a `NPlus` b)

type family (a :: Nat) + (f :: Fin n) :: Fin (a `NPlus` n) where
  'Zero + f = f
  'Succ a + f = 'FS (a + f)

type family FPred (f :: Fin ('Succ n)) :: Fin n where
  FPred ('FS f) = f

type family WeakenFin (f :: Fin n) :: Fin ('Succ n) where
  WeakenFin 'FZ = 'FZ
  WeakenFin ('FS f) = 'FS (WeakenFin f)

type family WeakenFinN (n :: Nat) (f :: Fin m) :: Fin (n `NPlus` m) where
  WeakenFinN 'Zero f = f
  WeakenFinN ('Succ n) f = WeakenFin (WeakenFinN n f)

type family StrengthenFin (f :: Fin ('Succ n)) :: Fin n where
  StrengthenFin 'FZ = 'FZ
  StrengthenFin ('FS f) = 'FS (StrengthenFin f)

data SFin :: forall n. Fin n -> * where
  SFZ :: SFin 'FZ
  SFS :: SFin n -> SFin ('FS n)

data Ty n where
  TVar :: Fin n -> Ty n
  TForall :: Ty ('Succ n) -> Ty n
  (:~>) :: Ty n -> Ty n -> Ty n
infixr 0 :~>

data STy :: forall n. Ty n -> * where
  STVar :: SFin n -> STy ('TVar n)
  STForall :: STy ty -> STy ('TForall ty)
  (:%~>) :: STy t1 -> STy t2 -> STy (t1 ':~> t2)
infixr 0 :%~>

data Elem :: [a] -> a -> * where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

type family NPlus_Succ_R' (a :: Nat) (b :: Nat) (eq :: (a `NPlus` 'Succ b) :~: ('Succ (a `NPlus` b))) :: (('Succ a `NPlus` 'Succ b) :~: ('Succ ('Succ (a `NPlus` b)))) where
  NPlus_Succ_R' a b 'Refl = 'Refl

type family NPlus_Succ_R (a :: Nat) (b :: Nat) :: (a `NPlus` 'Succ b) :~: 'Succ (a `NPlus` b) where
  NPlus_Succ_R 'Zero b = 'Refl
--  NPlus_Succ_R ('Succ a) b = 'Refl

type family TShift (cutoff :: Nat) (shift :: Nat) (ty :: Ty n) :: Ty (shift `NPlus` n) where
  TShift cutoff shift ('TVar f)
    = If (cutoff <= f) ('TVar (shift + f)) ('TVar (WeakenFinN shift f))
--  TShift cutoff shift ('TForall ty) = 'TForall (TShift ('Succ cutoff) shift ty)
--  TShift cutoff shift (a ':~> b) = (TShift shift cutoff a) ':~> (TShift shift cutoff b)
{-
type family TShiftCtx (shift :: Nat) (tys :: [Ty n]) :: [Ty ('Succ n)] where
  TShiftCtx shift '[] = '[]
  TShiftCtx shift (ty ': tys) = (TShift 'Zero shift ty ': TShiftCtx tys)

type family TSubst (var :: Fin ('Succ n1))
                   (inner_ty :: Ty n1)
                   (outer_ty :: Ty ('Succ n1))
                   :: Ty n1 where
  TSubst var inner_ty ('TVar var) = inner_ty
  TSubst var inner_ty ('TVar var') = 'TVar (If (var <= var') (FPred var') (BumpFinDown var'))
  TSubst var inner_ty ('TForall ty) = 'TForall (TSubst ('FS var) (TShift 'Zero inner_ty) ty)
  TSubst var inner_ty (a ':~> b) = TSubst var inner_ty a ':~> TSubst var inner_ty b

data Expr :: [Ty n] -> Ty n -> * where
  Var :: Elem ctx ty -> Expr ctx ty
  Abs :: Expr (arg ': ctx) res -> Expr ctx (arg ':~> res)
  App :: Expr ctx (arg ':~> res) -> Expr ctx arg -> Expr ctx res
  TAbs :: Expr (TShiftCtx ('Succ 'Zero) ctx) ty -> Expr ctx ('TForall ty)
  TApp :: Expr ctx ('TForall res) -> STy arg -> Expr ctx (TSubst 'FZ arg res)

data Length :: [a] -> * where
  LZ :: Length '[]
  LS :: Length xs -> Length (x ': xs)

tshift :: Expr ctx ty -> Expr

shift :: forall ctx ty x. Expr ctx ty -> Expr (x ': ctx) ty
shift = go LZ
  where
    go :: forall ctx0 ty. Length ctx0
       -> Expr (ctx0 ++ ctx) ty -> Expr (ctx0 ++ x ': ctx) ty
    go ctx0 (Var v) = Var (shift_var ctx0 v)
    go ctx0 (Abs body) = Abs (go (LS ctx0) body)
    go ctx0 (App e1 e2) = App (go ctx0 e1) (go ctx0 e2)
    go ctx0 (TAbs body) = TAbs (_ (go ctx0 body))

    shift_var :: forall ctx0 ty. Length ctx0
              -> Elem (ctx0 ++ ctx) ty -> Elem (ctx0 ++ x ': ctx) ty
    shift_var LZ e = ES e
    shift_var (LS _) EZ = EZ
    shift_var (LS ctx0') (ES e') = ES (shift_var ctx0' e')
-}
