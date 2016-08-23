{-# LANGUAGE TemplateHaskell, PolyKinds, DataKinds, TypeFamilies, GADTs,
             RankNTypes, TypeOperators, UndecidableInstances #-}

import Data.Singletons
import Data.Typeable

data Nat = Zero | Succ Nat
data Vec :: * -> Nat -> * where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

--data SVec :: Vec * n -> * where
--  SVNil :: SVec VNil
--  SVCons :: Typeable a => SVec v -> SVec (VCons a v)

data Fin :: Nat -> * where
  First :: Fin (Succ n)
  Next :: Fin n -> Fin (Succ n)

{-
data SFin :: Fin n -> * where
  SFirst :: SFin First
  SNext :: SFin f -> SFin (Next f)
-}
{-
==>
Fin :: Nat -> *
First :: forall (n :: Nat). forall (n' :: Nat) (c :: n ~ Succ n'). Fin n
Next :: forall (n :: Nat). forall (n' :: Nat) (c :: n ~ Succ n'). Fin n' -> Fin n
SFin :: forall (n :: Nat). Fin n -> *
SFirst :: forall (n :: Nat) (f :: Fin n).
          forall (n' :: Nat) (c1 :: n ~ Succ n') (c2 :: f ~ First n n' c1)
-}
$(genSingletons [''Nat])

$(promote [d|
  lookup :: Fin n -> Vec a n -> a
  lookup First (VCons h _) = h
  lookup (Next n') (VCons _ t) = lookup n' t
  lookup _ _ = undefined
  |])

data Expr :: Nat -> * where
  Var :: Fin n -> Expr n
  Lam :: Expr (Succ n) -> Expr n
  App :: Expr n -> Expr n -> Expr n
{-
data SExpr :: Expr n -> * where
  SVar :: SFin f -> SExpr (Var f)
  SLam :: SExpr e -> SExpr (Lam e)
  SApp :: SExpr e1 -> SExpr e2 -> SExpr (App e1 e2)
-}

data In :: Vec * n -> Fin n -> * -> * where
--  InZ :: In (VCons t VNil) First t
--  InS :: In tail f t -> In (VCons h tail) (Next f) t

data HasType :: Vec * n -> Expr n -> * -> * where
  TVar :: In ctx f t -> HasType ctx (Var f) t
  TLam :: HasType (VCons t1 ctx) body t2 -> HasType ctx (Lam body) (t1 -> t2)
  TApp :: HasType ctx lam (t1 -> t2) -> HasType ctx arg t1 -> HasType ctx (App lam arg) t2

type family Length (v :: Vec a n) :: Nat
type instance Length VNil = Zero
type instance Length (VCons h t) = Succ (Length t)
{-
inToFin :: In ctx f t -> Fin (Length ctx)
--inToFin InZ = First
--inToFin (InS i) = Next (inToFin i)
inToFin = undefined

extractExpr :: HasType ctx e t -> Expr (Length ctx)
extractExpr (TVar inn) = Var (inToFin inn)
extractExpr (TLam ht') = Lam (extractExpr ht')
extractExpr (TApp ht1 ht2) = App (extractExpr ht1) (extractExpr ht2)

applies :: Expr n -> HasType ctx e t -> Bool
applies expr ht = expr == extractExpr ht
-}

{-
class SingI (a :: k) where
  sing :: Sing a

instance SingI '[] where
  sing = SNil

==>

Sing :: forall (k :: *). k -> *

SingI :: forall (k :: *). k -> Constraint
SingI_Con :: forall (k :: *) (a :: k). Sing k a -> SingI k a

singNilInst :: forall (k :: *). SingI [k] ('[] k)
singNilInst = \(k :: *) -> SingI_Con [k] ('[] k) (SNil k)

---

instance SingI First where
  sing = SFirst
instance SingI f => SingI (Next f) where
  sing = SNext sing


==>

SNat :: Nat -> *
SZero :: forall (n :: Nat). forall (c :: n ~ Zero). SNat n
SSucc :: forall (n :: Nat). forall (n' :: Nat) (c :: n ~ Succ n'). SNat n' -> SNat n

Fin :: Nat -> *
First :: forall (n :: Nat). forall (m :: Nat) (c :: n ~ Succ m). Fin n
Next :: forall (n :: Nat). forall (m :: Nat) (c :: n ~ Succ m). Fin m -> Fin n
SFin :: forall (n :: Nat). Fin n -> *
SFirst :: forall (n :: Nat) (f :: Fin n).
          forall (m :: Nat) (c1 :: n ~ Succ m) (c2 :: f ~ First n m c1).
          SFin n f
SNext :: forall (n :: Nat) (f :: Fin n).
         forall (m :: Nat) (c1 :: n ~ Succ m) (f' :: Fin m)
                (c2 :: f ~ Next n m c1 f').
         SFin m f' -> SFin n f

axSFin :: forall (n :: Nat). Sing (Fin n) ~ SFin n

singFirstInst :: forall (n :: Nat). SingI (Fin (Succ n)) (First (Succ n) n <Succ n>)
singFirstInst =
  \(n :: Nat). SingI_Con (Fin (Succ n)) (First (Succ n) n <Succ n>)
                         ((SFirst (Succ n) (First (Succ n) n <Succ n>)
                                  n <Succ n> <First (Succ n) n <Succ n>>) |>
                          (sym (axSFin (Succ n))) <First (Succ n) n <Succ n>>)

---

instance SingE (KindParam :: OfKind (Fin n)) where
  type DemoteRep (kparam :: OfKind (Fin n)) = Fin (DemoteRep (KindParam :: OfKind n))
  fromSing SFirst = First
  fromSing (SNext f) = Next (fromSing f)
-}