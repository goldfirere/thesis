-- Based on https://github.com/idris-lang/Idris-dev/blob/v0.9.10/libs/effects/Effects.idr

{-# LANGUAGE TypeOperators, TypeInType, GADTs, MultiParamTypeClasses,
             AllowAmbiguousTypes, TypeFamilies, ScopedTypeVariables,
             RebindableSyntax, MonadFailDesugaring, TypeApplications,
             FlexibleContexts, LambdaCase, EmptyCase, FlexibleInstances,
             ConstraintKinds, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors
                -Wno-name-shadowing #-}

module Effects where

import Data.Kind
import Data.Singletons.Prelude
import qualified Prelude as P
import Prelude ( Either(..), error,
                 Applicative(..), Functor(..), (<$>), Bool(..),
               )
import Control.Catchable

type Good x = (DemoteRep x ~ x, SingKind x)

type Effect = Type ~> Type ~> Type ~> Type

data EFFECT :: Type where
  MkEff :: Type -> Effect -> EFFECT

data instance Sing (x :: EFFECT) where
  SMkEff :: Sing t -> Sing e -> Sing (MkEff t e)

class Handler (e :: Effect) (m :: Type ~> Type) where
  handle :: forall a res res' t.
            e @@ res @@ res' @@ t -> res -> (res' -> t -> m @@ a) -> m @@ a

data SubList :: [a] -> [a] -> Type where
  SubNil :: SubList '[] '[]
  Keep :: SubList xs ys -> SubList (x ': xs) (x ': ys)
  Drop :: SubList xs ys -> SubList xs (x ': ys)

data instance Sing (x :: SubList ys xs) where
  SSubNil :: Sing SubNil
  SKeep   :: Sing x -> Sing (Keep x)
  SDrop   :: Sing x -> Sing (Drop x)

type SSubList = (Sing :: SubList (ys :: [a]) (xs :: [a]) -> Type)

instance SingKind (SubList ys xs) where
  type DemoteRep (SubList ys xs) = SubList ys xs

  fromSing SSubNil = SubNil
  fromSing (SKeep p) = Keep (fromSing p)
  fromSing (SDrop p) = Drop (fromSing p)

  toSing SubNil = SomeSing SSubNil
  toSing (Keep p) = case toSing p of SomeSing p' -> SomeSing (SKeep p')
  toSing (Drop p) = case toSing p of SomeSing p' -> SomeSing (SDrop p')

class FindableSubList xs ys where
  subListProof :: SubList xs ys

instance FindableSubList '[] '[] where
  subListProof = SubNil
instance FindableSubList xs ys => FindableSubList (x ': xs) (x ': ys) where
  subListProof = Keep subListProof
instance FindableSubList xs ys => FindableSubList xs (x ': ys) where
  subListProof = Drop subListProof

type family SubListProof :: SubList (xs :: [a]) (ys :: [a]) where
  SubListProof = SubNil
  SubListProof = Keep SubListProof
  SubListProof = Drop SubListProof

class SFindableSubList xs ys where
  sSubListProof :: Sing (SubListProof :: SubList xs ys)

instance SFindableSubList '[] '[] where
  sSubListProof = SSubNil
instance {-# OVERLAPPING #-}
         SFindableSubList xs ys => SFindableSubList (x ': xs) (x ': ys) where
  sSubListProof = SKeep sSubListProof
instance ( (SubListProof :: SubList xs (x ': ys)) ~ Drop SubListProof
         , SFindableSubList xs ys )
         => SFindableSubList xs (x ': ys) where
  sSubListProof = SDrop sSubListProof

instance (SFindableSubList xs ys, prf ~ SubListProof)
         => SingI (prf :: SubList xs ys) where
  sing = sSubListProof

subListId :: Sing xs -> SubList xs xs
subListId SNil = SubNil
subListId (_ `SCons` xs) = Keep (subListId xs)

data Env :: (Type ~> Type) -> [EFFECT] -> Type where
  Empty :: Env m '[]
  (:>) :: Handler eff m => a -> Env m xs -> Env m (MkEff a eff ': xs)
infixr 4 :>

data EffElem :: (Type ~> Type ~> Type ~> Type) -> Type -> [EFFECT] -> Type where
  Here :: EffElem x a (MkEff a x ': xs)
  There :: EffElem x a xs -> EffElem x a (y ': xs)

data instance Sing (elem :: EffElem x a xs) where
  SHere :: Sing Here
  SThere :: Sing z -> Sing (There z)

instance SingKind (EffElem x a xs) where
  type DemoteRep (EffElem x a xs) = EffElem x a xs

  fromSing SHere = Here
  fromSing (SThere p) = There (fromSing p)

  toSing Here = SomeSing SHere
  toSing (There p) = case toSing p of
    SomeSing p' -> SomeSing (SThere p')

class FindableElem x a xs where
  elemProof :: EffElem x a xs

instance FindableElem x a (MkEff a x ': xs) where
  elemProof = Here
instance FindableElem x a xs => FindableElem x a (y ': xs) where
  elemProof = There elemProof

type family ElemProof :: EffElem x a xs where
  ElemProof = Here
  ElemProof = There ElemProof

class SFindableElem x a xs where
  sElemProof :: Sing (ElemProof :: EffElem x a xs)

instance SFindableElem x a (MkEff a x ': xs) where
  sElemProof = SHere
instance {-# OVERLAPPABLE #-} ((ElemProof :: EffElem x a (y ': xs)) ~ There (ElemProof :: EffElem x a xs), SFindableElem x a xs) => SFindableElem x a (y ': xs) where
  sElemProof = SThere sElemProof

instance (SFindableElem x a xs, prf ~ ElemProof)
           => SingI (prf :: EffElem x a xs) where
  sing = sElemProof

nothingInEmpty :: EffElem x a '[] -> anything
-- nothingInEmpty Here = undefined
-- nothingInEmpty (There _) = undefined
nothingInEmpty = \case {}

dropEnv :: Env m ys -> SubList xs ys -> Env m xs
dropEnv Empty SubNil = Empty
dropEnv (v :> vs) (Keep rest) = v :> dropEnv vs rest
dropEnv (_ :> vs) (Drop rest) = dropEnv vs rest

updateWith :: Good a => [a] -> SList (xs :: [a]) -> SubList ys xs -> [a]
updateWith (y : ys) (_ `SCons` xs) (Keep rest) = y : updateWith ys xs rest
updateWith ys       (x `SCons` xs) (Drop rest) = fromSing x : updateWith ys xs rest
updateWith []       SNil           SubNil      = []
updateWith (y : ys) SNil           SubNil      = y : ys
updateWith []       (_ `SCons` _)  (Keep _)    = []

type family UpdateWith (ys' :: [a]) (xs :: [a]) (pf :: SubList ys xs) :: [a] where
  UpdateWith (y ': ys) (_ ': xs) (Keep rest) = y ': UpdateWith ys xs rest
  UpdateWith ys        (x ': xs) (Drop rest) = x ': UpdateWith ys xs rest
  UpdateWith '[]       '[]       SubNil      = '[]
  UpdateWith (y ': ys) '[]       SubNil      = y ': ys
  UpdateWith '[]       (_ ': _)  (Keep _)    = '[]

rebuildEnv :: Env m ys' -> SSubList (prf :: SubList ys xs) -> Env m xs -> Env m (UpdateWith ys' xs prf)
rebuildEnv Empty      SSubNil      env         = env
rebuildEnv (x :> xs) (SKeep rest) (_ :> env) = x :> rebuildEnv xs rest env
rebuildEnv xs         (SDrop rest) (y :> env) = y :> rebuildEnv xs rest env
rebuildEnv (x :> xs) SSubNil      Empty       = x :> xs
rebuildEnv Empty      (SKeep _)    _           = Empty

type family UpdateResTy b t (xs :: [EFFECT]) (elem :: EffElem e a xs)
                        (thing :: e @@ a @@ b @@ t) :: [EFFECT] where
  UpdateResTy b _ (MkEff a e ': xs) Here n = MkEff b e ': xs
  UpdateResTy b t (x ': xs) (There p) n = x ': UpdateResTy b t xs p n

type family UpdateResTyImm (xs :: [EFFECT]) (elem :: EffElem e a xs)
                           (t :: Type) :: [EFFECT] where
  UpdateResTyImm (MkEff a e ': xs) Here b = MkEff b e ': xs
  UpdateResTyImm (x ': xs) (There p) b = x ': UpdateResTyImm xs p b

infix 5 :::, := , :-

data LRes :: forall lbl. lbl -> Type -> Type where
  (:=) :: Sing (x :: lbl) -> res -> LRes x res

type family (x :: lbl) ::: (e :: EFFECT) :: EFFECT where
  x ::: MkEff r eff = MkEff (LRes x r) eff

unlabel :: Env m '[l ::: MkEff a eff] -> Env m '[MkEff a eff]
unlabel ((_ := v) :> Empty) = (v :> Empty)

relabel :: Sing (l :: ty) -> Env m '[MkEff a eff] -> Env m '[l ::: MkEff a eff]
relabel l (v :> Empty) = ((l := v) :> Empty)

data EffM :: (Type ~> Type) -> [EFFECT] -> [EFFECT] -> Type -> Type where
  Value :: a -> EffM m xs xs a
  Ebind :: EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
  Effect :: Good (e @@ a @@ b @@ t)
         => Proxy e -> Proxy a -> Proxy b -> Proxy t
         -> Sing (prf :: EffElem e a xs)
         -> Sing (eff :: e @@ a @@ b @@ t)
         -> EffM m xs (UpdateResTy b t xs prf eff) t
  Lift  :: Sing (prf :: SubList ys xs)
        -> EffM m ys ys' t -> EffM m xs (UpdateWith ys' xs prf) t
  New   :: Handler e m
        => res -> EffM m (MkEff res e ': xs) (MkEff res' e ': xs') a
        -> EffM m xs xs' a
  Test :: Sing (prf :: EffElem e (Either l r) xs)
       -> EffM m (UpdateResTyImm xs prf l) xs' t
       -> EffM m (UpdateResTyImm xs prf r) xs' t
       -> EffM m xs xs' t
  Test_lbl :: forall lbl (x :: lbl) e l r xs prf xs' t m.
              SingI x
           => Proxy x
           -> Sing (prf :: EffElem e (LRes x (Either l r)) xs)
           -> EffM m (UpdateResTyImm xs prf (LRes x l)) xs' t
           -> EffM m (UpdateResTyImm xs prf (LRes x r)) xs' t
           -> EffM m xs xs' t
  Catch :: Catchable m err
        => EffM m xs xs' a
        -> (err -> EffM m xs xs' a)
        -> EffM m xs xs' a
  (:-) :: Sing (l :: ty)
       -> EffM m '[MkEff ex ax] '[MkEff ey ay] t
       -> EffM m '[l ::: MkEff ex ax] '[l ::: MkEff ey ay] t

effect :: forall e a b t xs prf eff m.
          Good (e @@ a @@ b @@ t)
       => Sing (prf :: EffElem e a xs)
       -> Sing (eff :: e @@ a @@ b @@ t)
       -> EffM m xs (UpdateResTy b t xs prf eff) t
effect = Effect Proxy Proxy (Proxy :: Proxy b) Proxy

lift :: forall ys xs prf ys' m t.
        SingI (prf :: SubList ys xs)
     => EffM m ys ys' t -> EffM m xs (UpdateWith ys' xs prf) t
lift e = Lift (sing :: Sing prf) e

(|-) :: forall ty l ex ax xs prf m ey ay t.
        SingI (prf :: SubList '[l ::: MkEff ex ax] xs)
     => Sing (l :: ty)
     -> EffM m '[MkEff ex ax] '[MkEff ey ay] t
     -> EffM m xs (UpdateWith '[l ::: MkEff ey ay] xs prf) t
l |- e = Lift (sing :: Sing prf) (l :- e)

test :: forall e l r prf m xs' t.
        SingI (prf :: EffElem e (Either l r) xs)
     => EffM m (UpdateResTyImm xs prf l) xs' t
     -> EffM m (UpdateResTyImm xs prf r) xs' t
     -> EffM m xs xs' t
test = Test (sing :: Sing prf)

return :: a -> EffM m xs xs a
return x = Value x

(>>) :: EffM m xs xs' a -> EffM m xs' xs'' b -> EffM m xs xs'' b
a >> b = a >>= \_ -> b

(>>=) :: EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
(>>=) = Ebind

fail :: P.String -> EffM m xs ys a
fail = error

instance Functor (EffM m xs xs) where
  fn `fmap` v = do arg <- v
                   return (fn arg)

instance Applicative (EffM m xs xs) where
  pure = Value
  prog <*> v = do fn <- prog
                  arg <- v
                  return (fn arg)

execEff :: forall b t e res a (eff :: e @@ res @@ b @@ a) m xs
                  (p :: EffElem e res xs).
           Good (e @@ res @@ b @@ a)
        => Env m xs
        -> Sing (p :: EffElem e res xs)
        -> Sing (eff :: e @@ res @@ b @@ a)
        -> (Env m (UpdateResTy b a xs p eff) -> a -> m @@ t)
        -> m @@ t
execEff (val :> env) SHere eff' k
  = handle @e @m @t (fromSing eff') val (\ res v -> k (res :> env) v)
execEff (val :> env) (SThere p) eff k
  = execEff @b @t env p eff (\ env' v -> k (val :> env') v)
execEff Empty p _ _ = nothingInEmpty (fromSing p)

testEff :: forall b e xs l r p m.
           Sing (p :: EffElem e (Either l r) xs)
        -> Env m xs
        -> (Env m (UpdateResTyImm xs p l) -> m @@ b)
        -> (Env m (UpdateResTyImm xs p r) -> m @@ b)
        -> m @@ b
testEff SHere (Left err :> env) lk _rk = lk (err :> env)
testEff SHere (Right ok :> env) _lk rk = rk (ok :> env)
testEff (SThere p) (val :> env) lk rk
  = testEff @b p env (\envk -> lk (val :> envk))
                     (\envk -> rk (val :> envk))

testEffLbl :: forall b lbl x e l r xs p m.
              SingI (x :: lbl)
           => Sing (p :: EffElem e (LRes x (Either l r)) xs)
           -> Env m xs
           -> (Env m (UpdateResTyImm xs p (LRes x l)) -> m @@ b)
           -> (Env m (UpdateResTyImm xs p (LRes x r)) -> m @@ b)
           -> m @@ b
testEffLbl SHere ((lbl := Left err) :> env) lk _rk = lk ((lbl := err) :> env)
testEffLbl SHere ((lbl := Right ok) :> env) _lk rk = rk ((lbl := ok)  :> env)
testEffLbl (SThere p) (val :> env) lk rk
  = testEffLbl @b p env (\ envk -> lk (val :> envk))
                        (\ envk -> rk (val :> envk))

eff :: forall b m xs xs' a.
       Env m xs -> EffM m xs xs' a -> (Env m xs' -> a -> m @@ b) -> m @@ b
eff env (Value x) k = k env x
eff env (prog `Ebind` c) k
  = eff @b env prog (\ env' p' -> eff @b env' (c p') k)
eff env (Effect _ _ (_ :: Proxy b') _ prf effP) k
  = execEff @b' @b env prf effP k
eff env (Lift prf effP) k
  = let env' = dropEnv env (fromSing prf) in
    eff @b env' effP (\ envk p' -> k (rebuildEnv envk prf env) p')
eff env (New r prog) k
  = let env' = r :> env in
    eff @b env' prog (\ (_ :> envk) p' -> k envk p')
eff env (Test prf l r) k
  = testEff @b prf env (\ envk -> eff @b envk l k)
                       (\ envk -> eff @b envk r k)
eff env (Test_lbl (_ :: Proxy x) prf l r) k
  = testEffLbl @b prf env (\ envk -> eff @b envk l k)
                          (\ envk -> eff @b envk r k)
eff env (Catch prog handler) k
  = catch @m @_ @b (eff @b env prog k)
                   (\e -> eff @b env (handler e) k)
eff env (l :- prog) k
  = let env' = unlabel env in
    eff @b env' prog (\ envk p' -> k (relabel l envk) p')

run :: forall m xs xs' a.
       Applicative m => Env (TyCon1 m) xs -> EffM (TyCon1 m) xs xs' a -> m a
run env prog = eff @a env prog (\ _env r -> P.pure r)

runEnv :: forall m xs xs' a.
          Applicative m
       => Env (TyCon1 m) xs
       -> EffM (TyCon1 m) xs xs' a
       -> m (Env (TyCon1 m) xs', a)
runEnv env prog = eff @(Env (TyCon1 m) xs', a) env prog (\env r -> P.pure (env, r))

runPure :: forall xs xs' a. Env IdSym0 xs -> EffM IdSym0 xs xs' a -> a
runPure env prog = eff @a env prog (\_env r -> r)

runPureEnv :: forall xs xs' a.
              Env IdSym0 xs -> EffM IdSym0 xs xs' a -> (Env IdSym0 xs', a)
runPureEnv env prog = eff @(Env IdSym0 xs', a) env prog (,)

runWith :: forall a m xs xs'.
           (a -> m @@ a) -> Env m xs -> EffM m xs xs' a -> m @@ a
runWith inj env prog = eff @a env prog (\ _env r -> inj r)

type Eff m xs = EffM m xs xs

-- Section 2.3 from the paper:
mapE :: Applicative m => (a -> Eff (TyCon1 m) xs b) -> [a] -> Eff (TyCon1 m) xs [b]
mapE _ [] = pure []
mapE f (x : xs) = (:) <$> f x <*> mapE f xs

when :: Bool -> Eff (TyCon1 m) xs () -> Eff (TyCon1 m) xs ()
when True e = e
when False _ = pure ()
