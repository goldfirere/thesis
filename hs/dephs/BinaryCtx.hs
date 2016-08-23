-- As submitted by Rob Dockins (rdockins@galois.com)

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module BinaryCtx where

import Control.Applicative
import GHC.TypeLits
import Data.Bits
import Data.Type.Equality
import Data.Proxy
import Data.Maybe
import Data.List
import GHC.Exts ( Constraint )

------------------------------------------------------------------------
-- Ctx

data Twice k = TwiceVal k k

-- type family accessor functions for the Twice kind
type family TwiceLeft (x::Twice k) :: k where
  TwiceLeft (TwiceVal a b) = a
type family TwiceRight (x::Twice k) :: k where
  TwiceRight (TwiceVal a b) = b

-- Double is already taken, use Dbl instead...
data Dbl (f :: k -> *) (tv :: Twice k) where
  Dbl :: (WF a, WF b) => f a -> f b -> Dbl f (TwiceVal a b)


type TwiceEta tv = (tv ~ TwiceVal (TwiceLeft tv) (TwiceRight tv))
type family WF (x :: k) :: Constraint where
  WF (x :: Twice k) = (WF (TwiceLeft x), WF (TwiceRight x), TwiceEta x)
  WF x              = ()

-- | Contexts are a kind representing a hetergenous list of values in some key.
--   The parameter k, may be any kind.  This datastructure is inspired
--   by the binary number system, and is intended to allow log-time operations,
--   for lookup, comparing indices, etc.

data PosCtx k where
  EndCtx     :: k -> PosCtx k
  ZeroBitCtx :: PosCtx (Twice k) -> PosCtx k
  OneBitCtx  :: PosCtx (Twice k) -> k -> PosCtx k

data Ctx k where
  EmptyCtx    :: Ctx k
  NonemptyCtx :: PosCtx k -> Ctx k

-- | A procedure for adding a new element to a context (on the right).
--   It is essentially the algorithm for incrementing a binary counter.
type family CtxPosSnoc (ctx::PosCtx k) (x::k) :: PosCtx k where
  CtxPosSnoc (EndCtx a) b        = ZeroBitCtx (EndCtx (TwiceVal a b))
  CtxPosSnoc (ZeroBitCtx ctx) b  = OneBitCtx ctx b
  CtxPosSnoc (OneBitCtx ctx a) b = ZeroBitCtx (CtxPosSnoc ctx (TwiceVal a b))

-- | Snoc for contexts is written  ::>

type family (ctx::Ctx k) ::> (x::k) :: Ctx k where
  EmptyCtx          ::> x = NonemptyCtx (EndCtx x)
  (NonemptyCtx ctx) ::> x = NonemptyCtx (CtxPosSnoc ctx x)


-- Addition is not currently used for anything, but could be used to implement
-- log-time merge of two contexts.  It's a little wierd, though, because the elements
-- from the two contexts get mixed together in nonobvious ways.

type family CtxPosAdd (ctx1 :: PosCtx k) (ctx2 :: PosCtx k) :: PosCtx k where
  CtxPosAdd (EndCtx a)         (EndCtx b)          = ZeroBitCtx (EndCtx (TwiceVal a b))
  CtxPosAdd (EndCtx a)         (ZeroBitCtx ctx2)   = OneBitCtx ctx2 a
  CtxPosAdd (EndCtx a)         (OneBitCtx ctx2 b)  = ZeroBitCtx (CtxPosSnoc ctx2 (TwiceVal a b))
  CtxPosAdd (ZeroBitCtx ctx1)  (EndCtx b)          = OneBitCtx ctx1 b
  CtxPosAdd (ZeroBitCtx ctx1)  (ZeroBitCtx ctx2)   = ZeroBitCtx (CtxPosAdd ctx1 ctx2)
  CtxPosAdd (ZeroBitCtx ctx1)  (OneBitCtx ctx2 b)  = OneBitCtx (CtxPosAdd ctx1 ctx2) b
  CtxPosAdd (OneBitCtx ctx1 a) (EndCtx b)          = ZeroBitCtx (CtxPosSnoc ctx1 (TwiceVal a b))
  CtxPosAdd (OneBitCtx ctx1 a) (ZeroBitCtx ctx2)   = OneBitCtx (CtxPosAdd ctx1 ctx2) a
  CtxPosAdd (OneBitCtx ctx1 a) (OneBitCtx ctx2 b)  = ZeroBitCtx (CtxPosAddC ctx1 ctx2 (TwiceVal a b))

type family CtxPosAddC (ctx1 :: PosCtx k) (ctx2 :: PosCtx k) (c :: k) :: PosCtx k where
  CtxPosAddC (EndCtx a)         (EndCtx b)         c = OneBitCtx (EndCtx (TwiceVal a b)) c
  CtxPosAddC (EndCtx a)         (ZeroBitCtx ctx2)  c = ZeroBitCtx (CtxPosSnoc ctx2 (TwiceVal a c))
  CtxPosAddC (EndCtx a)         (OneBitCtx ctx2 b) c = OneBitCtx (CtxPosSnoc ctx2 (TwiceVal a b)) c
  CtxPosAddC (ZeroBitCtx ctx1)  (EndCtx b)         c = ZeroBitCtx (CtxPosSnoc ctx1 (TwiceVal b c))
  CtxPosAddC (ZeroBitCtx ctx1)  (ZeroBitCtx ctx2)  c = OneBitCtx (CtxPosAdd ctx1 ctx2) c
  CtxPosAddC (ZeroBitCtx ctx1)  (OneBitCtx ctx2 b) c = ZeroBitCtx (CtxPosAddC ctx1 ctx2 (TwiceVal b c))
  CtxPosAddC (OneBitCtx ctx1 a) (EndCtx b)         c = OneBitCtx (CtxPosSnoc ctx1 (TwiceVal a b)) c
  CtxPosAddC (OneBitCtx ctx1 a) (ZeroBitCtx ctx2)  c = ZeroBitCtx (CtxPosAddC ctx1 ctx2 (TwiceVal a c)) 
  CtxPosAddC (OneBitCtx ctx1 a) (OneBitCtx ctx2 b) c = OneBitCtx (CtxPosAddC ctx1 ctx2 (TwiceVal a b)) c


type family CtxAdd (ctx1 :: Ctx k) (ctx2 :: Ctx k) :: Ctx k where
  CtxAdd EmptyCtx           ctx2               = ctx2
  CtxAdd ctx1               EmptyCtx           = ctx1
  CtxAdd (NonemptyCtx ctx1) (NonemptyCtx ctx2) = NonemptyCtx (CtxPosAdd ctx1 ctx2)


-- The borrow algorithm is used to define "unsnoc" which deletes the
-- rightmost element from a context.

data BorrowResult k = BorrowResultVal (PosCtx k) k

type family BorrowCtx (x::BorrowResult k) :: PosCtx k where
  BorrowCtx (BorrowResultVal ctx x) = ctx
type family BorrowBit (x::BorrowResult k) ::k where
  BorrowBit (BorrowResultVal ctx x) = x


type ZeroBitBorrowResult br =
  BorrowResultVal (OneBitCtx (BorrowCtx br) (TwiceLeft (BorrowBit br)))
                  (TwiceRight (BorrowBit br))

type family Borrow (ctx :: PosCtx (Twice k)) :: BorrowResult k where
  Borrow (EndCtx x)        = BorrowResultVal (EndCtx (TwiceLeft x))
                                             (TwiceRight x)
  Borrow (OneBitCtx ctx x) = BorrowResultVal (OneBitCtx (ZeroBitCtx ctx) (TwiceLeft x))
                                             (TwiceRight x)
  Borrow (ZeroBitCtx ctx)  = ZeroBitBorrowResult (Borrow ctx)

    -- original defn:  I was worried about exponential behavior because of the triple-occurence of (Borrow ctx)
    -- I'm not sure the new definition makes any difference, except that I feel better about it.
    --
    -- BorrowResultVal (OneBitCtx (BorrowCtx (Borrow ctx)) (TwiceLeft (BorrowBit (Borrow ctx))))
    --                                                     (TwiceRight (BorrowBit (Borrow ctx)))

type family Unsnoc (ctx :: PosCtx k) :: Ctx k where
  Unsnoc (EndCtx x)        = EmptyCtx
  Unsnoc (OneBitCtx ctx x) = NonemptyCtx (ZeroBitCtx ctx)
  Unsnoc (ZeroBitCtx ctx)  = NonemptyCtx (BorrowCtx (Borrow ctx))

------------------------------------------------------------------------
-- Size

-- | Represents the size of a context.
--
--   The `Proxy` is needed in the one-bit case for
--   exceptionally tedious reasons.  Basically, I need to
--   be able to bring the type variable "x" into scope somehow
--   so I can mention it later to help the typechecker figure
--   some things out.  We make is strict and UNPACK it in the hopes
--   that is dissapears at runtime.

data PosSize :: PosCtx k -> * where

  SizeEnd     :: WF x => PosSize (EndCtx x)

  SizeZeroBit :: PosSize ctx
              -> PosSize (ZeroBitCtx ctx)

  SizeOneBit  :: WF x
              => {-# UNPACK #-} !(Proxy x)
              -> PosSize ctx
              -> PosSize (OneBitCtx ctx x)

data Size :: Ctx k -> * where
  SizeZero :: Size EmptyCtx
  SizePos  :: PosSize ctx -> Size (NonemptyCtx ctx)

posSizeInt :: PosSize ctx -> Int
posSizeInt SizeEnd           = 1
posSizeInt (SizeZeroBit sz)  = (posSizeInt sz `shiftL` 1)
posSizeInt (SizeOneBit _ sz) = (posSizeInt sz `shiftL` 1) + 1

sizeInt :: Size ctx -> Int
sizeInt SizeZero     = 0
sizeInt (SizePos sz) = posSizeInt sz

-- | The size of an empty context.
zeroSize :: Size EmptyCtx
zeroSize = SizeZero

incPosSize :: WF tp => PosSize ctx -> Proxy tp -> PosSize (CtxPosSnoc ctx tp)
incPosSize SizeEnd           _ = SizeZeroBit SizeEnd
incPosSize (SizeZeroBit sz)  _ = SizeOneBit Proxy sz
-- GHC cannot figure out the right types on its own; hence all this Proxy nonsense
incPosSize (SizeOneBit (_ :: Proxy x) sz) (_ :: Proxy tp) =
   SizeZeroBit (incPosSize sz (Proxy :: Proxy (TwiceVal x tp)))

-- | Increment the size to the next value.
incSize :: forall ctx tp. WF tp => Size ctx -> Size (ctx ::> tp)
incSize SizeZero     = SizePos SizeEnd
incSize (SizePos sz) = SizePos (incPosSize sz (Proxy :: Proxy tp))

incSize' :: forall ctx tp. WF tp => Proxy tp -> Size ctx -> Size (ctx ::> tp)
incSize' _ SizeZero     = SizePos SizeEnd
incSize' p (SizePos sz) = SizePos (incPosSize sz p)

-- An index points to a location in a context
--
-- Note: The proxy values exists entirely so that we can bring certain
-- type varaibles into scope later.  We UNPACK them in the hope that GHC
-- will allocate no space to storing the singleton Proxy values.
-- Proxies are needed for cases where a type variable would otherwise occur only
-- in the result type of the constructor.
data PosIndex :: PosCtx k -> k -> * where

   IdxEnd    :: WF x
             => {-# UNPACK #-} !(Proxy x)
             -> PosIndex (EndCtx x) x

   IdxHere   :: WF x
             => {-# UNPACK #-} !(Proxy x)
             -> PosSize ctx
             -> PosIndex (OneBitCtx ctx x) x

   IdxLeft0  :: WF tv
             => PosIndex ctx tv
             -> PosIndex (ZeroBitCtx ctx) (TwiceLeft tv)

   IdxRight0 :: WF tv
             => PosIndex ctx tv
             -> PosIndex (ZeroBitCtx ctx) (TwiceRight tv)

   IdxLeft1  :: (WF tv, WF c)
             => {-# UNPACK #-} !(Proxy c)
             -> PosIndex ctx tv
             -> PosIndex (OneBitCtx ctx c) (TwiceLeft tv)

   IdxRight1 :: (WF tv, WF c)
             => {-# UNPACK #-} !(Proxy c)
             -> PosIndex ctx tv
             -> PosIndex (OneBitCtx ctx c) (TwiceRight tv)

data Index (ctx :: Ctx k) (x :: k) where
   Idx :: PosIndex ctx x -> Index (NonemptyCtx ctx) x

posIndexVal :: PosIndex ctx tp -> Int
posIndexVal (IdxEnd _) = 0
posIndexVal (IdxHere _ sz)    = posSizeInt sz
posIndexVal (IdxLeft0 idx)    = (posIndexVal idx `shiftL` 1)
posIndexVal (IdxRight0 idx)   = (posIndexVal idx `shiftL` 1) + 1
posIndexVal (IdxLeft1 _ idx)  = (posIndexVal idx `shiftL` 1)
posIndexVal (IdxRight1 _ idx) = (posIndexVal idx `shiftL` 1) + 1

indexVal :: Index ctx tp -> Int
indexVal (Idx idx) = posIndexVal idx


-- An assignment is essentially a finite dependent product
data PosAssignment :: (k -> *) -> PosCtx k -> * where
   AssignEnd  :: WF x => f x -> PosAssignment f (EndCtx x)
   AssignZero :: PosAssignment (Dbl f) ctx        -> PosAssignment f (ZeroBitCtx ctx)
   AssignOne  :: WF x => PosAssignment (Dbl f) ctx -> f x -> PosAssignment f (OneBitCtx ctx x)

data Assignment :: (k -> *) -> Ctx k -> * where
   EmptyAssign    :: Assignment f EmptyCtx
   NonemptyAssign :: PosAssignment f ctx -> Assignment f (NonemptyCtx ctx)

extendPos :: WF tp
          => PosAssignment f ctx -> f tp -> PosAssignment f (CtxPosSnoc ctx tp)
extendPos (AssignEnd x) y      = AssignZero (AssignEnd (Dbl x y))
extendPos (AssignZero asgn) y  = AssignOne asgn y
extendPos (AssignOne asgn (x :: f a)) (y :: f tp)
   = AssignZero (extendPos asgn (Dbl x y :: Dbl f (TwiceVal a tp)))

empty :: Assignment f EmptyCtx
empty = EmptyAssign

extend :: WF tp => Assignment f ctx -> f tp -> Assignment f (ctx ::> tp)
extend EmptyAssign y = NonemptyAssign (AssignEnd y)
extend (NonemptyAssign asgn) y = NonemptyAssign (extendPos asgn y)



posAssignBorrow :: PosAssignment (Dbl f) ctx -> (PosAssignment f (BorrowCtx (Borrow ctx)) -> f (BorrowBit (Borrow ctx)) -> a) -> a
posAssignBorrow (AssignEnd (Dbl x y))      cont = cont (AssignEnd x) y
posAssignBorrow (AssignOne asgn (Dbl x y)) cont = cont (AssignOne (AssignZero asgn) x) y
posAssignBorrow (AssignZero asgn)          cont = posAssignBorrow asgn (\asgn' (Dbl x y) -> cont (AssignOne asgn' x) y)

initPos :: PosAssignment f ctx -> Assignment f (Unsnoc ctx)
initPos (AssignEnd _)      = EmptyAssign
initPos (AssignOne asgn _) = NonemptyAssign (AssignZero asgn)
initPos (AssignZero asgn)  = posAssignBorrow asgn (\asgn' _ -> NonemptyAssign asgn')

-- | Return assignment with all but the last block.
init :: ((ctx ::> tp) ~ NonemptyCtx ctx', Unsnoc ctx' ~ ctx) => Assignment f (ctx::>tp) -> Assignment f ctx
init (NonemptyAssign asgn) = initPos asgn
init _ = error "impossible!"


lookupPos :: (f tp -> a) -> PosIndex ctx tp -> PosAssignment f ctx -> a
lookupPos h (IdxEnd _)        (AssignEnd x)      = h x
lookupPos h (IdxHere _ _)     (AssignOne _ x)    = h x
lookupPos h (IdxLeft0  idx)   (AssignZero asgn)  = lookupPos (\(Dbl x _) -> h x) idx asgn
lookupPos h (IdxRight0 idx)   (AssignZero asgn)  = lookupPos (\(Dbl _ y) -> h y) idx asgn
lookupPos h (IdxLeft1 _ idx)  (AssignOne asgn _) = lookupPos (\(Dbl x _) -> h x) idx asgn
lookupPos h (IdxRight1 _ idx) (AssignOne asgn _) = lookupPos (\(Dbl _ y) -> h y) idx asgn

-- make the coverage checker be quiet
lookupPos _ _ _ = error "lookupPos: unpossible!"

-- ugh: GHC (properly) rejects the following as ill typed, but the coverge checker complains that
--      they are missing....
--lookupPos h (IdxEnd _) (AssignZero _) = error "impossible!"
--lookupPos h (IdxEnd _) (AssignOne _ _) = error "impossible!"
--lookupPos h (IdxHere _ _) (AssignEnd _) = error "impossible!"
--lookupPos h (IdxHere _ _) (AssignZero _) = error "impossible!"

lookupIdx :: Index ctx tp -> Assignment f ctx -> f tp
lookupIdx (Idx idx) (NonemptyAssign asgn) = lookupPos (\x -> x) idx asgn

-- make the coverage checker be quiet
lookupIdx _ _ = error "lookupIdx: unpossible!"

-- again: GHC rejects the following, then complains it is missing...
-- lookupIdx (Idx _)   EmptyAssign = error "impossible!"


-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
(!) asgn idx = lookupIdx idx asgn

-- | Return value of assignment.
(!!) :: (KnownDiff l r, WF tp) => Assignment f r -> Index l tp -> f tp
a !! i = a ! extendIndex i


extendIndex :: (KnownDiff l r, WF tp) => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

extendIndex' :: WF tp => Diff l r -> Index l tp -> Index r tp
extendIndex' DiffHere           idx = idx
extendIndex' (DiffThere p diff) idx = skip' p (extendIndex' diff idx)



-- | Index for first element in context.
base :: WF tp => Index (EmptyCtx ::> tp) tp
base = Idx (IdxEnd Proxy)

posNextIndex :: WF tp => PosSize ctx -> Proxy tp -> PosIndex (CtxPosSnoc ctx tp) tp
posNextIndex SizeEnd _ = IdxRight0 (IdxEnd Proxy)
posNextIndex (SizeZeroBit sz) _ = IdxHere Proxy sz
posNextIndex (SizeOneBit (_ :: Proxy c) sz) (_ :: Proxy tp) =
   IdxRight0 (posNextIndex sz (Proxy :: Proxy (TwiceVal c tp)))

-- | Return the index of a element one past the size.
nextIndex :: WF tp => Size ctx -> Index (ctx ::> tp) tp
nextIndex (SizePos sz) = Idx (posNextIndex sz Proxy)
nextIndex SizeZero     = Idx (IdxEnd Proxy)

skipPos :: forall ctx x y. (WF x, WF y) => PosIndex ctx x -> Proxy y -> PosIndex (CtxPosSnoc ctx y) x
skipPos (IdxEnd _) _      = IdxLeft0 (IdxEnd Proxy)
skipPos (IdxLeft0  idx) p = IdxLeft1 p idx
skipPos (IdxRight0 idx) p = IdxRight1 p idx
skipPos (IdxHere   (_ :: Proxy x) sz)  (_ :: Proxy y) = IdxLeft0  (posNextIndex sz (Proxy :: Proxy (TwiceVal x y)))
skipPos (IdxLeft1  (_ :: Proxy c) idx) (_ :: Proxy y) = IdxLeft0  (skipPos idx (Proxy :: Proxy (TwiceVal c y)))
skipPos (IdxRight1 (_ :: Proxy c) idx) (_ :: Proxy y) = IdxRight0 (skipPos idx (Proxy :: Proxy (TwiceVal c y)))

skip' :: (WF x, WF y) => Proxy y -> Index ctx x -> Index (ctx::>y) x
skip' p (Idx idx) = Idx (skipPos idx p)

skip :: forall ctx x y. (WF x, WF y) => Index ctx x -> Index (ctx::>y) x
skip (Idx idx) = Idx (skipPos idx (Proxy :: Proxy y))

posIndexSize :: PosIndex ctx tp -> PosSize ctx
posIndexSize (IdxEnd _)         = SizeEnd
posIndexSize (IdxHere p sz)     = SizeOneBit p sz
posIndexSize (IdxLeft0  idx)    = SizeZeroBit (posIndexSize idx)
posIndexSize (IdxRight0 idx)    = SizeZeroBit (posIndexSize idx)
posIndexSize (IdxLeft1  p idx)  = SizeOneBit p (posIndexSize idx)
posIndexSize (IdxRight1 p idx)  = SizeOneBit p (posIndexSize idx)

indexSize :: Index ctx tp -> Size ctx
indexSize (Idx idx) = SizePos (posIndexSize idx)

instance Eq (Index ctx tp) where
   idx1 == idx2 = isJust (testEquality idx1 idx2)

instance TestEquality (Index ctx) where
   testEquality (Idx idx1) (Idx idx2) = testEquality idx1 idx2

instance TestEquality (PosIndex ctx) where
   testEquality (IdxEnd _)    (IdxEnd _)    = Just Refl
   testEquality (IdxHere _ _) (IdxHere _ _) = Just Refl
   testEquality (IdxLeft0  idx1) (IdxLeft0 idx2)  = 
        case testEquality idx1 idx2 of
           Just Refl -> Just Refl
           Nothing   -> Nothing
   testEquality (IdxRight0 idx1) (IdxRight0 idx2) =
        case testEquality idx1 idx2 of
           Just Refl -> Just Refl
           Nothing   -> Nothing
   testEquality (IdxLeft1 _ idx1) (IdxLeft1 _ idx2) =
        case testEquality idx1 idx2 of
           Just Refl -> Just Refl
           Nothing   -> Nothing
   testEquality (IdxRight1 _ idx1) (IdxRight1 _ idx2) =
        case testEquality idx1 idx2 of
           Just Refl -> Just Refl
           Nothing   -> Nothing

   testEquality _ _ = Nothing


------------------------------------------------------------------------
-- Diff

-- | Difference in number of elements between two contexts.
-- The first context must be a sub-context of the other.
-- FIXME? Is there a reasonable way to do this other than
-- by a sequence of increments?
data Diff (l :: Ctx k) (r :: Ctx k) where
   DiffHere  :: Diff ctx ctx
   DiffThere :: WF tp
             => {-# UNPACK #-} !(Proxy tp)
             -> Diff ctx1 ctx2
             -> Diff ctx1 (ctx2 ::> tp)

deriving instance Show (Diff l r)

-- | The identity difference.
noDiff :: Diff l l
noDiff = DiffHere

-- | Extend the difference to a sub-context of the right side.
extendRight :: forall l r tp. WF tp => Diff l r -> Diff l (r::>tp)
extendRight diff = DiffThere (Proxy :: Proxy tp) diff

composeDiff :: Diff a b -> Diff b c -> Diff a c
composeDiff x DiffHere = x
composeDiff x (DiffThere p y) = DiffThere p (composeDiff x y)

-- instance Cat.Category Diff where
--   id = DiffHere
--   d1 . d2 = composeDiff d2 d1

-- | Extend the size by a given difference.
extSize :: Size l -> Diff l r -> Size r
extSize sz DiffHere = sz
extSize sz (DiffThere p (diff :: Diff a b)) = incSize' p (extSize sz diff)

-- ------------------------------------------------------------------------
-- -- KnownDiff

-- | A difference that can be automatically inferred at compile time.
class KnownDiff (l :: Ctx k) (r :: Ctx k) where
   knownDiff :: Diff l r


instance KnownDiff EmptyCtx EmptyCtx
      where knownDiff = DiffHere
  
instance (TestDiff n' EmptyCtx (NonemptyCtx r), n' ~ NatPred (ComputePosSize r))
  => KnownDiff EmptyCtx (NonemptyCtx r)
      where knownDiff = testDiff (Proxy :: Proxy n')

instance (TestDiff n' (NonemptyCtx l) (NonemptyCtx r), n' ~ NatPred n, ComputePosDiff l r n)
  => KnownDiff (NonemptyCtx l) (NonemptyCtx r)
      where knownDiff = testDiff (Proxy :: Proxy n')

type family ComputePosSize (l :: PosCtx k) :: Nat where
  ComputePosSize (EndCtx x)        = 1
  ComputePosSize (ZeroBitCtx ctx)  = (2 * ComputePosSize ctx)
  ComputePosSize (OneBitCtx ctx p) = (2 * ComputePosSize ctx) + 1
  
class ComputePosDiff (ctx1 :: PosCtx k) (ctx2:: PosCtx k) (n::Nat) | ctx1 ctx2 -> n
instance (n ~ ComputePosSize ctx1, m ~ ComputePosSize ctx2, n <= m, diff ~ (m - n)) => ComputePosDiff ctx1 ctx2 diff

type family NatPred (n :: Nat) :: Maybe Nat where
  NatPred 0 = Nothing
  NatPred n = Just (n-1)

class TestDiff (n::Maybe Nat) (l::Ctx k) (r::Ctx k) where
  testDiff :: Proxy n -> Diff l r

instance l ~ r => TestDiff Nothing l r where
  testDiff _ = DiffHere
  
instance (TestDiff n' l r', n' ~ NatPred n, CtxPred r r' tp, NonemptyCtx r ~ (r' ::> tp), WF tp) => TestDiff (Just n) l (NonemptyCtx r) where
  testDiff _ = DiffThere (Proxy :: Proxy tp) (testDiff (Proxy :: Proxy n') :: Diff l r')

class CtxPred (r::PosCtx k) (r'::Ctx k) (tp::k) | r -> r' tp

instance (Borrow ctx ~ BorrowResultVal ctx' x)
      => CtxPred (ZeroBitCtx ctx)  (NonemptyCtx ctx')             x
instance CtxPred (OneBitCtx ctx x) (NonemptyCtx (ZeroBitCtx ctx)) x
instance CtxPred (EndCtx x)        EmptyCtx                       x





posSize :: PosAssignment f ctx -> PosSize ctx
posSize (AssignEnd _)      = SizeEnd
posSize (AssignZero asgn)  = SizeZeroBit (posSize asgn)
posSize (AssignOne asgn (_ :: f tp)) = SizeOneBit (Proxy :: Proxy tp) (posSize asgn)

size :: Assignment f ctx -> Size ctx
size EmptyAssign = SizeZero
size (NonemptyAssign asgn) = SizePos (posSize asgn)


-- | Generate an assignment
generate :: forall ctx f
          . Size ctx
         -> (forall tp . WF tp => Index ctx tp -> f tp)
         -> Assignment f ctx
generate SizeZero _     = EmptyAssign
generate (SizePos sz) f = NonemptyAssign $ go (\i -> f (Idx i)) sz
 where go :: forall f' ctx'
           . (forall tp. WF tp => PosIndex ctx' tp -> f' tp)
          -> PosSize ctx'
          -> PosAssignment f' ctx'
       go g SizeEnd           = AssignEnd  (g (IdxEnd Proxy))
       go g (SizeZeroBit sz)  = AssignZero (go (\i -> Dbl (g (IdxLeft0 i))   (g (IdxRight0 i)))   sz)
       go g (SizeOneBit p sz) = AssignOne  (go (\i -> Dbl (g (IdxLeft1 p i)) (g (IdxRight1 p i))) sz) (g (IdxHere p sz))

-- | Generate an assignment in an applicative
generateM :: forall ctx m f
           . Applicative m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM SizeZero _     = pure EmptyAssign
generateM (SizePos sz) f = pure NonemptyAssign <*> go (\i -> f (Idx i)) sz
  where go :: forall f' ctx'
            . (forall tp. WF tp => PosIndex ctx' tp -> m (f' tp))
           -> PosSize ctx'
           -> m (PosAssignment f' ctx')
        go g SizeEnd           = pure AssignEnd  <*> g (IdxEnd Proxy)
        go g (SizeZeroBit sz)  = pure AssignZero <*> go (\i -> pure Dbl <*> g (IdxLeft0 i)   <*> g (IdxRight0 i))   sz
        go g (SizeOneBit p sz) = pure AssignOne  <*> go (\i -> pure Dbl <*> g (IdxLeft1 p i) <*> g (IdxRight1 p i)) sz <*> g (IdxHere p sz)


-- | A right fold over an assignment.
foldrF :: (forall tp . f tp -> r -> r)
       -> r
       -> Assignment f c
       -> r
foldrF _ r0 EmptyAssign = r0
foldrF f r0 (NonemptyAssign asgn) = go f r0 asgn
  where go :: forall f' r ctx
            . (forall tp. f' tp -> r -> r)
           -> r
           -> PosAssignment f' ctx
           -> r
        go f' r (AssignEnd x)      = f' x r
        go f' r (AssignZero asgn)  = go (\ (Dbl x y) -> f' x . f' y) r        asgn
        go f' r (AssignOne asgn z) = go (\ (Dbl x y) -> f' x . f' y) (f' z r) asgn

-- | A left fold over an assignment.
foldlF :: (forall tp . r -> f tp -> r)
       -> r
       -> Assignment f c
       -> r
foldlF _ rz EmptyAssign = rz
foldlF f rz (NonemptyAssign asgn) = go f rz asgn
  where go :: forall f' r ctx
            . (forall tp. r -> f' tp -> r)
           -> r
           -> PosAssignment f' ctx
           -> r
        go f' rz (AssignEnd x)      = f' rz x
        go f' rz (AssignZero asgn)  = go (\r (Dbl x y) -> f' (f' r x) y) rz asgn
        go f' rz (AssignOne asgn z) = f' (go (\r (Dbl x y) -> f' (f' r x) y) rz asgn) z

traverseF :: forall f g m c
           . Applicative m
          => (forall tp . f tp -> m (g tp))
          -> Assignment f c
          -> m (Assignment g c)
traverseF _ EmptyAssign = pure EmptyAssign
traverseF f (NonemptyAssign asgn) = pure NonemptyAssign <*> go f asgn
  where go :: forall f' g' ctx
            . (forall tp. f' tp -> m (g' tp))
           -> PosAssignment f' ctx
           -> m (PosAssignment g' ctx)
        go f' (AssignEnd x)      = pure AssignEnd  <*> f' x
        go f' (AssignZero asgn)  = pure AssignZero <*> go (\ (Dbl x y) -> pure Dbl <*> f' x <*> f' y) asgn
        go f' (AssignOne asgn z) = pure AssignOne  <*> go (\ (Dbl x y) -> pure Dbl <*> f' x <*> f' y) asgn <*> f' z


toLists :: (forall tp . f tp -> a)
        -> Assignment f c
        -> [a] -> [a]
toLists f = foldlF (\l x -> l . (f x:)) id

-- | Convert assignment to list.
toList :: (forall tp . f tp -> a)
       -> Assignment f c
       -> [a]
toList f asgn = toLists f asgn []

-- | Map assignment
map :: (forall tp . f tp -> g tp) -> Assignment f c -> Assignment g c
map _ EmptyAssign = EmptyAssign
map f (NonemptyAssign asgn) = NonemptyAssign (go f asgn)
  where go :: forall f' g' ctx
            . (forall tp. f' tp -> g' tp)
           -> PosAssignment f' ctx
           -> PosAssignment g' ctx
        go f' (AssignEnd x)      = AssignEnd  (f' x)
        go f' (AssignZero asgn)  = AssignZero (go (\ (Dbl x y) -> Dbl (f' x) (f' y)) asgn)
        go f' (AssignOne asgn z) = AssignOne  (go (\ (Dbl x y) -> Dbl (f' x) (f' y)) asgn) (f' z)

zipWithM :: forall m f g h c
          . Applicative m
         => (forall tp . f tp -> g tp -> m (h tp))
         -> Assignment f c
         -> Assignment g c
         -> m (Assignment h c)
zipWithM _ EmptyAssign EmptyAssign = pure EmptyAssign
zipWithM f (NonemptyAssign a1) (NonemptyAssign a2) = pure NonemptyAssign <*> go f a1 a2
  where go :: forall f' g' h' ctx
            . (forall tp. f' tp -> g' tp -> m (h' tp))
           -> PosAssignment f' ctx
           -> PosAssignment g' ctx
           -> m (PosAssignment h' ctx)
        go f' (AssignEnd x) (AssignEnd y) = pure AssignEnd <*> f' x y
        go f' (AssignZero a1) (AssignZero a2) =
                pure AssignZero
                  <*> go (\ (Dbl a b) (Dbl x y) -> pure Dbl <*> f' a x <*> f' b y) a1 a2
        go f' (AssignOne a1 z1) (AssignOne a2 z2) =
                pure AssignOne
                  <*> go (\ (Dbl a b) (Dbl x y) -> pure Dbl <*> f' a x <*> f' b y) a1 a2
                  <*> f' z1 z2

        go _ _ _ = error "unpossible!"
zipWithM _ _ _ = error "unpossible!"


(%>) :: WF tp => Assignment f x -> f tp -> Assignment f (x::>tp)
a %> v = extend a v


showAsgn :: (forall tp. f tp -> String) -> Assignment f ctx -> String
showAsgn showf a = "[" ++ intercalate ", " (toList showf a) ++ "]"


instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

instance TestEquality f => TestEquality (Assignment f) where
   testEquality = testEq


testEq :: TestEquality f
       => Assignment f ctx1
       -> Assignment f ctx2
       -> Maybe (ctx1 :~: ctx2)
testEq EmptyAssign EmptyAssign = Just Refl
testEq (NonemptyAssign a1) (NonemptyAssign a2) =
   case testPosEq testEquality a1 a2 of
      Nothing   -> Nothing
      Just Refl -> Just Refl
testEq _ _ = error "unpossible!"


testPosEq
       :: (forall tp1 tp2. f tp1 -> f tp2 -> Maybe (tp1 :~: tp2))
       -> PosAssignment f ctx1
       -> PosAssignment f ctx2
       -> Maybe (ctx1 :~: ctx2)
testPosEq teq (AssignEnd x) (AssignEnd y) =
   case teq x y of
      Just Refl -> Just Refl
      Nothing -> Nothing
testPosEq teq (AssignZero a1) (AssignZero a2) =
   case testPosEq (doubleTest teq) a1 a2 of
     Nothing -> Nothing
     Just Refl -> Just Refl
testPosEq teq (AssignOne a1 z1) (AssignOne a2 z2) =
   case testPosEq (doubleTest teq) a1 a2 of
     Nothing -> Nothing
     Just Refl ->
       case teq z1 z2 of
         Nothing -> Nothing
         Just Refl -> Just Refl


doubleTest :: (forall a b. f a -> f b -> Maybe (a :~: b))
           -> (forall a b. Dbl f a -> Dbl f b -> Maybe (a :~: b))
doubleTest teq (Dbl a b) (Dbl x y) = 
    case teq a x of
       Nothing -> Nothing
       Just Refl ->
         case teq b y of
           Nothing -> Nothing
           Just Refl -> Just Refl

