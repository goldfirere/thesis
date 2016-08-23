{-# LANGUAGE DataKinds, PolyKinds, MultiParamTypeClasses, ConstraintKinds, TypeFamilies,
             UndecidableInstances, FlexibleInstances, TypeOperators, GADTs,
             RankNTypes, TypeHoles, ScopedTypeVariables, IncoherentInstances,
             NullaryTypeClasses, EmptyCase #-}

module Sort where

import GHC.Exts
import GHC.TypeLits
import Data.Singletons.Prelude
import Unsafe.Coerce

class (True ~ False) => Falsehood
class Truth
instance Truth

data Dict :: Constraint -> * where
  Dict :: c => Dict c
withDict :: Dict c -> (c => r) -> r
withDict Dict x = x

type family OneMethod (c :: Constraint) :: *
type instance OneMethod (c1, c2) = (OneMethod c1, OneMethod c2)

newtype Constrained c r = Don'tInstantiate (c => r)
mkDict :: forall proxy c. proxy c -> OneMethod c -> Dict c
mkDict _ meth = unsafeCoerce (Don'tInstantiate Dict :: Constrained c (Dict c)) meth

class l ==> r where
  implies :: l => Proxy l -> Dict r
type instance OneMethod (l ==> r) = Constrained l (Proxy l -> Dict r)
  
instance Falsehood ==> a -- no body possible
instance a ==> a where
  implies _ = Dict

type l <==> r = (l ==> r, r ==> l)

class (a :: Constraint) \/ (b :: Constraint) where
  disjunct :: Either (Dict a) (Dict b)
type instance OneMethod (a \/ b) = Either (Dict a) (Dict b)

withLeft :: forall proxy a b r. a => proxy (a \/ b) -> ((a \/ b) => r) -> r
withLeft proxy f = withDict (mkDict proxy (Left Dict)) f

withRight :: forall proxy a b r. b => proxy (a \/ b) -> ((a \/ b) => r) -> r
withRight proxy f = withDict (mkDict proxy (Right Dict)) f

instance (a \/ a) ==> a where
  implies _ = case disjunct :: Either (Dict a) (Dict a) of
              Left Dict  -> Dict
              Right Dict -> Dict

instance a ==> (a \/ b) where
  implies _ = withLeft (Proxy :: Proxy (a \/ b)) Dict
instance b ==> (a \/ b) where
  implies _ = withRight (Proxy :: Proxy (a \/ b)) Dict
instance a ==> (a \/ a) where
  implies _ = withLeft (Proxy :: Proxy (a \/ a)) Dict
instance (a ==> c, b ==> c) => (a \/ b) ==> c where
  implies _ = case disjunct :: Either (Dict a) (Dict b) of
              Left Dict  -> withDict (implies (Proxy :: Proxy a) :: Dict c) Dict
              Right Dict -> withDict (implies (Proxy :: Proxy b) :: Dict c) Dict

data InPf :: k -> [k] -> * where
  InHere :: InPf x (x ': rest)
  InThere :: InPf x rest -> InPf x (y ': rest)

class In (x :: k) (list :: [k]) where
  inPf :: InPf x list
instance In x (x ': rest) where
  inPf = InHere
instance In x rest => In x (y ': rest) where
  inPf = InThere inPf

instance In x '[] ==> a where
  implies _ = case inPf :: InPf x '[] of {}

type family SortedRange (min :: Nat) (max :: Nat) (list :: [Nat]) :: Constraint
type instance SortedRange n m '[] = n <= m
type instance SortedRange n m (hd ': tl) = (SortedRange hd m tl, n <= hd, hd <= m)

data Nat_st :: Nat -> Constraint -> * where
  MkNat_st :: c => Sing n -> Nat_st n c

data SortedRangeList :: Nat -> Nat -> [Nat] -> * where
  MkSRL :: SortedRange n1 n2 list => Sing list -> SortedRangeList n1 n2 list

data ExSRL :: Nat -> Nat -> [Nat] -> [Nat] -> * where
  MkExSRL :: SortedRange n1 n4 k => (forall proxy x. proxy x ->
                                                     Dict (In x k <==> (In x i \/ In x j)))
                                 -> Sing k -> ExSRL n1 n4 i j 

append :: forall n1 n2 n3 n4 i j.
          Sing n1 -> Nat_st n2 (n1 <= n2) -> Nat_st n3 (n2 <= n3) -> Nat_st n4 (n3 <= n4)
       -> SortedRangeList n1 n2 i -> SortedRangeList n3 n4 j
       -> ExSRL n1 n4 i j
append n1 (MkNat_st n2) (MkNat_st n3) (MkNat_st n4) (MkSRL i) (MkSRL j) =
  case i of
    SNil -> case j of
              SNil -> MkExSRL (\_ -> Dict) j
              SCons _ _ -> MkExSRL (\_ -> Dict) j
    SCons (hd :: Sing nx) (tl :: Sing nxs) -> case append hd (MkNat_st n2) (MkNat_st n3) (MkNat_st n4)
                                  (MkSRL tl) (MkSRL j) of
                     MkExSRL toDict (result :: Sing k) ->
                       MkExSRL (\(proxy :: proxy x) ->
                         withDict (toDict proxy) $
                         mkDict (Proxy :: Proxy (In x (nx ': k) <==> (In x i \/ In x j)))
                                ( Don'tInstantiate $ \_ ->
                                    case inPf :: InPf x (nx ': k) of
                                      InHere -> withLeft (Proxy :: Proxy (In x i \/ In x j)) Dict
                                      InThere _ -> Dict
                                , undefined))
{-                                (Don'tInstantiate $ \(_ :: Proxy (In x j)) ->
                                  let orProxy = (Proxy :: Proxy (In x nxs \/ In x j)) in
                                  withRight orProxy $
                                  withDict (implies orProxy :: Dict (In x k)) Dict) -}
                               (SCons hd result)
                                                  
{-

val append: n1:int -> n2:int{n1 <= n2} -> n3:int{n2 <= n3} -> n4:int{n3 <= n4} 
         -> i:list int{SortedRange n1 n2 i} 
         -> j:list int{SortedRange n3 n4 j}
         -> k:list int{SortedRange n1 n4 k 
                      /\ (forall x. In x k <==> In x i \/ In x j)}
let rec append n1 n2 n3 n4 i j = match i with 
  | [] -> 
    (match j with
      | [] -> j
      | _::_ -> j)
  | hd::tl -> hd::(append hd n2 n3 n4 tl j)

val partition: x:int
            -> l:list int
            -> (lo:list int
                * hi:list int{(forall y. In y lo ==> y <= x /\ In y l)
                               /\ (forall y. In y hi ==> x < y /\ In y l)
                               /\ (forall y. In y l ==> In y lo \/ In y hi)})
let rec partition x l = match l with
  | [] -> ([], [])
  | hd::tl ->
    let lo, hi = partition x tl in
    if hd <= x
    then (hd::lo, hi)
    else (lo, hd::hi)

val sort: min:int  
       -> max:int{min <= max} 
       -> i:list int {forall x. In x i ==> (min <= x /\ x <= max)}
       -> j:list int{SortedRange min max j /\ (forall x. In x i <==> In x j)}
let rec sort min max i = match i with
  | [] -> []
  | hd::tl ->
    let lo,hi = partition hd tl in
    let i' = sort min hd lo in 
    let j' = sort hd max hi in
    append min hd hd max i' (hd::j')

-}