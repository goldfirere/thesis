{-# LANGUAGE TemplateHaskell, PolyKinds, DataKinds, RankNTypes, TypeFamilies,
             GADTs, NoImplicitPrelude, TypeOperators, LambdaCase, EmptyCase,
             TypeHoles #-}

import Prelude ((++), Either(..), undefined, ($))
import Data.Singletons

$(singletons [d|
  data Char = CA | CB | CC | CD | CE
  data Nat = Zero | Succ Nat

  length :: [a] -> Nat
  length [] = Zero
  length (_:t) = Succ (length t)

  truncate :: Nat -> [Char] -> [Char]
  truncate Zero s = []
  truncate (Succ n) (h : t) = h : (truncate n t)
  truncate (Succ _) [] = []

  substring :: Nat -> Nat -> [Char] -> [Char]
  substring Zero n s = truncate n s
  substring (Succ start) n (h : t) = substring start n t
  substring (Succ _) n [] = []

  (-) :: Nat -> Nat -> Nat
  Zero - a = Zero
  (Succ n) - (Succ m) = n - m
  (Succ n) - Zero = Succ n
  |])

data a :~: b where
  Refl :: a :~: a

data False
absurd :: False -> a
absurd = \case {}

type Refuted a = a -> False
type Decidable a = Either a (Refuted a)

data Star :: ([Char] -> *) -> [Char] -> * where
  Empty :: Star p '[]
  Iter :: p s1 -> Star p s2 -> Star p (s1 :++ s2)

data Existential :: (k -> *) -> * where
  Exists :: Sing x -> p x -> Existential p

data ConcatCond p1 p2 s where
  ConcatCondC :: Sing s1 -> Sing s2 -> (s :~: (s1 :++ s2)) -> p1 s1 -> p2 s2
              -> ConcatCond p1 p2 s

data OrCond p1 p2 s where
  OrCondC :: Either (p1 s) (p2 s) -> OrCond p1 p2 s

data Regexp :: ([Char] -> *) -> * where
  RChar :: SChar ch -> Regexp ((:~:) '[ch])
  RConcat :: Regexp p1 -> Regexp p2 ->
             Regexp (ConcatCond p1 p2)
  ROr :: Regexp p1 -> Regexp p2 -> Regexp (OrCond p1 p2)
  RStar :: Regexp p -> Regexp (Star p)

data a <= b where
  LEZero :: Zero <= b
  LESucc :: a <= b -> (Succ a) <= (Succ b)

le_succ :: Sing a -> a <= Succ (Succ a)
le_succ SZero = LEZero
le_succ (SSucc n') = LESucc $ le_succ n'

data Split'L n s p1 p2 where
  Split'LC :: Sing s1 -> Sing s2 -> Length s1 <= n -> (s1 :++ s2) :~: s -> p1 s1 -> p2 s2
           -> Split'L n s p1 p2

data Split'R n s p1 p2 where
  Split'RC :: (forall s1 s2. Sing s1 -> Sing s2 -> Length s1 <= n -> (s1 :++ s2) :~: s ->
                             Either (Refuted (p1 s1)) (Refuted (p2 s2)))
           -> Split'R n s p1 p2

(&&) :: Either a b -> Either c d -> Either (a, c) (Either b d)
(Left a) && (Left c) = Left (a, c)
(Left _) && (Right d) = Right (Right d)
(Right b) && (Left _) = Right (Left b)
(Right b) && (Right _) = Right (Left b)

(||) :: Either a b -> Either c d -> (a -> e) -> (b -> c -> e) -> (b -> d -> f)
     -> Either e f
(Left x) || _ = \first _ _ -> Left $ first x
(Right x) || (Left y) = \_ second _ -> Left $ second x y
(Right x) || (Right y) = \_ _ third -> Right $ third x y

split' :: (forall s. Sing s -> Decidable (p1 s))
       -> (forall s. Sing s -> Decidable (p2 s))
       -> Sing (s :: [Char])
       -> SNat n
       -> n <= Length s
       -> Either (Split'L n s p1 p2) (Split'R n s p1 p2)
split' p1_dec p2_dec s n =
  case n of
  { SZero -> \_ -> case p1_dec SNil && p2_dec s of
    { Right contra -> Right $ Split'RC $ \s1 _ pf_le pf_eq -> case s1 of
      { SNil -> case pf_eq of { Refl -> contra }
      ; SCons _ _ -> case pf_le of { }
      }
    ; Left (p1_pf, p2_pf) -> Left $ Split'LC SNil s LEZero Refl p1_pf p2_pf
    }
  ; SSucc n' -> \(LESucc pf_le) ->
      ((p1_dec (sSubstring sZero (sSucc n') s) &&
        p2_dec (sSubstring (sSucc n') (sLength s %:- sSucc n') s)) ||
       split' p1_dec p2_dec s n' _)
      (\(p1_prefix, p2_suffix) -> Split'LC (sSubstring sZero (sSucc n') s)
                                           (sSubstring (sSucc n') (sLength s %:- sSucc n') s)
                                           pf_le
                                           Refl
                                           p1_prefix
                                           p2_suffix)
      (\_ (Split'LC prefix suffix pf_le' pf_eq p1_prefix p2_suffix) ->
        Split'LC prefix suffix pf_le pf_eq p1_prefix p2_suffix)
      (\bad_pre_or_suff (Split'RC contra) ->
        Split'RC $ \s1 s2 pf_le' pf_eq ->
          case bad_pre_or_suff of
          { Left bad_pre -> Left bad_pre
          ; Right bad_suf -> Right bad_suf
          })
  }
  