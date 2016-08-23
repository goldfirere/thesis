{-# LANGUAGE GADTs, DataKinds, PolyKinds, TemplateHaskell, TypeFamilies,
             ConstraintKinds, TypeOperators, MultiParamTypeClasses, 
             FlexibleInstances, FlexibleContexts #-}

import Prelude hiding (Read)
import Data.Singletons

$(promote [d|
  data Cap = Create | Read | Update | Delete
    deriving Eq
  |])

data Principal :: [Cap] -> * where
  MkP :: String -> Principal caps

class Contains (cap :: Cap) (caps :: [Cap])
instance Contains cap (cap ': caps)
instance Contains cap t => Contains cap (h ': t)

class Doesn'tContain (cap :: Cap) (caps :: [Cap])
instance Doesn'tContain cap '[]
instance (Doesn'tContain cap caps, (cap :/=: newcap) ~ True) => Doesn'tContain cap (newcap ': caps)

data DbHandle
data DbData

readDb :: Contains Read caps => Principal caps -> DbHandle -> IO DbData
readDb = undefined

updateDb :: Contains Update caps => Principal caps -> DbHandle -> DbData -> IO ()
updateDb = undefined

readOnlyDb :: (Doesn'tContain Create caps, Doesn'tContain Update caps,
               Doesn'tContain Delete caps) => Principal caps -> IO a -> IO a
readOnlyDb = undefined

readUpdDb p handle = do
  dat <- readDb p handle
  updateDb p handle dat
  readOnlyDb p undefined

foo :: Doesn'tContain Read '[Read] => ()
foo = ()