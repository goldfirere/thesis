{-# LANGUAGE CPP, MagicHash, UnboxedTuples, DeriveDataTypeable, BangPatterns #-}

-- |
-- Module      : Data.Primitive.Array
-- Copyright   : (c) Roman Leshchinskiy 2009-2012
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Portability : non-portable
--
-- Primitive boxed arrays
--

module Data.Primitive.Array (
  Array(..), MutableArray(..),

  newArray, readArray, writeArray, indexArray, indexArrayM,
  unsafeFreezeArray, unsafeThawArray, sameMutableArray,
  copyArray, copyMutableArray,
  cloneArray, cloneMutableArray
) where

import Control.Monad.Primitive

import GHC.Base  ( Int(..) )
import GHC.Prim

import Data.Typeable ( Typeable )
import Data.Data ( Data(..) )
import Data.Primitive.Internal.Compat ( isTrue#, mkNoRepType )

#if !(__GLASGOW_HASKELL__ >= 702)
import Control.Monad.ST(runST)
#endif

-- | Boxed arrays
data Array a = Array (Array# a) deriving ( Typeable )

-- | Mutable boxed arrays associated with a primitive state token.
data MutableArray s a = MutableArray (MutableArray# s a)
                                deriving ( Typeable )

-- | Create a new mutable array of the specified size and initialise all
-- elements with the given value.
newArray :: PrimMonad m => Int -> a -> m (MutableArray (PrimState m) a)
{-# INLINE newArray #-}
newArray (I# n#) x = primitive
   (\s# -> case newArray# n# x s# of
             (# s'#, arr# #) -> (# s'#, MutableArray arr# #))

-- | Read a value from the array at the given index.
readArray :: PrimMonad m => MutableArray (PrimState m) a -> Int -> m a
{-# INLINE readArray #-}
readArray (MutableArray arr#) (I# i#) = primitive (readArray# arr# i#)

-- | Write a value to the array at the given index.
writeArray :: PrimMonad m => MutableArray (PrimState m) a -> Int -> a -> m ()
{-# INLINE writeArray #-}
writeArray (MutableArray arr#) (I# i#) x = primitive_ (writeArray# arr# i# x)

-- | Read a value from the immutable array at the given index.
indexArray :: Array a -> Int -> a
{-# INLINE indexArray #-}
indexArray (Array arr#) (I# i#) = case indexArray# arr# i# of (# x #) -> x

-- | Monadically read a value from the immutable array at the given index.
-- This allows us to be strict in the array while remaining lazy in the read
-- element which is very useful for collective operations. Suppose we want to
-- copy an array. We could do something like this:
--
-- > copy marr arr ... = do ...
-- >                        writeArray marr i (indexArray arr i) ...
-- >                        ...
--
-- But since primitive arrays are lazy, the calls to 'indexArray' will not be
-- evaluated. Rather, @marr@ will be filled with thunks each of which would
-- retain a reference to @arr@. This is definitely not what we want!
--
-- With 'indexArrayM', we can instead write
--
-- > copy marr arr ... = do ...
-- >                        x <- indexArrayM arr i
-- >                        writeArray marr i x
-- >                        ...
--
-- Now, indexing is executed immediately although the returned element is
-- still not evaluated.
--
indexArrayM :: Monad m => Array a -> Int -> m a
{-# INLINE indexArrayM #-}
indexArrayM (Array arr#) (I# i#)
  = case indexArray# arr# i# of (# x #) -> return x

-- | Convert a mutable array to an immutable one without copying. The
-- array should not be modified after the conversion.
unsafeFreezeArray :: PrimMonad m => MutableArray (PrimState m) a -> m (Array a)
{-# INLINE unsafeFreezeArray #-}
unsafeFreezeArray (MutableArray arr#)
  = primitive (\s# -> case unsafeFreezeArray# arr# s# of
                        (# s'#, arr'# #) -> (# s'#, Array arr'# #))

-- | Convert an immutable array to an mutable one without copying. The
-- immutable array should not be used after the conversion.
unsafeThawArray :: PrimMonad m => Array a -> m (MutableArray (PrimState m) a)
{-# INLINE unsafeThawArray #-}
unsafeThawArray (Array arr#)
  = primitive (\s# -> case unsafeThawArray# arr# s# of
                        (# s'#, arr'# #) -> (# s'#, MutableArray arr'# #))

-- | Check whether the two arrays refer to the same memory block.
sameMutableArray :: MutableArray s a -> MutableArray s a -> Bool
{-# INLINE sameMutableArray #-}
sameMutableArray (MutableArray arr#) (MutableArray brr#)
  = isTrue# (sameMutableArray# arr# brr#)

-- | Copy a slice of an immutable array to a mutable array.
copyArray :: PrimMonad m
          => MutableArray (PrimState m) a    -- ^ destination array
          -> Int                             -- ^ offset into destination array
          -> Array a                         -- ^ source array
          -> Int                             -- ^ offset into source array
          -> Int                             -- ^ number of elements to copy
          -> m ()
{-# INLINE copyArray #-}
#if __GLASGOW_HASKELL__ > 706
-- NOTE: copyArray# and copyMutableArray# are slightly broken in GHC 7.6.* and earlier
copyArray (MutableArray dst#) (I# doff#) (Array src#) (I# soff#) (I# len#)
  = primitive_ (copyArray# src# soff# dst# doff# len#)
#else
copyArray !dst !doff !src !soff !len = go 0
  where
    go i | i < len = do
                       x <- indexArrayM src (soff+i)
                       writeArray dst (doff+i) x
                       go (i+1)
         | otherwise = return ()
#endif

-- | Copy a slice of a mutable array to another array. The two arrays may
-- not be the same.
copyMutableArray :: PrimMonad m
          => MutableArray (PrimState m) a    -- ^ destination array
          -> Int                             -- ^ offset into destination array
          -> MutableArray (PrimState m) a    -- ^ source array
          -> Int                             -- ^ offset into source array
          -> Int                             -- ^ number of elements to copy
          -> m ()
{-# INLINE copyMutableArray #-}
#if __GLASGOW_HASKELL__ >= 706
-- NOTE: copyArray# and copyMutableArray# are slightly broken in GHC 7.6.* and earlier
copyMutableArray (MutableArray dst#) (I# doff#)
                 (MutableArray src#) (I# soff#) (I# len#)
  = primitive_ (copyMutableArray# src# soff# dst# doff# len#)
#else
copyMutableArray !dst !doff !src !soff !len = go 0
  where
    go i | i < len = do
                       x <- readArray src (soff+i)
                       writeArray dst (doff+i) x
                       go (i+1)
         | otherwise = return ()
#endif

-- | Return a newly allocated Array with the specified subrange of the
-- provided Array. The provided Array should contain the full subrange
-- specified by the two Ints, but this is not checked.
cloneArray :: Array a -- ^ source array
           -> Int     -- ^ offset into destination array
           -> Int     -- ^ number of elements to copy
           -> Array a
{-# INLINE cloneArray #-}
#if __GLASGOW_HASKELL__ >= 702
cloneArray (Array arr#) (I# off#) (I# len#) 
  = case cloneArray# arr# off# len# of arr'# -> Array arr'#
#else
cloneArray arr off len = runST $ do
    marr2 <- newArray len (error "Undefined element")
    copyArray marr2 0 arr off len
    unsafeFreezeArray marr2
#endif

-- | Return a newly allocated MutableArray. with the specified subrange of
-- the provided MutableArray. The provided MutableArray should contain the
-- full subrange specified by the two Ints, but this is not checked.
cloneMutableArray :: PrimMonad m
        => MutableArray (PrimState m) a -- ^ source array
        -> Int                          -- ^ offset into destination array
        -> Int                          -- ^ number of elements to copy
        -> m (MutableArray (PrimState m) a)
{-# INLINE cloneMutableArray #-}
#if __GLASGOW_HASKELL__ >= 702
cloneMutableArray (MutableArray arr#) (I# off#) (I# len#) = primitive
   (\s# -> case cloneMutableArray# arr# off# len# s# of
             (# s'#, arr'# #) -> (# s'#, MutableArray arr'# #))
#else
cloneMutableArray marr off len = do
        marr2 <- newArray len (error "Undefined element")
        let go !i !j c
                | c >= len = return marr2
                | otherwise = do
                    b <- readArray marr i
                    writeArray marr2 j b
                    go (i+1) (j+1) (c+1)
        go off 0 0
#endif

instance Typeable a => Data (Array a) where
  toConstr _ = error "toConstr"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Data.Primitive.Array.Array"

instance (Typeable s, Typeable a) => Data (MutableArray s a) where
  toConstr _ = error "toConstr"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Data.Primitive.Array.MutableArray"
