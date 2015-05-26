{-# LANGUAGE MagicHash, UnboxedTuples #-}
import Control.Monad.Primitive
import Data.Primitive.Array
import GHC.IO
import GHC.Prim

-- Since we only have a single test case right now, I'm going to avoid the
-- issue of choosing a test framework for the moment. This also keeps the
-- package as a whole light on dependencies.

main :: IO ()
main = do
    arr <- newArray 1 'A'
    let unit =
            case writeArray arr 0 'B' of
                IO f ->
                    case f realWorld# of
                        (# _, _ #) -> ()
    c1 <- readArray arr 0
    return $! unit
    c2 <- readArray arr 0
    if c1 == 'A' && c2 == 'B'
        then return ()
        else error $ "Expected AB, got: " ++ show (c1, c2)
