module LazyReadBoundGood where

import qualified Data.ByteString.Lazy as ByteString
import Data.Int (Int64)
import System.IO (Handle)

{-@ readBounded :: Handle -> n:{Int | 0 <= n} -> IO {v:Int64 | 0 <= v && v <= n} @-}
readBounded :: Handle -> Int -> IO Int64
readBounded handle count = do
    bytes <- ByteString.hGet handle count
    pure (ByteString.length bytes)
