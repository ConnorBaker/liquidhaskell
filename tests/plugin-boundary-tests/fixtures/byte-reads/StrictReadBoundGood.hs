module StrictReadBoundGood where

import qualified Data.ByteString as ByteString
import System.IO (Handle)

{-@ readBounded :: Handle -> n:{Int | 0 <= n} -> IO {v:Int | 0 <= v && v <= n} @-}
readBounded :: Handle -> Int -> IO Int
readBounded handle count = do
    bytes <- ByteString.hGet handle count
    pure (ByteString.length bytes)
