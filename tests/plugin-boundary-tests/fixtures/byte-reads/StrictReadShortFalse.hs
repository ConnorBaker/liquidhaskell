module StrictReadShortFalse where

import qualified Data.ByteString as ByteString
import System.IO (Handle)

{-@ noShortRead :: Handle -> IO {v:Bool | v} @-}
noShortRead :: Handle -> IO Bool
noShortRead handle = do
    bytes <- ByteString.hGet handle 2
    pure (ByteString.length bytes /= 1)
