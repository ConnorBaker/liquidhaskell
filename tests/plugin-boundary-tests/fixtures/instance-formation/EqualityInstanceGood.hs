module EqualityInstanceGood where

import Data.String (fromString)

{-@ identityString :: input:[Char] -> {output:[Char] | output == input} @-}
identityString :: String -> String
identityString = fromString
