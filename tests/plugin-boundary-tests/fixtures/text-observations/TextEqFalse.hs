module TextEqFalse where

import Data.Text (Text)

{-@ alwaysEqual :: Text -> Text -> {v:Bool | v} @-}
alwaysEqual :: Text -> Text -> Bool
alwaysEqual x y = x == y

{-@ neverEqual :: x:Text -> y:Text -> {v:Bool | not v} @-}
neverEqual :: Text -> Text -> Bool
neverEqual x y = x == y

{-@ equalMeansValid :: x:Text -> y:Text -> {v:Bool | v => tvalid x} @-}
equalMeansValid :: Text -> Text -> Bool
equalMeansValid x y = x == y

{-@ vacuous :: x:Text -> y:Text -> {v:Bool | false} @-}
vacuous :: Text -> Text -> Bool
vacuous x y = x == y

-- Content equality is not representation equality.
{-@ representation :: x:Text -> y:Text -> {v:Bool | v => x == y} @-}
representation :: Text -> Text -> Bool
representation x y = x == y

-- Outside valid slices tlen states nothing.
{-@ invalidLengths :: x:Text -> y:Text -> {v:Bool | v => tlen x == tlen y} @-}
invalidLengths :: Text -> Text -> Bool
invalidLengths x y = x == y
