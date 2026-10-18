module TextEqGood where

import Data.Text (Text)
import Data.Text qualified as Text

-- text-2.1.3's (==) compares byte lengths, then the stored byte slices.
{-@ reflexive :: x:Text -> {v:Bool | v} @-}
reflexive :: Text -> Bool
reflexive x = x == x

{-@ sameRepresentation :: x:Text -> y:{Text | y == x} -> {v:Bool | v} @-}
sameRepresentation :: Text -> Text -> Bool
sameRepresentation x y = x == y

{-@ observationsAgree :: x:Text -> y:Text
      -> {v:Bool | v => (tbytes x == tbytes y && (tvalid x <=> tvalid y))} @-}
observationsAgree :: Text -> Text -> Bool
observationsAgree x y = x == y

{-@ lengthsAgree :: x:{Text | tvalid x} -> y:Text -> {v:Bool | v => tlen x == tlen y} @-}
lengthsAgree :: Text -> Text -> Bool
lengthsAgree x y = x == y

{-@ emptyIsEmpty :: {v:Bool | v} @-}
emptyIsEmpty :: Bool
emptyIsEmpty = Text.empty == Text.empty
