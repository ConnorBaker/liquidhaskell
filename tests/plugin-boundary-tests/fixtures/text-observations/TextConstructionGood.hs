module TextConstructionGood where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ type AsciiChar = {c:Char | (lit "0" Char) <= c && c <= (lit "127" Char)} @-}

{-@ singletonObserved :: c:AsciiChar
      -> {t:Text | tvalid t && tlen t == 1 && tbytes t == 1 && thead t == c} @-}
singletonObserved :: Char -> Text
singletonObserved = Text.singleton

{-@ nulObserved :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 1} @-}
nulObserved :: Text
nulObserved = Text.singleton '\0'

{-@ upperAsciiObserved :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 1} @-}
upperAsciiObserved :: Text
upperAsciiObserved = Text.singleton '\127'

{-@ appendObserved
      :: x:{Text | tvalid x}
      -> y:{Text | tvalid y && tbytes x + tbytes y <= 64}
      -> {t:Text | tvalid t && tbytes t == tbytes x + tbytes y
                            && tlen t == tlen x + tlen y} @-}
appendObserved :: Text -> Text -> Text
appendObserved = Text.append

-- This is a checked structural construction, not pack, an overloaded Text
-- literal, or a claim that arbitrary addresses contain a valid encoding.
{-@ asciiText :: xs:{[AsciiChar] | len xs <= 64}
      -> {t:Text | tvalid t && tbytes t == len xs && tlen t == len xs}
      / [len xs] @-}
asciiText :: String -> Text
asciiText [] = Text.empty
asciiText (character : rest) =
    Text.append (Text.singleton character) (asciiText rest)

{-@ schemaField :: {t:Text | tvalid t && tbytes t == 13 && tlen t == 13} @-}
schemaField :: Text
schemaField = asciiText ['s', 'c', 'h', 'e', 'm', 'a', 'V', 'e', 'r', 's', 'i', 'o', 'n']

{-@ appendEmptyLeft :: t:{Text | tvalid t}
      -> {v:Text | tvalid v && tbytes v == tbytes t && tlen v == tlen t} @-}
appendEmptyLeft :: Text -> Text
appendEmptyLeft = Text.append Text.empty

{-@ appendEmptyRight :: t:{Text | tvalid t}
      -> {v:Text | tvalid v && tbytes v == tbytes t && tlen v == tlen t} @-}
appendEmptyRight :: Text -> Text
appendEmptyRight text = Text.append text Text.empty
