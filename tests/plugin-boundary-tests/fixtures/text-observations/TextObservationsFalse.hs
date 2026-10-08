module TextObservationsFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ alwaysEmpty :: t:{Text | tvalid t} -> {v:Bool | v} @-}
alwaysEmpty :: Text -> Bool
alwaysEmpty text = Text.null text

{-@ byteCountIsCharacterCount :: t:{Text | tvalid t && tlen t == 1} -> {v:Int | v == tbytes t} @-}
byteCountIsCharacterCount :: Text -> Int
byteCountIsCharacterCount text = Text.length text

{-@ unchangedTail
      :: t:{Text | tvalid t && tlen t > 0} -> {r:Text | tlen r == tlen t}
  @-}
unchangedTail :: Text -> Text
unchangedTail text = case Text.uncons text of
    Nothing -> Text.empty
    Just (_, rest) -> rest

{-@ unchangedSpan
      :: t:{Text | tvalid t && tlen t > 0} -> {r:Text | tlen r == tlen t}
  @-}
unchangedSpan :: Text -> Text
unchangedSpan text = snd (Text.span (\_ -> True) text)

{-@ unchangedDrop
      :: t:{Text | tvalid t && tlen t > 0} -> {r:Text | tlen r == tlen t}
  @-}
unchangedDrop :: Text -> Text
unchangedDrop text = Text.drop 1 text

-- The portable contract retains text-2.1.3's maximum-count endpoint.
{-@ nonnegativeLength :: t:{Text | tvalid t} -> {v:Int | v >= 0} @-}
nonnegativeLength :: Text -> Int
nonnegativeLength text = Text.length text

{-@ dependentSecond :: (first :: {v:Int | 0 <= v}, {v:Int | first < v}) -> {v:Int | v <= 0} @-}
dependentSecond :: (Int, Int) -> Int
dependentSecond pair = snd pair

{-@ nestedSecond
      :: (first :: {v:Int | 0 <= v}, (first :: {v:Int | first < v}, {v:Int | first < v}))
      -> {v:Int | v <= 0}
  @-}
nestedSecond :: (Int, (Int, Int)) -> Int
nestedSecond pair = snd (snd pair)
