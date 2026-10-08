module TextObservationsGood where

import Data.ByteString qualified as ByteString
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Encoding

{-@ emptyObserved :: {v:Bool | v} @-}
emptyObserved :: Bool
emptyObserved = Text.null Text.empty && Text.length Text.empty == 0

{-@ countCharacters :: t:{Text | tvalid t} -> {n:Int | n == tlen t} / [tlen t] @-}
countCharacters :: Text -> Int
countCharacters text = case Text.uncons text of
    Nothing -> 0
    Just (_, rest) -> 1 + countCharacters rest

{-@ tailObserved
      :: t:{Text | tvalid t && tlen t > 0}
      -> {r:Text | tvalid r && tlen r + 1 == tlen t
                 && 1 <= tbytes t - tbytes r && tbytes t - tbytes r <= 4}
  @-}
tailObserved :: Text -> Text
tailObserved text = case Text.uncons text of
    Nothing -> Text.empty
    Just (_, rest) -> rest

{-@ headObserved :: t:{Text | tvalid t} -> Maybe {c:Char | tlen t > 0 && c == thead t} @-}
headObserved :: Text -> Maybe Char
headObserved text = case Text.uncons text of
    Nothing -> Nothing
    Just (character, _) -> Just character

{-@ dropObserved
      :: n:Int -> t:{Text | tvalid t}
      -> {r:Text | tvalid r && tlen r <= tlen t && tbytes r <= tbytes t
                 && (n > 0 && tlen t > 0 => tlen r < tlen t)
                 && (n <= 0 => tbytes r == tbytes t)
                 && (n <= 0 && tlen t > 0 => thead r == thead t)}
  @-}
dropObserved :: Int -> Text -> Text
dropObserved = Text.drop

{-@ spanObserved
      :: p:(Char -> Bool) -> t:{Text | tvalid t}
      -> {r:Text | tvalid r && tlen r <= tlen t && tbytes r <= tbytes t
                 && (tlen t > 0 && p (thead t) => tlen r < tlen t)
                 && (tlen r > 0 => not (p (thead r)))}
  @-}
spanObserved :: (Char -> Bool) -> Text -> Text
spanObserved predicate text = snd (Text.span predicate text)

-- The decoder establishes validity, not a literal-content equation. The Just
-- branch supplies the nonempty witness used by both subsequent scan steps.
-- Strictly shorter slices avoid Text.length's maximum-count endpoint.
{-@ decodedScan :: {v:Bool | v} @-}
decodedScan :: Bool
decodedScan = case Encoding.decodeUtf8' (ByteString.pack [0x41, 0xc3, 0xa9]) of
    Left _ -> True
    Right text -> case Text.uncons text of
        Nothing -> True
        Just (_, rest) -> case Text.span (\_ -> True) text of
            (prefix, suffix) ->
                not (Text.null prefix)
                    && Text.length suffix < countCharacters text
                    && Text.length (Text.drop 1 text) == Text.length rest

{-@ rawNull :: Text -> Bool @-}
rawNull :: Text -> Bool
rawNull = Text.null

{-@ dependentSecond :: (first :: {v:Int | 0 <= v}, {v:Int | first < v}) -> {v:Int | 0 < v} @-}
dependentSecond :: (Int, Int) -> Int
dependentSecond pair = snd pair

-- Each projection opens its own witness; the inner first shadows the outer.
{-@ nestedSecond
      :: (first :: {v:Int | 0 <= v}, (first :: {v:Int | first < v}, {v:Int | first < v}))
      -> {v:Int | 0 < v}
  @-}
nestedSecond :: (Int, (Int, Int)) -> Int
nestedSecond pair = snd (snd pair)

{-@ splitObserved :: (Char -> Bool) -> {t:Text | tvalid t}
                  -> [{piece:Text | tvalid piece}] @-}
splitObserved :: (Char -> Bool) -> Text -> [Text]
splitObserved = Text.split

-- Independently derive preservation and termination from the existing slice
-- contracts. The imported split above remains the actual producer under test.
{-@ splitBySlices :: (Char -> Bool) -> t:{Text | tvalid t}
                 -> [{piece:Text | tvalid piece}] / [tlen t] @-}
splitBySlices :: (Char -> Bool) -> Text -> [Text]
splitBySlices predicate text =
    case Text.span (not . predicate) text of
        (prefix, suffix) ->
            prefix : case Text.uncons suffix of
                Nothing -> []
                Just (_, rest) -> splitBySlices predicate rest
