{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
-- A projection applied to fromJust's logical result keeps its meaning: the
-- prefix is one shorter than the input.
module LogicalCarrierObservation01 (splitLast) where

import Data.Maybe ()

{-@ splitLast :: xs : [a]
      -> {v : Maybe ([a], a) | isJust v => len (fst (fromJust v)) == len xs} @-}
splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast (x : xs) = case splitLast xs of
  Nothing -> Just ([], x)
  Just (middle, final) -> Just (x : middle, final)
