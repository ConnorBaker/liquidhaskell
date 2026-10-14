-- A partial measure's result (head, tail, fromJust) is a logical value with no
-- source constructor. An outer measure or projection consumes it logically.
module LogicalCarrierObservation (signals, splitLast) where

import Data.Maybe ()

{-@ signals :: b:Bool -> {s:[Int] | len s == (if b then 3 else 2) && head (tail s) == (if b then 2 else 9)} @-}
signals :: Bool -> [Int]
signals b = if b then 1 : rest else rest
  where rest = [2, 9]

{-@ splitLast :: xs : [a]
      -> {v : Maybe ([a], a) | (isJust v <=> len xs > 0)
                            && (isJust v => len (fst (fromJust v)) == len xs - 1)} @-}
splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast (x : xs) = case splitLast xs of
  Nothing -> Just ([], x)
  Just (middle, final) -> Just (x : middle, final)
