{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
-- A measure applied to a partial measure's logical result keeps its meaning:
-- the second element is 9 only when b is False.
module LogicalCarrierObservation00 (signals) where

{-@ signals :: b:Bool -> {s:[Int] | head (tail s) == (if b then 9 else 2)} @-}
signals :: Bool -> [Int]
signals b = if b then 1 : rest else rest
  where rest = [2, 9]
