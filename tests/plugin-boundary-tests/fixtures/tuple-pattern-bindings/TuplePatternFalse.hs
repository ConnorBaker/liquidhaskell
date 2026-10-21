module TuplePatternFalse where

-- The pair's sum holds. The four-tuple's claimed sum is off by one: its
-- components keep the constructor arguments' values, not arbitrary ones.

{-@ pairSum :: {v:Integer | v == 3} @-}
pairSum :: Integer
pairSum = a + b
  where
    (a, b) = (1, 2)

{-@ quadSum :: {v:Integer | v == 11} @-}
quadSum :: Integer
quadSum = a + b + c + d
  where
    (a, b, c, d) = (1, 2, 3, 4)
