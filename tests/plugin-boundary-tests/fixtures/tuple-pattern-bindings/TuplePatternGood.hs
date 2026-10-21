module TuplePatternGood where

-- A where-bound tuple pattern is a lazy pattern binding: its components are
-- case selections from the bound tuple, whose type carries the constructor
-- result's abstract-refinement properties.

{-@ pairSum :: {v:Integer | v == 3} @-}
pairSum :: Integer
pairSum = a + b
  where
    (a, b) = (1, 2)

{-@ quadSum :: {v:Integer | v == 10} @-}
quadSum :: Integer
quadSum = a + b + c + d
  where
    (a, b, c, d) = (1, 2, 3, 4)
