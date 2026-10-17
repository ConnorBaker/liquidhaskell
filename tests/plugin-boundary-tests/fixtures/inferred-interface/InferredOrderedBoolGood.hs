module InferredOrderedBoolGood where

-- opaque-reflect makes noneLeft a source fact: an independent query admits
-- its body, and later queries assume its solved callable. Recursion makes its
-- result variable a cut, solved from qualifiers; over Bool these include the
-- orderings v >= False and v <= False, which the solver elaborates through an
-- integer cast that the later query does not declare.
{-@ opaque-reflect noneLeft @-}
noneLeft :: [Int] -> Bool
noneLeft [] = False
noneLeft (_ : rest) = noneLeft rest

{-@ useNoneLeft :: [Int] -> {v:Bool | not v} @-}
useNoneLeft :: [Int] -> Bool
useNoneLeft values = noneLeft values
