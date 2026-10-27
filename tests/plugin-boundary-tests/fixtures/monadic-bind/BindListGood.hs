module BindListGood where

-- A lawful list bind. Lists carry an abstract refinement, which the bind rule
-- refuses ("refined monadic type"), so the rule must not fire here.
{-@ pairs :: [Int] -> [Int] @-}
pairs :: [Int] -> [Int]
pairs xs = do
  x <- xs
  [x, x]
