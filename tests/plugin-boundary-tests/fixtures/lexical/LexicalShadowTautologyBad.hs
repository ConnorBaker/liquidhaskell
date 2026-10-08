module LexicalShadowTautologyBad where

{-@ reflect onlyTrue @-}
{-@ onlyTrue :: b:{Bool | b} -> Bool / [0] @-}
onlyTrue :: Bool -> Bool
onlyTrue b = if b then True else onlyTrue b

{-@ outer :: b:{Bool | b} -> Bool @-}
outer :: Bool -> Bool
outer b = if b then local False else local False
  where
    {-@ local :: b:Bool -> Bool @-}
    local :: Bool -> Bool
    local b = go True
      where
        {-@ go :: x:Bool -> {v:Bool | onlyTrue b == onlyTrue b} @-}
        go :: Bool -> Bool
        go x = if x then True else True
