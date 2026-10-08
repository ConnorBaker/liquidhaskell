module LexicalBranchTautologyBad where

{-@ reflect onlyTrue @-}
{-@ onlyTrue :: b:{Bool | b} -> Bool / [0] @-}
onlyTrue :: Bool -> Bool
onlyTrue b = if b then True else onlyTrue b

{-@ outer :: b:Bool -> Bool @-}
outer :: Bool -> Bool
outer b =
    if b
        then False
        else
            let
                {-@ go :: x:Bool -> {v:Bool | onlyTrue b == onlyTrue b} @-}
                go :: Bool -> Bool
                go x = if x then True else True
             in
                go True
