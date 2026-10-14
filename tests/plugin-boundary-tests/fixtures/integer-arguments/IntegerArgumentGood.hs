module IntegerArgumentGood where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Logical integer arithmetic passed to an Int parameter of a reflected
-- source function inside a refinement (upstream tests ple/neg/Ple_sum).
{-@ reflect ident @-}
ident :: Int -> Int
ident x = x

{-@ prop :: {v:() | ident (5 + 1) == 6} @-}
prop :: ()
prop = ()
