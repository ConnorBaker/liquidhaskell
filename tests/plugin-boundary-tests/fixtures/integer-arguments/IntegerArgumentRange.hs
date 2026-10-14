module IntegerArgumentRange where

{-@ LIQUID "--reflection" @-}

-- 2^64 is not an Int: the conversion is an obligation, not an assumption
-- (assuming it would contradict Int's range invariant and make this vacuous).
{-@ reflect ident @-}
ident :: Int -> Int
ident x = x

{-@ prop :: {v:() | ident 18446744073709551616 == 0 && false} @-}
prop :: ()
prop = ()
