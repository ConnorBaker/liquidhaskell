module SharedFailureGood where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-simplify-core" @-}

-- Without core simplification, the reflected body keeps the desugarer's
-- shared match-failure handler: both failing branches jump to one
-- let-bound `\_ -> case patError ... of {}`.
{-@ reflect secondOf @-}
{-@ secondOf :: {xs:[Int] | len xs >= 2} -> Int @-}
secondOf :: [Int] -> Int
secondOf xs = case xs of (_ : y : _) -> y

{-@ reflect three @-}
{-@ three :: {v:[Int] | len v == 3} @-}
three :: [Int]
three = [1, 2, 3]

{-@ claim :: {v:() | secondOf three == 2} @-}
claim :: ()
claim = ()
