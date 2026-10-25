module Owner (W (..), wfOf) where

data W = W {wf :: Int}

{-@ reflect wfOf @-}
wfOf :: W -> Int
wfOf (W n) = n
