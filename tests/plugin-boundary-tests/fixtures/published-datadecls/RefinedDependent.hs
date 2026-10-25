module RefinedDependent (usesR) where

import RefinedOwner

-- Reflecting over R makes this module re-derive R's (unrefined) declaration.
{-@ reflect usesR @-}
usesR :: R -> Int
usesR (R n) = n
