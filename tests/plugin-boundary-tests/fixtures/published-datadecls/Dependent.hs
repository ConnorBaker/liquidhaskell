module Dependent (usesW) where

import Owner

-- Reflecting over Owner's type makes this module re-derive W's data declaration.
{-@ reflect usesW @-}
usesW :: W -> Int
usesW (W n) = n + 1
