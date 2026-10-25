module PlainDependent (usesP, getP) where

import Plain

-- Plain has no LiquidHaskell interface, so this module is P's only publisher.
{-@ reflect usesP @-}
usesP :: P -> Int
usesP (P n) = n + 1

{-@ measure getP @-}
getP :: P -> Int
getP (P n) = n
