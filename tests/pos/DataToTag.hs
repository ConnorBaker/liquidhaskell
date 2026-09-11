{-# LANGUAGE MagicHash #-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTag where

import GHC.Exts (Int(I#), dataToTag#, (/=#))
import GHC.Prim (dataToTagSmall#, dataToTagLarge#)

data Choice = First Int | Second Int deriving (Eq, Ord)

{-@ measure constructorTag @-}
constructorTag :: Choice -> Int
constructorTag (First _) = 0
constructorTag (Second _) = 1

{-@ tag :: x:Choice -> {v:Int | v == constructorTag x} @-}
tag :: Choice -> Int
tag x = case x of
  First _ -> I# (dataToTag# x)
  Second _ -> I# (dataToTag# x)

{-@ smallTag :: x:Choice -> {v:Int | v == constructorTag x} @-}
smallTag :: Choice -> Int
smallTag x = case x of
  First _ -> I# (dataToTagSmall# x)
  Second _ -> I# (dataToTagSmall# x)

{-@ largeTag :: x:Choice -> {v:Int | v == constructorTag x} @-}
largeTag :: Choice -> Int
largeTag x = case x of
  First _ -> I# (dataToTagLarge# x)
  Second _ -> I# (dataToTagLarge# x)

-- Enough constructors to make GHC derive tag-first Eq, including payloads.
data Six = C0 Int | C1 Int | C2 Int | C3 Int | C4 Int | C5 Int
  deriving (Eq, Ord)

-- More constructors than fit in pointer tags on either 32- or 64-bit GHC.
data Nine = N0 Int | N1 Int | N2 Int | N3 Int | N4 Int
          | N5 Int | N6 Int | N7 Int | N8 Int deriving (Eq, Ord)

{-@ nineTag :: Nine -> {v:Int | 0 <= v && v < 9} @-}
nineTag :: Nine -> Int
nineTag x = I# (dataToTagLarge# x)

-- Primitive inequality, used by GHC's generated tag comparison, is an Int#
-- returning exactly zero for equal inputs and one for unequal inputs.
{-@ unequalSelf :: Int -> {v:Int | v == 0} @-}
unequalSelf :: Int -> Int
unequalSelf (I# x) = I# (x /=# x)

{-@ unequalInputs :: x:Int -> y:{Int | x /= y} -> {v:Int | v == 1} @-}
unequalInputs :: Int -> Int -> Int
unequalInputs (I# x) (I# y) = I# (x /=# y)

{-@ fail wrongInequality @-}
{-@ wrongInequality :: x:Int -> y:{Int | x /= y} -> {v:Int | v == 0} @-}
wrongInequality :: Int -> Int -> Int
wrongInequality (I# x) (I# y) = I# (x /=# y)

{-@ fail equalPayloads @-}
{-@ equalPayloads :: x:Int -> y:Int -> {v:Bool | v} @-}
equalPayloads :: Int -> Int -> Bool
equalPayloads x y = if tag (First x) == tag (First y) then x == y else True

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
