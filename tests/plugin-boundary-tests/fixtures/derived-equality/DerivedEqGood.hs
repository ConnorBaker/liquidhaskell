module DerivedEqGood where

import Data.Int (Int64)

data Color = Red | Green | Blue deriving (Eq)

data Shape = Dot | Line Int | Box Integer Color deriving stock (Eq)

-- An authored, checked equality contract also makes a field qualify.
data Op = Open | Close

{-@ instance Eq Op where
      (==) :: x:Op -> y:Op -> {v:Bool | v <=> x == y} @-}
instance Eq Op where
  Open == Open = True
  Close == Close = True
  _ == _ = False

data Row = Row {rowShape :: Shape, rowOp :: Op, rowSize :: Int64} deriving (Eq)

{-@ sameColor :: x:Color -> y:Color -> {v:Bool | v <=> x == y} @-}
sameColor :: Color -> Color -> Bool
sameColor x y = x == y

{-@ sameShape :: x:Shape -> y:Shape -> {v:Bool | v <=> x == y} @-}
sameShape :: Shape -> Shape -> Bool
sameShape x y = x == y

{-@ sameRow :: x:Row -> y:Row -> {v:Bool | v <=> x == y} @-}
sameRow :: Row -> Row -> Bool
sameRow x y = x == y

{-@ distinct :: {v:Bool | not v} @-}
distinct :: Bool
distinct = Line 1 == Line 2
