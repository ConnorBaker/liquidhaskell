{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Classes_LHAssumptions where

import GHC.Types_LHAssumptions ()

{-@

assume not :: x:Bool -> {v:Bool | ((v) <=> ~(x))}
define not    x                         = (~ x)

assume &&    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) && (y)))}
assume ||    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) || (y)))}
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool

class Eq a => Ord a where
    compare :: a -> a -> Ordering
    (<) :: a -> a -> Bool
    (<=) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    max :: a -> a -> a
    min :: a -> a -> a

predicate NumericOrdering X Y V =
  ((V = EQ) <=> X = Y) &&
  ((V = LT) <=> X < Y) &&
  ((V = GT) <=> X > Y)
// Class membership supplies methods, not equality or ordering laws.
// These trusted arrows belong to the actual signed Int implementations.
instance Eq Int where
    assume (==) :: x:Int -> y:Int -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Int -> y:Int -> {v:Bool | v <=> x != y}

instance Ord Int where
    assume (>) :: x:Int -> y:Int -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Int -> y:Int -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Int -> y:Int -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Int -> y:Int -> {v:Bool | v <=> x <= y}
    assume compare :: x:Int -> y:Int -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Int -> y:Int -> {v:Int | v = (if x <= y then y else x)}
    assume min :: x:Int -> y:Int -> {v:Int | v = (if x <= y then x else y)}

// Native Word, like Int, uses the matching signed/unsigned GHC primops.

instance Eq Word where
    assume (==) :: x:Word -> y:Word -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Word -> y:Word -> {v:Bool | v <=> x != y}

instance Ord Word where
    assume (>) :: x:Word -> y:Word -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Word -> y:Word -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Word -> y:Word -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Word -> y:Word -> {v:Bool | v <=> x <= y}
    assume compare :: x:Word -> y:Word -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Word -> y:Word -> {v:Word | v = (if x <= y then y else x)}
    assume min :: x:Word -> y:Word -> {v:Word | v = (if x <= y then x else y)}

@-}
