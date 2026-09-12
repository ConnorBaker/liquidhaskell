{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- Two independent abstract predicates must be instantiated in their declared order.
module NewtypeCastPredicates (Dual (..), first, second, construct) where

{-@ data Dual a <p :: a -> Bool, q :: a -> Bool> = Dual { payload :: (a<p>, a<q>) } @-}
newtype Dual a = Dual { payload :: (a, a) }

{-@ first :: Dual <{\v -> 0 <= v}, {\v -> v < 0}> Int -> Nat @-}
first :: Dual Int -> Int
first (Dual (left, _)) = left

{-@ second :: Dual <{\v -> 0 <= v}, {\v -> v < 0}> Int -> {v:Int | v < 0} @-}
second :: Dual Int -> Int
second (Dual (_, right)) = right

{-@ construct :: left:Nat -> right:{v:Int | v < 0} -> Dual <{\v -> 0 <= v}, {\v -> v < 0}> Int @-}
construct :: Int -> Int -> Dual Int
construct left right = Dual (left, right)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
