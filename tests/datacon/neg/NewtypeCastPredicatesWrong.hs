{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- The left field cannot borrow the right field's incompatible predicate.
module NewtypeCastPredicatesWrong (Dual (..), swapped) where

{-@ data Dual a <p :: a -> Bool, q :: a -> Bool> = Dual { payload :: (a<p>, a<q>) } @-}
newtype Dual a = Dual { payload :: (a, a) }

{-@ swapped :: Dual <{\v -> 0 <= v}, {\v -> v < 0}> Int -> {v:Int | v < 0} @-}
swapped :: Dual Int -> Int
swapped (Dual (left, _)) = left

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
