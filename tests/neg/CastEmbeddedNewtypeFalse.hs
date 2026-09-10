{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module CastEmbeddedNewtypeFalse where

import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

-- A cast preserves the embedded set; it cannot prove the opposite relation.
{-@ forged :: values:Set Int -> {v:WrappedSet | v /= values} @-}
forged :: Set Int -> WrappedSet
forged = WrappedSet
