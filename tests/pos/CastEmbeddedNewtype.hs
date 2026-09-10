module CastEmbeddedNewtype where

import Data.Coerce (coerce)
import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

{-@ wrap :: values:Set Int -> {v:WrappedSet | v == values} @-}
wrap :: Set Int -> WrappedSet
wrap = WrappedSet

{-@ unwrap :: wrapped:WrappedSet -> {v:Set Int | v == wrapped} @-}
unwrap :: WrappedSet -> Set Int
unwrap = coerce

{-@ roundTrip :: values:Set Int -> {v:Set Int | v == values} @-}
roundTrip :: Set Int -> Set Int
roundTrip values = unwrap (wrap values)

{-@ wrappedRoundTrip :: wrapped:WrappedSet -> {v:WrappedSet | v == wrapped} @-}
wrappedRoundTrip :: WrappedSet -> WrappedSet
wrappedRoundTrip wrapped = wrap (unwrap wrapped)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
