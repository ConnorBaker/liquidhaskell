module CastEstablishedRefinement where

newtype Wrapped = Wrapped Int

{-@ measure wrappedValue @-}
wrappedValue :: Wrapped -> Int
wrappedValue (Wrapped n) = n

-- Newtype constructor facts still establish valid result refinements.
{-@ zero :: {v : Wrapped | wrappedValue v == 0} @-}
zero :: Wrapped
zero = Wrapped 0

{-@ wrap :: n:Int -> {v : Wrapped | wrappedValue v == n} @-}
wrap :: Int -> Wrapped
wrap = Wrapped

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
