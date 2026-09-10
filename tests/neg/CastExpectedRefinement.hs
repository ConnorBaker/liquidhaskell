{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- A newtype constructor becomes a Core cast. Checking that cast must not
-- assume the result refinement it is supposed to establish.
module CastExpectedRefinement where

newtype Wrapped = Wrapped Int

{-@ forged :: {v : Wrapped | false} @-}
forged :: Wrapped
forged = Wrapped 0
