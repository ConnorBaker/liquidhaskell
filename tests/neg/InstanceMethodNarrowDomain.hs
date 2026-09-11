{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodNarrowDomain where

class Dispatch a where
    dispatch :: a -> Int -> Int

data Token = Token

-- An instance-only precondition cannot narrow the domain promised by an
-- unrefined class: polymorphic callers do not carry that restriction.
{-@ instance Dispatch Token where
      dispatch :: Token -> {n:Int | n > 0} -> Int
  @-}
instance Dispatch Token where
    dispatch _ n = if n > 0 then n else error "excluded only by instance contract"

genericCall :: (Dispatch a) => a -> Int
genericCall x = dispatch x 0

reachable :: Int
reachable = genericCall Token

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
