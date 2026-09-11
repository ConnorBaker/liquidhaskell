{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodPartial where

data Broken = Broken

-- The private dictionary method must not infer an empty input domain while
-- the public selector continues to admit every Broken value.
instance Eq Broken where
    _ == _ = error "partial instance method"

reachable :: Bool
reachable = Broken == Broken

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
