{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- Representation bounds and refined type arguments survive both directions.
module NewtypeCastRefined where

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | len v > 0} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-@ singleton :: value:a -> {v:Nonempty a | items v == [value]} @-}
singleton :: a -> Nonempty a
singleton value = Nonempty [value]

{-@ extract :: value:Nonempty a -> {v:[a] | len v > 0 && v == items value} @-}
extract :: Nonempty a -> [a]
extract (Nonempty values) = values

{-@ firstNatural :: Nonempty Nat -> Nat @-}
firstNatural :: Nonempty Int -> Int
firstNatural (Nonempty values) = case values of
  [] -> 0
  first : _ -> first

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity argument = argument - 1
