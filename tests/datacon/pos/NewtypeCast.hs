{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- Direct and eta-reduced constructor casts preserve the same interpretation.
module NewtypeCast where

newtype Direct a = Direct a
newtype Applied a = Applied [a]

{-@ measure directValue @-}
directValue :: Direct a -> a
directValue (Direct value) = value

{-@ measure appliedValues @-}
appliedValues :: Applied a -> [a]
appliedValues (Applied values) = values

{-@ wrapDirect :: value:a -> {v:Direct a | directValue v == value} @-}
wrapDirect :: a -> Direct a
wrapDirect value = Direct value

{-@ wrapApplied :: values:[a] -> {v:Applied a | appliedValues v == values} @-}
wrapApplied :: [a] -> Applied a
wrapApplied values = Applied values

{-@ extract :: value:Applied a -> {v:[a] | v == appliedValues value} @-}
extract :: Applied a -> [a]
extract (Applied values) = values

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity argument = argument - 1
