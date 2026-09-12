{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- Two independent arguments distinguish constructor meaning from a
-- postcondition merely copied onto its result.
module NewtypeCastWrongValue where

newtype Box a = Box [a]

{-@ measure values @-}
values :: Box a -> [a]
values (Box entries) = entries

{-@ wrong :: expected:[a] -> other:[a] -> {v:Box a | values v == expected} @-}
wrong :: [a] -> [a] -> Box a
wrong _expected other = Box other

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity argument = argument - 1
