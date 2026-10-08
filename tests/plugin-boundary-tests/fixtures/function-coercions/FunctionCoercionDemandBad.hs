module FunctionCoercionDemandBad where

import Data.Coerce (coerce)

newtype Wrapped = Wrapped Int

{-@ outward :: n:Nat -> {future:Int | false} -> Wrapped / [n] @-}
outward :: Int -> Int -> Wrapped
outward n = coerce (inward n)
{-# NOINLINE outward #-}

{-@ inward :: n:Nat -> {future:Int | false} -> Int / [n] @-}
inward :: Int -> Int -> Int
inward n = coerce (outward n)
{-# NOINLINE inward #-}
