{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--eliminate=all" @-}
module SemigroupEliminateAll where

import Data.Semigroup (stimes)

data Bucket = Unresolved | Recovered

{-@ measure recovered @-}
recovered :: Bucket -> Bool
recovered Recovered = True
recovered Unresolved = False

-- Refining only (<>) must not lose the class-owned domain of the default
-- stimes method. No qualifier inference is available in elimination-all.
{-@ instance Semigroup Bucket where
      (<>) :: left:Bucket -> right:Bucket
           -> {v:Bucket | recovered v <=> (recovered left || recovered right)} @-}
instance Semigroup Bucket where
    Recovered <> _ = Recovered
    _ <> right = right

validCall :: Bucket
validCall = stimes (2 :: Int) Recovered

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
