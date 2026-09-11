{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodOddDomain where

class Compare a where
    cmax :: a -> a -> a
    cmin :: a -> a -> a

-- Preserve the old Inst00 contract as a negative substitutability test.
-- Even a total implementation cannot export an instance contract whose
-- input domain is smaller than the class domain seen by generic callers.
{-@ instance Compare Int where
      cmax :: Odd -> Odd -> Odd
      cmin :: Int -> Int -> Int
  @-}
instance Compare Int where
    cmax y x = if x >= y then x else y
    cmin y x = if x >= y then x else y

genericCall :: (Compare a) => a -> a
genericCall x = cmax x x

evenCall :: Int
evenCall = genericCall 0

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
