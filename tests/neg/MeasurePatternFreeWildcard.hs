{-@ LIQUID "--expect-error-containing=anonymous measure pattern wildcard '_' cannot be used in the body" @-}
{-@ LIQUID "--total-Haskell" @-}
module MeasurePatternFreeWildcard where

data Pair = Pair Int Int

{-@ measure anonymous :: Pair -> Int
      anonymous (Pair _ right) = _
  @-}
