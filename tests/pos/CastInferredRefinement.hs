module CastInferredRefinement (observed) where

newtype Wrapped = Wrapped Int

-- Keep this binding private: unspecified exported values get true contracts,
-- whereas this binding exercises inference of a fresh result refinement.
wrapped :: Wrapped
wrapped = Wrapped 0

observed :: Int
observed = case wrapped of Wrapped n -> n

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
