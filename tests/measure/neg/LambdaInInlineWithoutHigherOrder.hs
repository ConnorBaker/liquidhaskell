{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=requires the --higherorder flag" @-}

-- | The `inline` arm of `tests/reflect/neg/LambdaWithoutHigherOrder.hs`.
--
--   An inlined body is lifted by `coreToFun` and substituted into every
--   specification that names it, so the lambda reached the solver from a
--   refinement type rather than from a PLE unfolding -- and crashed the same
--   way (`unknown constant x##1`). The refusal sits on `coreToFun`'s result,
--   so the error names the inlined function. Before the fix this module failed
--   with the crash, which the substring expectation does not accept.
module LambdaInInlineWithoutHigherOrder where

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ inline mkI @-}
mkI :: Int -> Int
mkI n = apply (\x -> x + 1) n

{-@ useIt :: n:Int -> {v:Int | v == mkI n} @-}
useIt :: Int -> Int
useIt n = apply (\x -> x + 1) n
