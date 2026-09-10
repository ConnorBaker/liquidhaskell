{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=requires the --higherorder flag" @-}

-- | The `measure` arm of `tests/reflect/neg/LambdaWithoutHigherOrder.hs`.
--
--   A measure alternative is lifted by `coreAltToDef`, a different entry point
--   from a reflected body, and it reached the same fixpoint crash
--   (`unknown constant x##0`) through the same unconditional `ELam` in
--   `coreToLg`. The refusal is applied where the alternative's body is lifted,
--   so the error names the measure. Before the fix this module failed with the
--   crash, which the substring expectation does not accept.
module LambdaInMeasureWithoutHigherOrder where

data W = W !Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ measure unW @-}
unW :: W -> Int
unW (W n) = apply (\x -> x + 1) n

{-@ useIt :: w:W -> {v:Int | v == unW w} @-}
useIt :: W -> Int
useIt (W n) = apply (\x -> x + 1) n
