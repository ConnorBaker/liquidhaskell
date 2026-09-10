{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The false-claim twin of `tests/reflect/pos/ConstructorAsValue.hs`: the
--   same source, claiming `mkW n == W (n + 1)`.
--
--   Eta-reduction ADDS a way to prove things about a definition that used to
--   crash, so the soundness question is whether it also proves a false one.
--   It does not: after `apply` is unfolded the claim is `W n == W (n + 1)`
--   and it is rejected as a `Liquid Type Mismatch`.
--
--   The expectation names that error rather than accepting any error, because
--   before the fix this module ALSO failed -- with the fixpoint crash on the
--   parent library, and with `Cannot lift Haskell function mkW` under the
--   refusal alone -- and `--expect-any-error` would have been discharged by
--   either. Only a module that gets far enough to state the claim and reject
--   it satisfies this one.
module ConstructorAsValueFalse where

data W = W !Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = apply W n

{-@ mkWIsW :: n:Int -> {v:() | mkW n == W (n + 1)} @-}
mkWIsW :: Int -> ()
mkWIsW _ = ()
