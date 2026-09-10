{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | False-claim twin of `tests/reflect/pos/ConstructorAsValueLazy.hs`: the
--   lazy-field constructor as a value, `\ds -> W ds` with no wrapper, claiming
--   `mkW n == W (n + 1)`. UNSAFE, so the eta-reduced `define mkW n = apply W n`
--   added no false fact. Pinned by substring because before this commit the
--   module failed with the fixpoint crash (`unknown constant ds_dPJ##1`), which
--   `--expect-any-error` would have accepted.
module ConstructorAsValueLazyFalse where

data W = W Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = apply W n

{-@ mkWIsNotW :: n:Int -> {v:() | mkW n == W (n + 1)} @-}
mkWIsNotW :: Int -> ()
mkWIsNotW _ = ()
