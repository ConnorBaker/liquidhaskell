{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | The constructor passed as a value under `--higherorder` WITHOUT
--   `--etabeta`: eta-reduction in `firstOrderOnly` proves it where the kept
--   lambda does not.
--
--   Same source as `tests/reflect/pos/ConstructorAsValue.hs`. With
--   `--higherorder` the lambda `\ds -> W ds` is representable, so a fix that
--   only ran eta without the flag would leave it in place -- and PLE cannot
--   beta-reduce `(\ds -> W ds) n` without `--etabeta`, so `mkW n == W n` is
--   then `Liquid Type Mismatch`. Eta-reducing it to `apply W n` regardless of
--   the flag gives SAFE (2 constraints checked). Without `--adt` no datatype is
--   declared to z3, so the bare `W` is an `Int`-sorted constant and the reduced
--   term is well sorted (contrast `tests/reflect/neg/ConstructorAsValueAdt.hs`).
--
--   Before (lambda kept under `--higherorder`, no `--etabeta`): UNSAFE, Liquid
--   Type Mismatch. After: SAFE (2). `LambdaWithHigherOrder.hs` is the lambda
--   eta cannot remove, which needs `--etabeta` on top.
module ConstructorAsValueHigherOrder where

data W = W !Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = apply W n

{-@ mkWIsW :: n:Int -> {v:() | mkW n == W n} @-}
mkWIsW :: Int -> ()
mkWIsW _ = ()
