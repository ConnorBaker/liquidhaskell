{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | False-claim twin of `tests/reflect/pos/ConstructorAsValueLambda.hs`: the
--   constructor lambda written out in the source, `apply (\x -> W x) n`,
--   claiming `mkW n == W (n + 1)`. UNSAFE, so eta added no false fact. Pinned
--   by substring because before this commit the module failed with the
--   fixpoint crash (`unknown constant x##...##0`), which `--expect-any-error`
--   would have accepted.
module ConstructorAsValueLambdaFalse where

data W = W !Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = apply (\x -> W x) n

{-@ mkWIsNotW :: n:Int -> {v:() | mkW n == W (n + 1)} @-}
mkWIsNotW :: Int -> ()
mkWIsNotW _ = ()
