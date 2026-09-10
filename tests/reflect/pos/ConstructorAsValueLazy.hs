{-@ LIQUID "--ple" @-}

-- | `tests/reflect/pos/ConstructorAsValue.hs` with a LAZY field.
--
--   With no strictness there is no wrapper, so the desugarer manufactures
--   `\ds -> W ds` directly rather than `\ds -> $WW ds`; the lambda is the same
--   and so is the eta-reduction, so this pins that the fix does not depend on
--   the worker/wrapper lifting having run first.
--
--   Before: the fixpoint crash (`unknown constant ds##0`) on the parent
--   library, `Cannot lift Haskell function mkW` with the refusal alone.
--   After: SAFE (2 constraints checked).
module ConstructorAsValueLazy where

data W = W Int

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
