{-@ LIQUID "--ple" @-}
{-@ LIQUID "--adt" @-}
{-@ LIQUID "--expect-error-containing=requires the --higherorder flag" @-}

-- | The constructor passed as a value, under `--adt` WITHOUT `--higherorder`:
--   refused, not crashed.
--
--   Same source as `tests/reflect/pos/ConstructorAsValue.hs`. `--adt` makes
--   `ToFixpoint.makeDecls` declare `W` to z3 through `declare-datatypes`, and
--   a bare datatype constructor in argument position is then read at the sort
--   `(Array Int W)`: the eta-reduced `apply W n` is `crash: SMTLIB2 respSat =
--   Error "... unknown constant apply##1 (Int (Array Int W)) declared:
--   (declare-fun apply##1 (Int Int) Int)"`, and the lambda kept is the
--   parent's `unknown constant ds_dPJ##1`. Neither encoding works without
--   `--higherorder`, so `firstOrderOnly` withholds eta from a lambda whose
--   result has a data constructor at its head when `--adt` is on, and refuses
--   it:
--
--   > Cannot lift Haskell function `mkW` to logic
--   > the body contains a lambda, which requires the --higherorder flag
--
--   Pinned by substring, not `--expect-any-error`, because on the parent this
--   module ALSO fails, with the crash, and the weaker form would be discharged
--   by the defect. Before: the crash (parent), and the `apply##1` crash with
--   eta applied under `--adt`. After: the refusal above.
--
--   Out of scope: from -O1 up GHC eta-reduces this lambda itself and under
--   `--adt` `workerApp` is off, so `mkW` lifts to `apply $WW n` and the claim
--   is UNSAFE rather than refused -- a pre-existing `--adt` limitation.
module ConstructorAsValueAdt where

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
