{-@ LIQUID "--ple" @-}

-- | A data constructor passed as a VALUE to a reflected higher-order function,
--   checked under plain `--ple`, without `--higherorder`.
--
--   There is no lambda in the source. `W` has a strict field, so GHC's
--   desugarer turns the constructor-as-value into `\ds -> $WW ds`, and
--   `mkW n = apply W n` reaches `coreToLg` as `apply (\ds -> $WW ds) n`; the
--   worker/wrapper lifting puts `W` back, leaving `apply (\ds -> W ds) n`.
--
--   That lambda is `\x -> f x` with `x` not free in `f`, so `firstOrderOnly`
--   eta-reduces it and the lifted definition is
--
--   > define mkW (n : int) : W = { apply W n }
--
--   which liquid-fixpoint represents without `--higherorder`, exactly as it
--   represents `apply inc n` for a reflected `inc`. PLE unfolds `apply` and
--   `mkW n == W n` is PROVED.
--
--   Before: on the parent library this module reached z3 with the lambda
--   serialized as `(smt_lambda##0 ds##0 (apply##0 W ds))` and died with
--   `crash: SMTLIB2 respSat = Error "... unknown constant ds##0"` -- no
--   verdict, no location, no binder; with the refusal alone it was
--   `Cannot lift Haskell function mkW to logic ... requires the --higherorder
--   flag`. After: SAFE (2 constraints checked), at -O0, -O1 and -O2 alike.
--
--   Its false-claim twin, `tests/reflect/neg/ConstructorAsValueFalse.hs`, is
--   UNSAFE, so the proof is not vacuous. `ConstructorAsValueLazy.hs` is the
--   lazy-field shape (`\ds -> W ds`, no wrapper) and `ConstructorAsValueLambda.hs`
--   the same lambda written out in the source; `tests/reflect/neg/
--   LambdaWithoutHigherOrder.hs` is the lambda eta cannot remove.
module ConstructorAsValue where

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
