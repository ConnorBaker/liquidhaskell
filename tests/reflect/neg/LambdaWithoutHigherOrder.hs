{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=requires the --higherorder flag" @-}

-- | A reflected body with a lambda that eta-reduction CANNOT remove, checked
--   without `--higherorder`.
--
--   `\x -> x + 1` has a body that is not an application to its bound variable,
--   so `firstOrderOnly` is left with an `ELam` and refuses the definition:
--
--   > Cannot lift Haskell function `mkI` to logic
--   > the body contains a lambda, which requires the --higherorder flag ...
--
--   located at the `reflect` pragma. Before this refusal existed, `coreToLg`
--   lifted the lambda unconditionally while liquid-fixpoint can only serialize
--   one under `allowHO` (`Defunctionalize` renames the binder to `lam_arg##i`
--   only then; `Serialize.smt2Lam` always renders it as `x##0`), so PLE's
--   first unfolding of `mkI` handed z3 an undeclared binder and the whole
--   query died with `crash: SMTLIB2 respSat = Error "... unknown constant
--   x##0"` -- no verdict, no location, no binder, no hint that a flag exists.
--
--   The expectation names the new error's substring rather than accepting any
--   error, because before the fix this module ALSO failed -- with the crash --
--   and `--expect-any-error` would have been discharged by the very defect
--   this test exists to catch.
--
--   `tests/reflect/pos/LambdaWithHigherOrder.hs` is the same source with the
--   flag on: SAFE, so the refusal names a flag that really makes the term work.
--   `tests/reflect/pos/ConstructorAsValue.hs` is the lambda eta DOES remove.
module LambdaWithoutHigherOrder where

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkI @-}
mkI :: Int -> Int
mkI n = apply (\x -> x + 1) n

{-@ mkIIsInc :: n:Int -> {v:() | mkI n == n + 1} @-}
mkIIsInc :: Int -> ()
mkIIsInc _ = ()
