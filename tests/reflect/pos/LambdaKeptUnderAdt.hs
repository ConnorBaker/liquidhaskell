{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

-- | GUARD: under `--adt` (implied by `--reflection`) the eta step in
--   `firstOrderOnly` must NOT reduce a lambda whose result would be a bare or
--   partially applied DATA CONSTRUCTOR; with `--higherorder` also on (as
--   `--reflection` implies) the lambda is kept and serialized instead.
--
--   `mkB = Box (\s -> W s)` is the constructor-as-value lambda of
--   `ConstructorAsValue.hs`, stored in a field instead of handed to `apply`.
--   Under `--reflection` the module's datatypes reach z3 through
--   `declare-datatypes`, so a bare `W` is read by z3 at the function-as-array
--   sort `(Array Int W)` while `Box`'s field is declared `Int`: eta-reduced to
--   `Box W` the module is `crash: SMTLIB2 respSat = Error "... unknown constant
--   Box ((Array Int W)) declared: (declare-fun Box (Int) Box)"` -- no verdict,
--   no binder. The lambda kept serializes as an `Int`-sorted `smt_lambda##`
--   and the module is SAFE (2 constraints checked).
--
--   The variable is `--adt`, not `--higherorder`: the same source under
--   `--ple --higherorder --etabeta` alone (no datatypes declared) is SAFE (2)
--   with the lambda eta-reduced to `Box W` as well, because without `--adt`
--   every symbol is an `Int`-sorted `declare-fun`. Under `--ple --adt` without
--   `--higherorder` neither encoding works and the definition is refused
--   (`tests/reflect/neg/ConstructorAsValueAdt.hs`).
--
--   `tests/ple/pos/MonadState.hs` pins the same guard at the partial-application
--   shape (`State $ \s -> MkPair x s` must not become `State (MkPair x)`).
--   Before this commit: SAFE (2), measured on the parent library through the
--   sibling arm `H_BareEscape` (this source minus the `Proof` import, which the
--   parent build had no `liquid-prelude` for). With eta applied to this lambda
--   under `--reflection`: the crash above. After: SAFE (2) at -O0 and -O2.
module LambdaKeptUnderAdt where

import Language.Haskell.Liquid.ProofCombinators

data W = W Int

{-@ data Box = Box { unBox :: Int -> W } @-}
data Box = Box { unBox :: Int -> W }

{-@ reflect mkB @-}
mkB :: Box
mkB = Box (\s -> W s)

{-@ prop :: n:Int -> { unBox mkB n == W n } @-}
prop :: Int -> Proof
prop _ = trivial
