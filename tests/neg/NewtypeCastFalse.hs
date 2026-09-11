{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | A @newtype@ constructor application is a 'Cast' in Core. The checking rule
--   for a 'Cast' used to conjoin the EXPECTED type's own refinement onto the
--   synthesized type before emitting the subtyping obligation, so at this
--   expression the obligation read @{v | v == P x && false} <: {v | false}@ --
--   a tautology for every postcondition, including @false@.
--
--   The one spec'd binder here has the newtype construction as its WHOLE body,
--   so no other site can decide the verdict: a module with several branches
--   whose other arms are honest would be UNSAFE either way and prove nothing
--   about this rule.
--
--   Measured: SAFE (1 constraints checked) before the fix,
--   UNSAFE (1) with @Liquid Type Mismatch@ at @mk@ after it -- the same
--   verdicts and count at -O0 and -O2 with `--check-derived --total-Haskell
--   --no-annotations` and under the suite's own flags (-XHaskell2010 -O0, no
--   plugin options).
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastFalse where

newtype P = P Int

{-@ mk :: Int -> {v : P | false} @-}
mk :: Int -> P
mk x = P x
