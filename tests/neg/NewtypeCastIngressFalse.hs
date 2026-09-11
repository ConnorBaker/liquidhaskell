{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | GUARD, red before and after the fix. Routing the construction through a
--   named function instead of applying the constructor directly makes the
--   body an application rather than a 'Cast', so the cast rule never sees it
--   and the false postcondition was always reported. This is the workaround
--   users reached for before the rule was fixed; the module pins that the
--   fix leaves that shape exactly as strict as it was.
--
--   Measured: UNSAFE (1) before the fix, UNSAFE (1) after it, identically at
--   -O0 and -O2 with `--check-derived --total-Haskell --no-annotations` and
--   under the suite's own flags (-XHaskell2010 -O0, no plugin options).
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastIngressFalse where

newtype P = P Int

mkP :: Int -> P
mkP = P

{-@ mk :: Int -> {v : P | false} @-}
mk :: Int -> P
mk x = mkP x
