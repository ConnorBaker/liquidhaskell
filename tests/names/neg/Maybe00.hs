{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The `isJust` define is an EQUALITY with the measure, not a licence: a
--   reflected `isJust` applied to a `Nothing` field must still be false.
--   Red with and without the define -- without it the application is
--   uninterpreted and undecided, with it PLE decides it false.
--
--   One arm per module: a module-level expectation is discharged by a single
--   failing binder, so two arms in one file would let either mask the other.
module Maybe00 where

import Data.Maybe (isJust)

{-@ data R = R { sel :: Maybe Int, flag :: Bool } @-}
data R = R { sel :: Maybe Int, flag :: Bool }

{-@ reflect hasSel @-}
hasSel :: R -> Bool
hasSel r = isJust (sel r) || flag r

-- FALSE: `isJust Nothing || False`.
{-@ hasSelNothing :: u : () -> { v : () | hasSel (R Nothing False) } @-}
hasSelNothing :: () -> ()
hasSelNothing _ = ()
