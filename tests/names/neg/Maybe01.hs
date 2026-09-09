{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The `isNothing` define is an EQUALITY with `not (isJust x)`, not a
--   licence: a reflected `isNothing` applied to a `Just` field must still be
--   false. One arm per module.
module Maybe01 where

import Data.Maybe (isNothing)

{-@ data R = R { sel :: Maybe Int, flag :: Bool } @-}
data R = R { sel :: Maybe Int, flag :: Bool }

{-@ reflect lacksSel @-}
lacksSel :: R -> Bool
lacksSel r = isNothing (sel r)

-- FALSE: `isNothing (Just n)`.
{-@ lacksSelJust :: n : Int -> { v : () | lacksSel (R (Just n) True) } @-}
lacksSelJust :: Int -> ()
lacksSelJust _ = ()
