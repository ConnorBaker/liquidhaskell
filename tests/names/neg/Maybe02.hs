{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The `fromJust` define is an EQUALITY with the measure, not a licence: a
--   reflected `fromJust (Just n)` is `n` and no other number. One arm per
--   module.
module Maybe02 where

import Data.Maybe (fromJust)

{-@ reflect unwrap @-}
{-@ unwrap :: { m : Maybe Int | isJust m } -> Int @-}
unwrap :: Maybe Int -> Int
unwrap m = fromJust m

-- FALSE: off by one.
{-@ unwrapJust :: n : Int -> { v : () | unwrap (Just n) == n + 1 } @-}
unwrapJust :: Int -> ()
unwrapJust _ = ()
