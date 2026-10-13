module TotalityUndefinedUnreachable (onlyFalse, impossible, local) where

import Prelude hiding (undefined)
import qualified Prelude

-- Unreachable uses of GHC's undefined are admitted.
{-@ onlyFalse :: {v : Bool | not v} -> Int @-}
onlyFalse :: Bool -> Int
onlyFalse x = if x then Prelude.undefined else 0

{-@ impossible :: {v : Int | false} -> Int @-}
impossible :: Int -> Int
impossible _ = Prelude.undefined

-- The obligation belongs to GHC's binder, not to its occurrence name.
undefined :: Int
undefined = 3

{-@ local :: {v : Int | v == 3} @-}
local :: Int
local = undefined

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
