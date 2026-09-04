{-@ LIQUID "--expect-any-error" @-}
{-# LANGUAGE OverloadedStrings #-}

-- | The @stringlen@ bridge is an EQUALITY between two measures, not a licence.
--   A literal's @tlen@ is its character count and no other number: were the
--   invariant contradictory -- or were @stringlen@ left unconstrained and the
--   binder's environment vacuous -- this would verify too.
--
--   One arm per module: a module-level @--expect-any-error@ is discharged by a
--   single failing binder, so two arms in one file would let either mask the
--   other.
module Text04 where

import Data.Text (Text)
import qualified Data.Text

-- FALSE: @"abc"@ is three characters.
{-@ litLen :: { v : Int | v == 4 } @-}
litLen :: Int
litLen = Data.Text.length ("abc" :: Text)
