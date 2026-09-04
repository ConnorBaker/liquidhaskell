{-@ LIQUID "--expect-any-error" @-}
-- | `tappend` pins the ORDER of a concatenation. One arm per module: a
--   module-level `--expect-any-error` is discharged by a single failing
--   binder, so two arms in one file would let either mask the other.
module Text00 where

import Data.Text

-- Transposed. No arithmetic identity over `tlen` could catch this, `+` being
-- commutative.
{-@ appendOrder :: a : Text -> b : Text -> { v : Text | v == tappend a b } @-}
appendOrder :: Text -> Text -> Text
appendOrder a b = Data.Text.append b a
