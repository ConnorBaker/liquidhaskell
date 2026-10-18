module TextEqRepresentationProbe where

import Data.Text (Text)
import Data.Text.Internal qualified as Internal

-- Logical Text equality is the equality of the representation.
{-@ injective :: x:Text -> y:{Text | y == x} -> {v:Bool | v} @-}
injective :: Text -> Text -> Bool
injective (Internal.Text _ o _) (Internal.Text _ p _) = o == p

-- text-2.1.3's (==) ignores offsets: pack "ab" == drop 1 (pack "xab") at
-- offsets 0 and 1. This claim is false for that pair.
{-@ sameOffset :: Text -> Text -> {v:Bool | v} @-}
sameOffset :: Text -> Text -> Bool
sameOffset x@(Internal.Text _ o _) y@(Internal.Text _ p _) = not (x == y) || o == p
