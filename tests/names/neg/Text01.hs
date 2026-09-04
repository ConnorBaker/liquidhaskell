{-@ LIQUID "--expect-any-error" @-}
-- | `drop` shrinks; it must not be provable that it grows.
module Text01 where

import Data.Text

{-@ dropGrows :: t : Text -> { s : Text | tlen t < tlen s } @-}
dropGrows :: Text -> Text
dropGrows = Data.Text.drop 1
