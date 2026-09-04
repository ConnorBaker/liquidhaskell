{-@ LIQUID "--expect-any-error" @-}
-- | `breakOn`'s precondition is real: `Data.Text.breakOn` calls `emptyError`
--   on an empty pattern, so a client that cannot show `0 < tlen pat` must be
--   rejected rather than admitted.
module Text03 where

import Data.Text

{-@ breakOnUnchecked :: Text -> t : Text -> { s : Text | tlen s <= tlen t } @-}
breakOnUnchecked :: Text -> Text -> Text
breakOnUnchecked p t = snd (Data.Text.breakOn p t)
