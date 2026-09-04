-- | The facts in `Data.Text_LHAssumptions`. Note this module imports only
--   `Data.Text`: the assumption module is discovered from that import.
module Text00 where

import Data.Text

{-@ nullIffEmpty :: t : Text -> { b : Bool | b <=> tlen t == 0 } @-}
nullIffEmpty :: Text -> Bool
nullIffEmpty = Data.Text.null

{-@ appendLen :: a : Text -> b : Text -> { v : Int | v == tlen a + tlen b } @-}
appendLen :: Text -> Text -> Int
appendLen a b = Data.Text.length (Data.Text.append a b)

{-@ consLen :: c : Char -> t : Text -> { v : Int | v == tlen t + 1 } @-}
consLen :: Char -> Text -> Int
consLen c t = Data.Text.length (Data.Text.cons c t)

-- ORDER, not just the sum. This is why `tappend` is an uninterpreted measure:
-- an arithmetic identity over `tlen` cannot see a transposition, since `+` is
-- commutative.
{-@ appendOrder :: a : Text -> b : Text -> { v : Text | v == tappend a b } @-}
appendOrder :: Text -> Text -> Text
appendOrder = Data.Text.append

{-@ dropShrinks :: t : Text -> { s : Text | tlen s <= tlen t } @-}
dropShrinks :: Text -> Text
dropShrinks = Data.Text.drop 1

{-@ unconsNonEmpty :: { t : Text | 0 < tlen t } -> { m : Maybe (Char, Text) | isJust m } @-}
unconsNonEmpty :: Text -> Maybe (Char, Text)
unconsNonEmpty = Data.Text.uncons

-- The fixed point the opaque reflection exists for.
{-@ folded :: Text -> { n : Text | n == Data.Text.toLower n } @-}
folded :: Text -> Text
folded = Data.Text.toLower

-- The link to the ARGUMENT, which exercises the explicit
-- `v == Data.Text.toLower n` conjunct: the strengthening the opaque reflection
-- performs is not part of the exported spec.
{-@ link :: t : Text -> { v : Text | v == Data.Text.toLower t } @-}
link :: Text -> Text
link = Data.Text.toLower

-- ORDER again, for the other declaration-only measure.
{-@ consOrder :: c : Char -> t : Text -> { v : Text | v == tcons c t } @-}
consOrder :: Char -> Text -> Text
consOrder = Data.Text.cons

-- `breakOn` carries the module's only PRECONDITION, so it is the only spec
-- here that can stop a client verifying. `cons` is what discharges it: its
-- result has `tlen == 1 + tlen t`, hence `0 < tlen`.
{-@ breakOnShrinks :: Char -> Text -> t : Text -> { s : Text | tlen s <= tlen t } @-}
breakOnShrinks :: Char -> Text -> Text -> Text
breakOnShrinks c p t = snd (Data.Text.breakOn (Data.Text.cons c p) t)
