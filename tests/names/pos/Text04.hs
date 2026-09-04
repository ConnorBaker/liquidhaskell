{-# LANGUAGE OverloadedStrings #-}

-- | The @stringlen@ bridge in `Data.Text_LHAssumptions`, which is what makes an
-- @OverloadedStrings@ `Data.Text.Text` literal usable in the logic.
--
-- `Data.String_LHAssumptions` gives an `IsString` literal only
-- @len i == stringlen o@, over the polymorphic `stringlen` measure. Without
-- @tlen t == stringlen t@ the logic therefore knows the CHARACTER COUNT of a
-- `Text` literal and nothing whatever about its @tlen@ -- which leaves
-- @breakOn@'s @0 < tlen pat@ precondition undischargeable at a needle that is
-- visibly two characters long. It is the counterpart of
-- `Data.ByteString_LHAssumptions`'s @bslen bs == stringlen bs@, not a new idea.
module Text04 where

import Data.Text (Text)
import qualified Data.Text

-- The literal's length reaches @tlen@ at all.
{-@ litLen :: { v : Int | v == 3 } @-}
litLen :: Int
litLen = Data.Text.length ("abc" :: Text)

-- And is enough to discharge the module's one precondition. Written as an
-- application rather than point-free: a composition through `snd` loses the
-- link between the argument and the result for reasons that have nothing to do
-- with this invariant.
{-@ breakOnLiteral :: t : Text -> { s : Text | tlen s <= tlen t } @-}
breakOnLiteral :: Text -> Text
breakOnLiteral t = snd (Data.Text.breakOn ("${" :: Text) t)
