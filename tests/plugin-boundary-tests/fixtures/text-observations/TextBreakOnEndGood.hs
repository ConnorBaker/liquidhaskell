module TextBreakOnEndGood where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ lastPiece :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:{Text | tvalid src}
      -> ({v:Text | tvalid v}, {v:Text | tvalid v}) @-}
lastPiece :: Text -> Text -> (Text, Text)
lastPiece pat src = Text.breakOnEnd pat src
