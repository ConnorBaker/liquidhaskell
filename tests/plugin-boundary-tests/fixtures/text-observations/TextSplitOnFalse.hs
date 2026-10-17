module TextSplitOnFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ nonemptyPieces :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:{Text | tvalid src}
      -> [{v:Text | 0 < tbytes v}] @-}
nonemptyPieces :: Text -> Text -> [Text]
nonemptyPieces pat src = Text.splitOn pat src
