module TextBreakStripSplitGood where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ firstMatch :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:{Text | tvalid src}
      -> ({v:Text | tvalid v}, {v:Text | tvalid v}) @-}
firstMatch :: Text -> Text -> (Text, Text)
firstMatch pat src = Text.breakOn pat src

{-@ rawMatch :: pat:{Text | 0 < tbytes pat} -> src:Text -> (Text, Text) @-}
rawMatch :: Text -> Text -> (Text, Text)
rawMatch pat src = Text.breakOn pat src

{-@ trimmed :: t:{Text | tvalid t} -> {v:Text | tvalid v} @-}
trimmed :: Text -> Text
trimmed t = Text.strip t

{-@ pieces :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:{Text | tvalid src}
      -> [{v:Text | tvalid v}] @-}
pieces :: Text -> Text -> [Text]
pieces pat src = Text.splitOn pat src
