module TextBreakOnEndFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ suffixWhole :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:{Text | tvalid src}
      -> {v:Text | tbytes v == tbytes src} @-}
suffixWhole :: Text -> Text -> Text
suffixWhole pat src = snd (Text.breakOnEnd pat src)
