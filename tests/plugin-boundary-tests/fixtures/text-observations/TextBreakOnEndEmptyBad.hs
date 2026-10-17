module TextBreakOnEndEmptyBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ anyPattern :: pat:{Text | tvalid pat} -> src:{Text | tvalid src} -> (Text, Text) @-}
anyPattern :: Text -> Text -> (Text, Text)
anyPattern pat src = Text.breakOnEnd pat src
