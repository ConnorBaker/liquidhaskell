module TextCountEmptyBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ anyPattern :: pat:{Text | tvalid pat} -> t:{Text | tvalid t} -> Int @-}
anyPattern :: Text -> Text -> Int
anyPattern pat t = Text.count pat t
