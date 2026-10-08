module OwnedWithText (withText) where

import Data.Aeson (Value, withText)
import Data.Aeson.Types (Parser)
import Data.Text (Text)

{-@ withText :: String -> (Text -> Parser a) -> Value -> Parser a @-}
