module UndecodedStrip where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Unsafe

{-@ sliced :: k:Nat -> {t:Text | tvalid t && k <= tbytes t} -> Text @-}
sliced :: Int -> Text -> Text
sliced k t =
  Text.strip (Unsafe.takeWord8 k t)

arbitrary :: Text -> Text
arbitrary t =
  Text.strip t
