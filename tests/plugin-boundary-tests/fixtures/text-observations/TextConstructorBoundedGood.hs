module TextConstructorBoundedGood where

import Data.Text (Text)
import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text.Internal qualified as Internal

whole :: ByteArray -> Text
whole array = Internal.Text array 0 (sizeofByteArray array)
