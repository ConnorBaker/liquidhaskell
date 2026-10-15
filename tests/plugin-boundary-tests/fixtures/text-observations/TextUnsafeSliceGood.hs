module TextUnsafeSliceGood where

import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text (Text)
import Data.Text.Internal qualified as Internal
import Data.Text.Unsafe qualified as Unsafe

-- Unchecked slicing within the stored length keeps the slice bounded.
whole :: Text -> Text
whole text = Unsafe.takeWord8 (Unsafe.lengthWord8 text) text

rest :: Text -> Text
rest text = Unsafe.dropWord8 (Unsafe.lengthWord8 text) text

array :: ByteArray -> Text
array bytes = Internal.text bytes 0 (sizeofByteArray bytes)
