module TextConstructorUnboundedBad where

import Data.Text (Text)
import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text.Internal qualified as Internal

-- A slice past the array's end cannot be formed in checked code.
beyond :: ByteArray -> Text
beyond array = Internal.Text array 0 (sizeofByteArray array + 1)
