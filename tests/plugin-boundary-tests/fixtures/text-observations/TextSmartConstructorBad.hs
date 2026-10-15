module TextSmartConstructorBad where

import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text (Text)
import Data.Text.Internal qualified as Internal

-- The smart constructor does not check a nonempty slice.
beyond :: ByteArray -> Text
beyond bytes = Internal.text bytes 1 (sizeofByteArray bytes)
