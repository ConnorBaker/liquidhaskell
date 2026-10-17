module TextSingletonAnyGood where

import Data.Text (Text)
import Data.Text qualified as Text

-- text-2.1.3 singleton accepts every Char: surrogates are replaced, and the
-- result is one scalar encoded in one to four bytes.
{-@ anyObserved :: c:Char
      -> {t:Text | tvalid t && tlen t == 1 && 1 <= tbytes t && tbytes t <= 4} @-}
anyObserved :: Char -> Text
anyObserved = Text.singleton

{-@ scalarObserved :: c:{Char | c < (lit "55296" Char) || (lit "57343" Char) < c}
      -> {t:Text | tvalid t && thead t == c} @-}
scalarObserved :: Char -> Text
scalarObserved = Text.singleton

{-@ twoBytes :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 2 && thead t == (lit "233" Char)} @-}
twoBytes :: Text
twoBytes = Text.singleton '\233'

{-@ threeBytes :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 3 && thead t == (lit "8364" Char)} @-}
threeBytes :: Text
threeBytes = Text.singleton '\x20AC'

{-@ fourBytes :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 4 && thead t == (lit "1114111" Char)} @-}
fourBytes :: Text
fourBytes = Text.singleton '\x10FFFF'

{-@ surrogateReplaced :: {t:Text | tvalid t && tlen t == 1 && tbytes t == 3 && thead t == (lit "65533" Char)} @-}
surrogateReplaced :: Text
surrogateReplaced = Text.singleton '\xDFFF'

{-@ pairObserved :: Char -> Char -> {t:Text | tvalid t && tlen t == 2} @-}
pairObserved :: Char -> Char -> Text
pairObserved left right = Text.append (Text.singleton left) (Text.singleton right)
