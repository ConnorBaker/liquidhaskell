module TextSingletonAnyFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ twoScalars :: Char -> {t:Text | tlen t == 2} @-}
twoScalars :: Char -> Text
twoScalars = Text.singleton

{-@ oneByte :: Char -> {t:Text | tbytes t == 1} @-}
oneByte :: Char -> Text
oneByte = Text.singleton

{-@ keepsSurrogate :: c:Char -> {t:Text | thead t == c} @-}
keepsSurrogate :: Char -> Text
keepsSurrogate = Text.singleton

{-@ surrogateKept :: {t:Text | thead t == (lit "55296" Char)} @-}
surrogateKept :: Text
surrogateKept = Text.singleton '\xD800'

{-@ latinOneByte :: {t:Text | tbytes t == 1} @-}
latinOneByte :: Text
latinOneByte = Text.singleton '\233'

{-@ unrelated :: Char -> u:Text -> {v:Bool | tvalid u} @-}
unrelated :: Char -> Text -> Bool
unrelated c _ = Text.null (Text.singleton c)

{-@ vacuous :: Char -> {t:Text | false} @-}
vacuous :: Char -> Text
vacuous = Text.singleton
