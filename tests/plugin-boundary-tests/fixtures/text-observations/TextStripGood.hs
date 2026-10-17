module TextStripGood where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ afterPrefix :: p:{Text | tvalid p} -> t:{Text | tvalid t}
      -> Maybe {r:Text | tvalid r && tbytes r == tbytes t - tbytes p
                                  && tlen r == tlen t - tlen p} @-}
afterPrefix :: Text -> Text -> Maybe Text
afterPrefix p t = Text.stripPrefix p t

{-@ beforeSuffix :: p:{Text | tvalid p} -> t:{Text | tvalid t}
      -> Maybe {r:Text | tvalid r && tbytes r == tbytes t - tbytes p
                                  && tlen r == tlen t - tlen p} @-}
beforeSuffix :: Text -> Text -> Maybe Text
beforeSuffix p t = Text.stripSuffix p t

{-@ rawSuffix :: p:Text -> t:Text -> Maybe {r:Text | tbytes r <= tbytes t} @-}
rawSuffix :: Text -> Text -> Maybe Text
rawSuffix p t = Text.stripSuffix p t

{-@ folded :: t:{Text | tvalid t} -> {v:Text | tvalid v} @-}
folded :: Text -> Text
folded t = Text.toCaseFold t

{-@ occurrences :: pat:{Text | tvalid pat && 0 < tlen pat} -> t:{Text | tvalid t}
      -> {v:Int | 0 <= v} @-}
occurrences :: Text -> Text -> Int
occurrences pat t = Text.count pat t
