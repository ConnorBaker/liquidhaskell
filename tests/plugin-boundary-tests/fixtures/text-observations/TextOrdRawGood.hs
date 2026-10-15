module TextOrdRawGood where

import Data.Text (Text)

-- Every Text is a bounded slice, so comparison has no further domain.
chooseMin, chooseMax :: Text -> Text -> Text
chooseMin = min
chooseMax = max

generic :: (Ord a) => a -> a -> a
generic = min
{-# NOINLINE generic #-}

chooseGeneric :: Text -> Text -> Text
chooseGeneric = generic

choose :: Text -> Text -> Ordering
choose = compare

{-@ bounded :: Text -> {v:Text | tbounds v} @-}
bounded :: Text -> Text
bounded text = text
