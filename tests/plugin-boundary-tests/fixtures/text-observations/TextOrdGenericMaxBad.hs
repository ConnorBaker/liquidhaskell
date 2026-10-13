module TextOrdGenericMaxBad where

import Data.Text (Text)

generic :: (Ord a) => a -> a -> a
generic = max
{-# NOINLINE generic #-}

choose :: Text -> Text -> Text
choose = generic
