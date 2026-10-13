module TextOrdGenericMinBad where

import Data.Text (Text)

generic :: (Ord a) => a -> a -> a
generic = min
{-# NOINLINE generic #-}

choose :: Text -> Text -> Text
choose = generic
