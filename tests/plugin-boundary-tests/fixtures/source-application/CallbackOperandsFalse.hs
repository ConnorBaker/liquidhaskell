module CallbackOperandsFalse where

import Data.Maybe (fromJust, isJust)

-- The callback's operands are swapped in the result: agrees need not be
-- symmetric.
{-@ pick :: agrees:(a -> a -> Bool) -> x:{Maybe a | isJust x}
      -> {y:Maybe a | isJust y && agrees (fromJust x) (fromJust y)}
      -> {v:a | agrees (fromJust y) v} @-}
pick :: (a -> a -> Bool) -> Maybe a -> Maybe a -> a
pick _ (Just x) _ = x
