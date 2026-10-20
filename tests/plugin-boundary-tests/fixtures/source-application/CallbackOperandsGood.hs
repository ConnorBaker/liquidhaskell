module CallbackOperandsGood where

import Data.Maybe (fromJust, isJust)

-- A bound callback applied to logical operands, in a precondition and in
-- the result. The Haskell call of the callback is never made, so only the
-- logical applications relate the result to the arguments.
{-@ pick :: agrees:(a -> a -> Bool) -> x:{Maybe a | isJust x}
      -> {y:Maybe a | isJust y && agrees (fromJust x) (fromJust y)}
      -> {v:a | agrees v (fromJust y)} @-}
pick :: (a -> a -> Bool) -> Maybe a -> Maybe a -> a
pick _ (Just x) _ = x
