module LogicalOperandsGood where

import Data.Maybe (fromJust, isJust)
import Data.Text (Text)

{-@ reflect textAgrees @-}
textAgrees :: Text -> Text -> Bool
textAgrees left right = left == right

-- Both arguments of the two-argument source function are logical operands.
{-@ maybeAgrees :: x:Maybe Text -> y:Maybe Text
      -> {v:Bool | v <=> (isJust y => (isJust x && textAgrees (fromJust x) (fromJust y)))} @-}
maybeAgrees :: Maybe Text -> Maybe Text -> Bool
maybeAgrees _ Nothing = True
maybeAgrees Nothing (Just _) = False
maybeAgrees (Just x) (Just y) = textAgrees x y
