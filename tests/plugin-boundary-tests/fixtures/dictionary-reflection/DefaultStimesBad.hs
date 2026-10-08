module DefaultStimesBad where

import Data.Semigroup (stimes)

data Box = Box Bool

instance Semigroup Box where
    _ <> right = right

use :: Box
use = stimes (1 :: Int) (Box False)
