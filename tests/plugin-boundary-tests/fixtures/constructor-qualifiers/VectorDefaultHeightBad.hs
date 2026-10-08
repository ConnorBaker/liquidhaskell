module VectorDefaultHeightBad where

import Data.Vector (Vector)
import qualified Data.Vector as Vector

data Tree = Leaf | Branch (Vector Tree)

{-@ measure height :: Tree -> Nat @-}
{-@ data size (Tree) height @-}
{-@ data Tree [height] where
      Leaf :: Tree
      Branch :: Vector Tree -> Tree
  @-}
{-@ data variance Vector covariant @-}

visit :: Tree -> ()
visit Leaf = ()
visit tree@(Branch children) = Vector.foldr (\_ rest -> visit tree `seq` rest) () children
