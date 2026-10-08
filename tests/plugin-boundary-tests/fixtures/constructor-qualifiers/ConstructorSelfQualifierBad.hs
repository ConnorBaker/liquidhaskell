module ConstructorSelfQualifierBad where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data Tree a = Leaf a | Branch (Map Int (Tree a))

{-@ measure height :: Tree a -> Nat @-}
{-@ data size (Tree a) height @-}
{-@ data Tree [height] a where
      Leaf :: a -> Tree a
      Branch :: Map Int (Tree a) -> Tree a
  @-}

{-@ visit :: tree:Tree a -> () / [height tree] @-}
visit :: Tree a -> ()
visit (Leaf _) = ()
visit tree@(Branch children) = Map.foldr (\_ rest -> visit tree `seq` rest) () children
