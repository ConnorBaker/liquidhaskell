module ConstructorSelfQualifierGood where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data Tree a = Leaf a | Branch (Map Int (Tree a))
data Other = End | Next (Map Int Other)

{-@ measure height :: Tree a -> Nat @-}
{-@ data size (Tree a) height @-}
{-@ data Tree [height] a where
      Leaf :: a -> Tree a
      Branch :: Map Int (Tree a) -> Tree a
  @-}
{-@ measure depth :: Other -> Nat @-}
{-@ data size (Other) depth @-}
{-@ data Other [depth] where
      End :: Other
      Next :: Map Int Other -> Other
  @-}

{-@ visit :: tree:Tree a -> () / [height tree] @-}
visit :: Tree a -> ()
visit (Leaf _) = ()
visit (Branch children) = Map.foldr (\child rest -> visit child `seq` rest) () children

{-@ inspect :: value:Other -> () / [depth value] @-}
inspect :: Other -> ()
inspect End = ()
inspect (Next children) = Map.foldr (\child rest -> inspect child `seq` rest) () children
