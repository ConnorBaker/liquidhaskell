module VarianceGood where

import Data.Vector (Vector)
import qualified Data.Vector as Vector

{-@ data variance Vector covariant @-}

data Wrapped a = Wrapped (Vector a)
data Recursive = End | More (Wrapped Recursive)

wrappedValue :: Recursive
wrappedValue = More (Wrapped (Vector.singleton End))

data Phantom a = Phantom
data PhantomRecursive = PhantomRecursive (Phantom (PhantomRecursive -> Int))

phantomValue :: PhantomRecursive
phantomValue = PhantomRecursive Phantom

data Tree a = Leaf a | Branch (Tree a) (Tree a)

{-@ widenTree :: Tree Nat -> Tree Int @-}
widenTree :: Tree Int -> Tree Int
widenTree x = x

data LeftTree a = LeftLeaf a | LeftBranch (RightTree a)
data RightTree a = RightLeaf a | RightBranch (LeftTree a)

{-@ widenMutual :: LeftTree Nat -> LeftTree Int @-}
widenMutual :: LeftTree Int -> LeftTree Int
widenMutual x = x

data Bush a = Bud a | Bush (Bush (Bush a))

{-@ widenBush :: Bush Nat -> Bush Int @-}
widenBush :: Bush Int -> Bush Int
widenBush x = x

data Negative a = Negative (a -> Int)

{-@ narrowNegative :: Negative Int -> Negative Nat @-}
narrowNegative :: Negative Int -> Negative Int
narrowNegative x = x

data Nested a = Stop a | Next (Nested (a -> Int))

{-@ preserveNested :: Nested Nat -> Nested Nat @-}
preserveNested :: Nested Int -> Nested Int
preserveNested x = x

{-@ inhabited :: (Tree Int, LeftTree Int, Bush Int, Negative Nat, Nested Nat) @-}
inhabited :: (Tree Int, LeftTree Int, Bush Int, Negative Int, Nested Int)
inhabited =
    ( widenTree (Branch (Leaf 0) (Leaf 1))
    , widenMutual (LeftBranch (RightLeaf 2))
    , widenBush (Bush (Bud (Bud 3)))
    , narrowNegative (Negative id)
    , preserveNested (Stop 4)
    )
