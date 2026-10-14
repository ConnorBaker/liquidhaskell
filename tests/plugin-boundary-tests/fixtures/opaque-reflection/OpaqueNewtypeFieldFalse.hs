module OpaqueNewtypeFieldFalse where

-- A newtype specification names its field. Reflecting a function with an
-- opaque callee consults the logic names that every specification defines.
newtype Count = Count Int

{-@ newtype Count = Count { countValue :: {v:Int | 0 <= v} } @-}

helper :: Int -> Int
helper x = x

{-@ reflect forward @-}
forward :: Int -> Int
forward x = helper x

one :: Count
one = Count (-1)
