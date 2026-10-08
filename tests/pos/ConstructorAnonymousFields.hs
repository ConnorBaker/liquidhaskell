module ConstructorAnonymousFields where

data Mixed = Mixed !Bool !Int !Int

{-@ measure enabled @-}
enabled :: Mixed -> Bool
enabled (Mixed b _ _) = b

{-@ measure first @-}
first :: Mixed -> Int
first (Mixed _ x _) = x

{-@ measure second @-}
second :: Mixed -> Int
second (Mixed _ _ y) = y

{-@ pack :: b:Bool -> x:Int -> y:Int
         -> {v:Mixed | enabled v == b && first v == x && second v == y} @-}
pack :: Bool -> Int -> Int -> Mixed
pack b x y = Mixed b x y

{-# NOINLINE pack #-}
