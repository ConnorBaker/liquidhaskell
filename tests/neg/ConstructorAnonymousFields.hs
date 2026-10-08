module ConstructorAnonymousFields where

data Mixed = Mixed !Bool !Int !Int

{-@ measure first @-}
first :: Mixed -> Int
first (Mixed _ x _) = x

{-@ measure second @-}
second :: Mixed -> Int
second (Mixed _ _ y) = y

{-@ pack :: b:Bool -> x:Int -> y:{Int | y /= x}
         -> {v:Mixed | first v == second v} @-}
pack :: Bool -> Int -> Int -> Mixed
pack b x y = Mixed b x y
