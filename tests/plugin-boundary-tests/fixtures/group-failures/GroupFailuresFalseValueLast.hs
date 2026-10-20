module GroupFailuresFalseValueLast where

{-@ other :: {v:Int | v > 0} @-}
other :: Int
other = 0

{-@ bad :: {v:Int | false} @-}
bad :: Int
bad = 0
