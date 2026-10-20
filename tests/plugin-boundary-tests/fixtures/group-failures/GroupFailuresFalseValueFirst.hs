module GroupFailuresFalseValueFirst where

{-@ bad :: {v:Int | false} @-}
bad :: Int
bad = 0

{-@ other :: {v:Int | v > 0} @-}
other :: Int
other = 0
