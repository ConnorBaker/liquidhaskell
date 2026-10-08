{-# LANGUAGE GADTs #-}

module MeasureGadtFalse where

data T a where
    C :: T ()

{-@ measure m @-}
{-@ m :: T a -> Int @-}
m :: T a -> Int
m C = 0

{-@ go :: v:T a -> {n:Int | n = m v} @-}
go :: T a -> Int
go C = 1
