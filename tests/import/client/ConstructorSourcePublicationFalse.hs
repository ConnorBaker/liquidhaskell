module ConstructorSourcePublicationFalse where

import ConstructorSourcePublicationLib


{-@ pack :: x:Int -> y:{Int | y /= x}
         -> {v:Packet | countValue (packetCount v) == packetOther v} @-}
pack :: Int -> Int -> Packet
pack x y = Packet (Count x) y
{-# NOINLINE pack #-}
