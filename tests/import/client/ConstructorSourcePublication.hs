module ConstructorSourcePublication where

import ConstructorSourcePublicationLib

-- The exported constructor contract uses Count, not its worker's Int# slot.
{-@ pack :: x:Int -> y:Int
         -> {v:Packet | countValue (packetCount v) == x && packetOther v == y} @-}
pack :: Int -> Int -> Packet
pack x y = Packet (Count x) y
{-# NOINLINE pack #-}
