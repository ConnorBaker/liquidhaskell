module ConstructorBoxedSource where

newtype Count = Count Int
data Packet = Packet !Count !Int

{-@ measure countValue @-}
countValue :: Count -> Int
countValue (Count n) = n

{-@ measure packetCount @-}
packetCount :: Packet -> Count
packetCount (Packet c _) = c

{-@ measure packetOther @-}
packetOther :: Packet -> Int
packetOther (Packet _ n) = n

{-@ pack :: x:Int -> y:Int
         -> {v:Packet | countValue (packetCount v) == x && packetOther v == y} @-}
pack :: Int -> Int -> Packet
pack x y = Packet (Count x) y

{-# NOINLINE pack #-}
