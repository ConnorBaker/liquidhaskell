module ConstructorWholeSource where

newtype Count = Count Int
data Packet = Packet !Count !Int | Empty

{-@ measure keepPacket @-}
keepPacket :: Packet -> Packet
keepPacket packet = case packet of
    Packet _ _ -> packet
    Empty -> Packet (Count 0) 0

{-@ pack :: x:Int -> y:Int -> {v:Packet | keepPacket v == v} @-}
pack :: Int -> Int -> Packet
pack x y = Packet (Count x) y
{-# NOINLINE pack #-}
