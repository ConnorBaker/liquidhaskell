module ConstructorPolymorphicReflection where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

data Box a = Box a

{-@ reflect makeBox @-}
makeBox :: Int -> Box Int
makeBox x = Box x

{-@ law :: x:Int -> {makeBox x == Box x} @-}
law :: Int -> ()
law _ = ()

data Packet a = Packet !a !Int

{-@ reflect makePacket @-}
makePacket :: Int -> Int -> Packet Int
makePacket x y = Packet x y

{-@ packetLaw :: x:Int -> y:Int -> {makePacket x y == Packet x y} @-}
packetLaw :: Int -> Int -> ()
packetLaw _ _ = ()
