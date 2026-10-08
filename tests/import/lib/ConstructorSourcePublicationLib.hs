module ConstructorSourcePublicationLib where

newtype Count = Count Int
data Packet = Packet {-# UNPACK #-} !Count !Int

{-@ measure countValue @-}
countValue :: Count -> Int
countValue (Count n) = n

{-@ measure packetCount @-}
packetCount :: Packet -> Count
packetCount (Packet count _) = count

{-@ measure packetOther @-}
packetOther :: Packet -> Int
packetOther (Packet _ other) = other
