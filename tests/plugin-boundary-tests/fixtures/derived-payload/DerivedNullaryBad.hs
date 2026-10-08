module DerivedNullaryBad where

data Token = Token deriving (Bounded)

{-@ instance Bounded Token where
      minBound :: {value:Token | False}
      maxBound :: Token @-}

{-@ bad :: {value:Bool | value} @-}
bad :: Bool
bad = case (minBound :: Token) of Token -> False
