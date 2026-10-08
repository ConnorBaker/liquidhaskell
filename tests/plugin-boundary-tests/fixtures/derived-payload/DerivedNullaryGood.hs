module DerivedNullaryGood where

data Token = Token deriving (Bounded)

{-@ instance Bounded Token where
      minBound :: {value:Token | value == Token}
      maxBound :: Token @-}

{-@ good :: {value:Token | value == Token} @-}
good :: Token
good = minBound
