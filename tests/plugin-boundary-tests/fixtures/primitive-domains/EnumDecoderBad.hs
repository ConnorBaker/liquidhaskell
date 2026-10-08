{-# LANGUAGE MagicHash #-}

module EnumDecoderBad where

import GHC.Exts (Int#, tagToEnum#)

data Choice = First | Second

{-# NOINLINE decoder #-}
{-@ decoder :: Int# -> Choice @-}
decoder :: Int# -> Choice
decoder x = tagToEnum# x

wrong :: Choice
wrong = decoder 2#
