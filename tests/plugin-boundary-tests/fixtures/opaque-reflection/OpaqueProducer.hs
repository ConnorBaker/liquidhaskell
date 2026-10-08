module OpaqueProducer (importedF) where

{-@ importedF :: Integer -> Integer @-}
{-# NOINLINE importedF #-}
importedF :: Integer -> Integer
importedF x = x + 1
