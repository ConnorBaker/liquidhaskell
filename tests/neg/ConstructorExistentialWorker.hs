{-# LANGUAGE GADTs #-}

module ConstructorExistentialWorker where

newtype Table row = Table [row]

data Package where
    Package :: (Show row) => !(Table row) -> Bool -> Package

{-@ bad :: input:Package -> {v:Package | v /= input} @-}
bad :: Package -> Package
bad input@(Package (Table _) _) = input
