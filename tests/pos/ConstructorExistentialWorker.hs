{-# LANGUAGE GADTs #-}

module ConstructorExistentialWorker where

newtype Table row = Table [row]

data Package where
    Package :: (Show row) => !(Table row) -> Bool -> Package

{-@ good :: input:Package -> {v:Package | v == input} @-}
good :: Package -> Package
good input@(Package (Table _) _) = input
