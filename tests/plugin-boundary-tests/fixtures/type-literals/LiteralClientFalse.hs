{-# LANGUAGE DataKinds #-}

module LiteralClientFalse where

import LiteralProducer

{-@ falseIdentity :: x:Named -> {v:Named | v /= x} @-}
falseIdentity :: Named -> Named
falseIdentity = symbolIdentity
