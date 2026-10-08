{-# LANGUAGE DataKinds #-}

module LiteralClient where

import LiteralProducer

{-@ symbolClient :: x:Named -> {v:Named | v == x} @-}
symbolClient :: Named -> Named
symbolClient = symbolIdentity

{-@ natClient :: x:Counted -> {v:Counted | v == x} @-}
natClient :: Counted -> Counted
natClient = natIdentity

{-@ charClient :: x:Lettered -> {v:Lettered | v == x} @-}
charClient :: Lettered -> Lettered
charClient = charIdentity
