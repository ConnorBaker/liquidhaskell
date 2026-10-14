{-# LANGUAGE NoImplicitPrelude #-}

module ImportedAbstractMethodGood where

import ImportedCarrier (Pick (..))

-- At an abstract dictionary the method is an uninterpreted function of that
-- dictionary and its arguments: a call denotes exactly that application.
{-@ viaMethod :: Pick a => x:a -> {v:a | v == pick x} @-}
viaMethod :: Pick a => a -> a
viaMethod x = pick x
