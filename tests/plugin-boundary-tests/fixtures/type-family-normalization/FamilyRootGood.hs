{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module FamilyRootGood where

import GHC.Types (Int (I#))

type family Carrier a where
    Carrier Int = Int

{-@ embed Carrier * as int @-}

{-@ positive :: {v:Carrier Int | v > 0} @-}
positive :: Carrier Int
positive = I# 1#
