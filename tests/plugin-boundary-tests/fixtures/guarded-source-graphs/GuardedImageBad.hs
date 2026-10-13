{-# LANGUAGE NoImplicitPrelude #-}

module GuardedImageBad (bad) where

import GHC.Types (Int)
import GuardedImageProducer (A (OnlyA), only)

{-@ opaque-reflect only @-}

-- This invariant is a tautology even outside the source datatype's image.
-- Its logical call cannot authorize treating an arbitrary Int as an A.
{-@ invariant {v:Int | only v => v + 1 > v} @-}

{-@ bad :: x:Int -> {v:Int | v = OnlyA} @-}
bad :: Int -> Int
bad x = x
