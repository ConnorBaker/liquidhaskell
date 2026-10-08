{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.Tuple_LHAssumptions where

import Data.Tuple

{-@
assume fst :: {f:(x:(a,b) -> {v:a | v = (fst x)}) | f == fst }
assume snd :: forall a b <p :: a -> b -> Bool>.
  {f:(x:(a,b)<p> -> {v:b<p (fst x)> | v = (snd x)}) | f == snd }

measure fst :: (a, b) -> a
  fst (a, b) = a

measure snd :: (a, b) -> b
  snd (a, b) = b

qualif Fst(__v:a, __y:b) { __v = (fst __y) }
qualif Snd(__v:a, __y:b) { __v = (snd __y) }
@-}
