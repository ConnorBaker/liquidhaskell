{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Client (claim) where
import Producer (f)

{-@ claim :: {v:Integer | v == 1} @-}
claim :: Integer
claim = f 0
