{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ValidClient (claim) where
import Producer (f)

{-@ claim :: {v:Integer | v == 0} @-}
claim :: Integer
claim = f 0
