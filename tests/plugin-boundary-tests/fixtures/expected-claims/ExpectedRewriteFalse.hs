{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ExpectedRewriteFalse (f) where

{-@ f :: xs:[()] -> {v:Integer | len xs == 0} @-}
f :: [()] -> Integer
f _ = 0

{-@ fail privateProof @-}
{-@ rewrite privateProof @-}
{-@ privateProof :: xs:[()] -> {v:() | len xs == 0} @-}
privateProof :: [()] -> ()
privateProof _ = ()
