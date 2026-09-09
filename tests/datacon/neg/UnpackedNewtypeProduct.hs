{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/UnpackedNewtypeProduct.hs@:
-- the same @{-# UNPACK #-}@ed newtype-over-product field, with the measure
-- reading the FIRST component and the claim naming the SECOND. A rebuild
-- that lost track of which leaf is which would be well sorted and would
-- discharge this; it must not.
module UnpackedNewtypeProduct where

data P2 = P2 !Int !Int

newtype NP = NP P2

data D = D {-# UNPACK #-} !NP

{-@ measure dFst @-}
dFst :: D -> Int
dFst (D (NP (P2 a _))) = a

{-@ mk :: a:Int -> b:Int -> {v:D | dFst v == b} @-}
mk :: Int -> Int -> D
mk a b = D (NP (P2 a b))
