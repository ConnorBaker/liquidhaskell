{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
-- Companion to @pos/NullaryUnpack.hs@: the same nullary-unpacked constructor,
-- with a claim the measure equation contradicts. Pins that the positive's
-- @SAFE (2)@ is a proof and not a vacuous environment: the equation over the
-- one-argument worker still says what 'dN' reads.
module NullaryUnpack where

data U = U
data D = D !U !Int

{-@ measure dN @-}
dN :: D -> Int
dN (D _ n) = n

{-@ bad :: d:D -> {v:Int | v /= dN d} @-}
bad :: D -> Int
bad (D _ n) = n
