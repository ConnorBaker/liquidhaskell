{-# OPTIONS_GHC -O1 #-}
-- A strict field of a NULLARY single-constructor type.
-- -funbox-small-strict-fields unpacks it to ZERO worker arguments, so
-- @D !U !Int@ has two source fields and a one-argument worker, and no
-- projection of the surviving field is anything but a variable.
--
-- Two decisions used to be made beside the RepMap's own 'rmChanged' and
-- both were wrong here: 'unpackedFieldSubst' also asked "is some projection
-- more than a variable" and answered no, leaving the measure equation
-- Core-shaped -- @Requires 2 fields but given 1@ at 'dN' -- and
-- 'knownDataCon' was keyed on a constructor's FIRST field, which @U@ has not
-- got, so @U@ was "unknown" to the logic that declares it. Both now come from
-- one place. SAFE (2) at -O0 before and after; at -O1 only after.
module NullaryUnpack where

data U = U
data D = D !U !Int

{-@ measure dN @-}
dN :: D -> Int
dN (D _ n) = n

{-@ mk :: n:Int -> {v:D | dN v == n} @-}
mk :: Int -> D
mk n = D U n

{-@ useD :: d:D -> {v:Int | v == dN d} @-}
useD :: D -> Int
useD (D _ n) = n
