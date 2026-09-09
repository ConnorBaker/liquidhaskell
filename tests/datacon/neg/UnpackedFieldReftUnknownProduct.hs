{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no datatype in the logic" @-}
-- A refinement WRITTEN on an {-# UNPACK #-}ed field whose type is a
-- two-field PRODUCT the logic has no datatype for. @Complex Double@ is
-- @!Double :+ !Double@ from @base@, with no LiquidHaskell declaration; the
-- worker takes its two components. Carrying the refinement across means
-- stating it over the rebuilt product, @(:+) a v@, and @:+@ is unknown to the
-- logic -- unlike a single-argument field (@pos/UnpackedFieldReftUnknown.hs@),
-- two components have no reading as "the field" without their constructor.
--
-- So 'RefType.expandProductType' refuses at the constructor, naming the field
-- and the constructor. Decided on the type actually emitted: the same field
-- with a trivial refinement rebuilds nothing and is accepted.
module UnpackedFieldReftUnknownProduct where

import Data.Complex

data B = B {-# UNPACK #-} !(Complex Double) !Int

{-@ data B = B (bZ :: {v:Complex Double | v == v}) (bN :: Int) @-}

{-@ mk :: z:Complex Double -> n:Int -> {v:B | bN v == n} @-}
mk :: Complex Double -> Int -> B
mk = B
