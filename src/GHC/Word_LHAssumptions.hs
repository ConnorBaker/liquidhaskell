{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Word_LHAssumptions where

import GHC.Classes_LHAssumptions ()
import GHC.Num_LHAssumptions ()
import GHC.Real_LHAssumptions ()
import GHC.Word

{-@
embed Word   as int
embed Word8  as int
embed Word16 as int
embed Word32 as int
embed Word64 as int

invariant {v:Word8 | 0 <= v && v < 256}
invariant {v:Word16 | 0 <= v && v < 65536}
invariant {v:Word32 | 0 <= v && v < 4294967296}
invariant {v:Word64 | 0 <= v && v < 18446744073709551616}
@-}

-- These complete arrows describe GHC.Internal.Word's actual fixed-width
-- dictionaries: modular arithmetic, exact widening, and guarded division.
-- They do not grant arithmetic laws to an unknown class dictionary.
{-@
instance Num Word8 where
    assume (+) :: x:Word8 -> y:Word8 -> {v:Word8 | UnsignedWrap 256 (x + y) v}
    assume (-) :: x:Word8 -> y:Word8 -> {v:Word8 | UnsignedWrap 256 (x - y) v}
    assume (*) :: x:Word8 -> y:Word8 -> {v:Word8 | UnsignedWrap 256 (x * y) v}
    assume negate :: x:Word8 -> {v:Word8 | UnsignedWrap 256 (-x) v}
    assume abs :: x:Word8 -> {v:Word8 | v = x}
    assume signum :: x:Word8 -> {v:Word8 | v = (if x = 0 then 0 else 1)}
    assume fromInteger :: x:Integer -> {v:Word8 | UnsignedWrap 256 x v}

instance Integral Word8 where
    assume quot :: x:Word8 -> y:{Word8 | y /= 0} -> {v:Word8 | v = x / y}
    assume rem :: x:Word8 -> y:{Word8 | y /= 0} -> {v:Word8 | v = x mod y}
    assume div :: x:Word8 -> y:{Word8 | y /= 0} -> {v:Word8 | v = x / y}
    assume mod :: x:Word8 -> y:{Word8 | y /= 0} -> {v:Word8 | v = x mod y}
    assume quotRem :: x:Word8 -> y:{Word8 | y /= 0} -> ({v:Word8 | v = x / y}, {v:Word8 | v = x mod y})
    assume divMod :: x:Word8 -> y:{Word8 | y /= 0} -> ({v:Word8 | v = x / y}, {v:Word8 | v = x mod y})
    assume toInteger :: x:Word8 -> {v:Integer | v = x}

instance Num Word16 where
    assume (+) :: x:Word16 -> y:Word16 -> {v:Word16 | UnsignedWrap 65536 (x + y) v}
    assume (-) :: x:Word16 -> y:Word16 -> {v:Word16 | UnsignedWrap 65536 (x - y) v}
    assume (*) :: x:Word16 -> y:Word16 -> {v:Word16 | UnsignedWrap 65536 (x * y) v}
    assume negate :: x:Word16 -> {v:Word16 | UnsignedWrap 65536 (-x) v}
    assume abs :: x:Word16 -> {v:Word16 | v = x}
    assume signum :: x:Word16 -> {v:Word16 | v = (if x = 0 then 0 else 1)}
    assume fromInteger :: x:Integer -> {v:Word16 | UnsignedWrap 65536 x v}

instance Integral Word16 where
    assume quot :: x:Word16 -> y:{Word16 | y /= 0} -> {v:Word16 | v = x / y}
    assume rem :: x:Word16 -> y:{Word16 | y /= 0} -> {v:Word16 | v = x mod y}
    assume div :: x:Word16 -> y:{Word16 | y /= 0} -> {v:Word16 | v = x / y}
    assume mod :: x:Word16 -> y:{Word16 | y /= 0} -> {v:Word16 | v = x mod y}
    assume quotRem :: x:Word16 -> y:{Word16 | y /= 0} -> ({v:Word16 | v = x / y}, {v:Word16 | v = x mod y})
    assume divMod :: x:Word16 -> y:{Word16 | y /= 0} -> ({v:Word16 | v = x / y}, {v:Word16 | v = x mod y})
    assume toInteger :: x:Word16 -> {v:Integer | v = x}

instance Num Word32 where
    assume (+) :: x:Word32 -> y:Word32 -> {v:Word32 | UnsignedWrap 4294967296 (x + y) v}
    assume (-) :: x:Word32 -> y:Word32 -> {v:Word32 | UnsignedWrap 4294967296 (x - y) v}
    assume (*) :: x:Word32 -> y:Word32 -> {v:Word32 | UnsignedWrap 4294967296 (x * y) v}
    assume negate :: x:Word32 -> {v:Word32 | UnsignedWrap 4294967296 (-x) v}
    assume abs :: x:Word32 -> {v:Word32 | v = x}
    assume signum :: x:Word32 -> {v:Word32 | v = (if x = 0 then 0 else 1)}
    assume fromInteger :: x:Integer -> {v:Word32 | UnsignedWrap 4294967296 x v}

instance Integral Word32 where
    assume quot :: x:Word32 -> y:{Word32 | y /= 0} -> {v:Word32 | v = x / y}
    assume rem :: x:Word32 -> y:{Word32 | y /= 0} -> {v:Word32 | v = x mod y}
    assume div :: x:Word32 -> y:{Word32 | y /= 0} -> {v:Word32 | v = x / y}
    assume mod :: x:Word32 -> y:{Word32 | y /= 0} -> {v:Word32 | v = x mod y}
    assume quotRem :: x:Word32 -> y:{Word32 | y /= 0} -> ({v:Word32 | v = x / y}, {v:Word32 | v = x mod y})
    assume divMod :: x:Word32 -> y:{Word32 | y /= 0} -> ({v:Word32 | v = x / y}, {v:Word32 | v = x mod y})
    assume toInteger :: x:Word32 -> {v:Integer | v = x}

instance Num Word64 where
    assume (+) :: x:Word64 -> y:Word64 -> {v:Word64 | UnsignedWrap 18446744073709551616 (x + y) v}
    assume (-) :: x:Word64 -> y:Word64 -> {v:Word64 | UnsignedWrap 18446744073709551616 (x - y) v}
    assume (*) :: x:Word64 -> y:Word64 -> {v:Word64 | UnsignedWrap 18446744073709551616 (x * y) v}
    assume negate :: x:Word64 -> {v:Word64 | UnsignedWrap 18446744073709551616 (-x) v}
    assume abs :: x:Word64 -> {v:Word64 | v = x}
    assume signum :: x:Word64 -> {v:Word64 | v = (if x = 0 then 0 else 1)}
    assume fromInteger :: x:Integer -> {v:Word64 | UnsignedWrap 18446744073709551616 x v}

instance Integral Word64 where
    assume quot :: x:Word64 -> y:{Word64 | y /= 0} -> {v:Word64 | v = x / y}
    assume rem :: x:Word64 -> y:{Word64 | y /= 0} -> {v:Word64 | v = x mod y}
    assume div :: x:Word64 -> y:{Word64 | y /= 0} -> {v:Word64 | v = x / y}
    assume mod :: x:Word64 -> y:{Word64 | y /= 0} -> {v:Word64 | v = x mod y}
    assume quotRem :: x:Word64 -> y:{Word64 | y /= 0} -> ({v:Word64 | v = x / y}, {v:Word64 | v = x mod y})
    assume divMod :: x:Word64 -> y:{Word64 | y /= 0} -> ({v:Word64 | v = x / y}, {v:Word64 | v = x mod y})
    assume toInteger :: x:Word64 -> {v:Integer | v = x}
@-}

-- Each concrete dictionary in GHC.Internal.Word uses the matching
-- signed/unsigned comparison primops. The existing embedding interprets each
-- value as its mathematical magnitude; comparison introduces no wrap step.
-- These are trusted source correspondences, not laws of arbitrary Eq/Ord.
{-@

instance Eq Word8 where
    assume (==) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x != y}

instance Ord Word8 where
    assume (>) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Word8 -> y:Word8 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Word8 -> y:Word8 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Word8 -> y:Word8 -> {v:Word8 | v = (if x <= y then y else x)}
    assume min :: x:Word8 -> y:Word8 -> {v:Word8 | v = (if x <= y then x else y)}

instance Eq Word16 where
    assume (==) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x != y}

instance Ord Word16 where
    assume (>) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Word16 -> y:Word16 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Word16 -> y:Word16 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Word16 -> y:Word16 -> {v:Word16 | v = (if x <= y then y else x)}
    assume min :: x:Word16 -> y:Word16 -> {v:Word16 | v = (if x <= y then x else y)}

instance Eq Word32 where
    assume (==) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x != y}

instance Ord Word32 where
    assume (>) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Word32 -> y:Word32 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Word32 -> y:Word32 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Word32 -> y:Word32 -> {v:Word32 | v = (if x <= y then y else x)}
    assume min :: x:Word32 -> y:Word32 -> {v:Word32 | v = (if x <= y then x else y)}

instance Eq Word64 where
    assume (==) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x != y}

instance Ord Word64 where
    assume (>) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Word64 -> y:Word64 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Word64 -> y:Word64 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Word64 -> y:Word64 -> {v:Word64 | v = (if x <= y then y else x)}
    assume min :: x:Word64 -> y:Word64 -> {v:Word64 | v = (if x <= y then x else y)}
@-}
