{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Int_LHAssumptions where

import GHC.Classes_LHAssumptions ()
import GHC.Int
import GHC.Num_LHAssumptions ()
import GHC.Real_LHAssumptions ()

{-@
embed Int8  as int
embed Int16 as int
embed Int32 as int
embed Int64 as int
invariant {v:Int8 | -128 <= v && v < 128}
invariant {v:Int16 | -32768 <= v && v < 32768}
invariant {v:Int32 | -2147483648 <= v && v < 2147483648}
invariant {v:Int64 | -9223372036854775808 <= v && v < 9223372036854775808}

type Nat64 = {v:Int64 | v >= 0}
@-}

-- These complete arrows describe GHC.Internal.Int's actual fixed-width
-- dictionaries: modular arithmetic, exact widening, and guarded division.
-- They do not grant arithmetic laws to an unknown class dictionary.
{-@
instance Num Int8 where
    assume (+) :: x:Int8 -> y:Int8 -> {v:Int8 | SignedWrap 128 (x + y) v}
    assume (-) :: x:Int8 -> y:Int8 -> {v:Int8 | SignedWrap 128 (x - y) v}
    assume (*) :: x:Int8 -> y:Int8 -> {v:Int8 | SignedWrap 128 (x * y) v}
    assume negate :: x:Int8 -> {v:Int8 | SignedWrap 128 (-x) v}
    assume abs :: x:Int8 -> {v:Int8 | SignedWrap 128 (if x >= 0 then x else -x) v}
    assume signum :: x:Int8 -> {v:Int8 | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Int8 | SignedWrap 128 x v}

instance Integral Int8 where
    assume quot :: x:Int8 -> y:{Int8 | SignedQuotientDomain 128 x y} -> {v:Int8 | IntegralQuotient x y v}
    assume rem :: x:Int8 -> y:{Int8 | y /= 0} -> {v:Int8 | IntegralRemainder x y v}
    assume div :: x:Int8 -> y:{Int8 | SignedQuotientDomain 128 x y} -> {v:Int8 | IntegralDiv x y v}
    assume mod :: x:Int8 -> y:{Int8 | y /= 0} -> {v:Int8 | IntegralMod x y v}
    assume quotRem :: x:Int8 -> y:{Int8 | SignedQuotientDomain 128 x y} -> ({v:Int8 | IntegralQuotient x y v}, {v:Int8 | IntegralRemainder x y v})
    assume divMod :: x:Int8 -> y:{Int8 | SignedQuotientDomain 128 x y} -> ({v:Int8 | IntegralDiv x y v}, {v:Int8 | IntegralMod x y v})
    assume toInteger :: x:Int8 -> {v:Integer | v = x}

instance Num Int16 where
    assume (+) :: x:Int16 -> y:Int16 -> {v:Int16 | SignedWrap 32768 (x + y) v}
    assume (-) :: x:Int16 -> y:Int16 -> {v:Int16 | SignedWrap 32768 (x - y) v}
    assume (*) :: x:Int16 -> y:Int16 -> {v:Int16 | SignedWrap 32768 (x * y) v}
    assume negate :: x:Int16 -> {v:Int16 | SignedWrap 32768 (-x) v}
    assume abs :: x:Int16 -> {v:Int16 | SignedWrap 32768 (if x >= 0 then x else -x) v}
    assume signum :: x:Int16 -> {v:Int16 | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Int16 | SignedWrap 32768 x v}

instance Integral Int16 where
    assume quot :: x:Int16 -> y:{Int16 | SignedQuotientDomain 32768 x y} -> {v:Int16 | IntegralQuotient x y v}
    assume rem :: x:Int16 -> y:{Int16 | y /= 0} -> {v:Int16 | IntegralRemainder x y v}
    assume div :: x:Int16 -> y:{Int16 | SignedQuotientDomain 32768 x y} -> {v:Int16 | IntegralDiv x y v}
    assume mod :: x:Int16 -> y:{Int16 | y /= 0} -> {v:Int16 | IntegralMod x y v}
    assume quotRem :: x:Int16 -> y:{Int16 | SignedQuotientDomain 32768 x y} -> ({v:Int16 | IntegralQuotient x y v}, {v:Int16 | IntegralRemainder x y v})
    assume divMod :: x:Int16 -> y:{Int16 | SignedQuotientDomain 32768 x y} -> ({v:Int16 | IntegralDiv x y v}, {v:Int16 | IntegralMod x y v})
    assume toInteger :: x:Int16 -> {v:Integer | v = x}

instance Num Int32 where
    assume (+) :: x:Int32 -> y:Int32 -> {v:Int32 | SignedWrap 2147483648 (x + y) v}
    assume (-) :: x:Int32 -> y:Int32 -> {v:Int32 | SignedWrap 2147483648 (x - y) v}
    assume (*) :: x:Int32 -> y:Int32 -> {v:Int32 | SignedWrap 2147483648 (x * y) v}
    assume negate :: x:Int32 -> {v:Int32 | SignedWrap 2147483648 (-x) v}
    assume abs :: x:Int32 -> {v:Int32 | SignedWrap 2147483648 (if x >= 0 then x else -x) v}
    assume signum :: x:Int32 -> {v:Int32 | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Int32 | SignedWrap 2147483648 x v}

instance Integral Int32 where
    assume quot :: x:Int32 -> y:{Int32 | SignedQuotientDomain 2147483648 x y} -> {v:Int32 | IntegralQuotient x y v}
    assume rem :: x:Int32 -> y:{Int32 | y /= 0} -> {v:Int32 | IntegralRemainder x y v}
    assume div :: x:Int32 -> y:{Int32 | SignedQuotientDomain 2147483648 x y} -> {v:Int32 | IntegralDiv x y v}
    assume mod :: x:Int32 -> y:{Int32 | y /= 0} -> {v:Int32 | IntegralMod x y v}
    assume quotRem :: x:Int32 -> y:{Int32 | SignedQuotientDomain 2147483648 x y} -> ({v:Int32 | IntegralQuotient x y v}, {v:Int32 | IntegralRemainder x y v})
    assume divMod :: x:Int32 -> y:{Int32 | SignedQuotientDomain 2147483648 x y} -> ({v:Int32 | IntegralDiv x y v}, {v:Int32 | IntegralMod x y v})
    assume toInteger :: x:Int32 -> {v:Integer | v = x}

instance Num Int64 where
    assume (+) :: x:Int64 -> y:Int64 -> {v:Int64 | SignedWrap 9223372036854775808 (x + y) v}
    assume (-) :: x:Int64 -> y:Int64 -> {v:Int64 | SignedWrap 9223372036854775808 (x - y) v}
    assume (*) :: x:Int64 -> y:Int64 -> {v:Int64 | SignedWrap 9223372036854775808 (x * y) v}
    assume negate :: x:Int64 -> {v:Int64 | SignedWrap 9223372036854775808 (-x) v}
    assume abs :: x:Int64 -> {v:Int64 | SignedWrap 9223372036854775808 (if x >= 0 then x else -x) v}
    assume signum :: x:Int64 -> {v:Int64 | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Int64 | SignedWrap 9223372036854775808 x v}

instance Integral Int64 where
    assume quot :: x:Int64 -> y:{Int64 | SignedQuotientDomain 9223372036854775808 x y} -> {v:Int64 | IntegralQuotient x y v}
    assume rem :: x:Int64 -> y:{Int64 | y /= 0} -> {v:Int64 | IntegralRemainder x y v}
    assume div :: x:Int64 -> y:{Int64 | SignedQuotientDomain 9223372036854775808 x y} -> {v:Int64 | IntegralDiv x y v}
    assume mod :: x:Int64 -> y:{Int64 | y /= 0} -> {v:Int64 | IntegralMod x y v}
    assume quotRem :: x:Int64 -> y:{Int64 | SignedQuotientDomain 9223372036854775808 x y} -> ({v:Int64 | IntegralQuotient x y v}, {v:Int64 | IntegralRemainder x y v})
    assume divMod :: x:Int64 -> y:{Int64 | SignedQuotientDomain 9223372036854775808 x y} -> ({v:Int64 | IntegralDiv x y v}, {v:Int64 | IntegralMod x y v})
    assume toInteger :: x:Int64 -> {v:Integer | v = x}
@-}

-- Each concrete dictionary in GHC.Internal.Int uses the matching
-- signed/unsigned comparison primops. The existing embedding interprets each
-- value as its mathematical magnitude; comparison introduces no wrap step.
-- These are trusted source correspondences, not laws of arbitrary Eq/Ord.
{-@

instance Eq Int8 where
    assume (==) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x != y}

instance Ord Int8 where
    assume (>) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Int8 -> y:Int8 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Int8 -> y:Int8 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Int8 -> y:Int8 -> {v:Int8 | v = (if x <= y then y else x)}
    assume min :: x:Int8 -> y:Int8 -> {v:Int8 | v = (if x <= y then x else y)}

instance Eq Int16 where
    assume (==) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x != y}

instance Ord Int16 where
    assume (>) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Int16 -> y:Int16 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Int16 -> y:Int16 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Int16 -> y:Int16 -> {v:Int16 | v = (if x <= y then y else x)}
    assume min :: x:Int16 -> y:Int16 -> {v:Int16 | v = (if x <= y then x else y)}

instance Eq Int32 where
    assume (==) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x != y}

instance Ord Int32 where
    assume (>) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Int32 -> y:Int32 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Int32 -> y:Int32 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Int32 -> y:Int32 -> {v:Int32 | v = (if x <= y then y else x)}
    assume min :: x:Int32 -> y:Int32 -> {v:Int32 | v = (if x <= y then x else y)}

instance Eq Int64 where
    assume (==) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x != y}

instance Ord Int64 where
    assume (>) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Int64 -> y:Int64 -> {v:Bool | v <=> x <= y}
    assume compare :: x:Int64 -> y:Int64 -> {v:Ordering | NumericOrdering x y v}
    assume max :: x:Int64 -> y:Int64 -> {v:Int64 | v = (if x <= y then y else x)}
    assume min :: x:Int64 -> y:Int64 -> {v:Int64 | v = (if x <= y then x else y)}
@-}
