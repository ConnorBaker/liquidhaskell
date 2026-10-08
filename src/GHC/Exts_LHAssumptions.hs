{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Exts_LHAssumptions where

#include "MachDeps.h"

import GHC.Base
import GHC.Prim
import GHC.Types_LHAssumptions ()

-- These contracts describe actual machine operations. The definitions give
-- reflection the same target-width interpretation through the ordinary
-- logical map; arithmetic inside refinements remains mathematical.
#if WORD_SIZE_IN_BITS == 32
{-@
assume GHC.Prim.+# :: x:Int# -> y:Int# -> {v:Int# | v = ((x + y + 2147483648) mod 4294967296) - 2147483648}
assume GHC.Prim.-# :: x:Int# -> y:Int# -> {v:Int# | v = ((x - y + 2147483648) mod 4294967296) - 2147483648}
assume GHC.Prim.*# :: x:Int# -> y:Int# -> {v:Int# | v = ((x * y + 2147483648) mod 4294967296) - 2147483648}
assume GHC.Prim.negateInt# :: x:Int# -> {v:Int# | v = ((-x + 2147483648) mod 4294967296) - 2147483648}

define GHC.Prim.+# x y = ((x + y + 2147483648) mod 4294967296) - 2147483648
define GHC.Prim.-# x y = ((x - y + 2147483648) mod 4294967296) - 2147483648
define GHC.Prim.*# x y = ((x * y + 2147483648) mod 4294967296) - 2147483648
define GHC.Prim.negateInt# x = ((-x + 2147483648) mod 4294967296) - 2147483648
@-}
#elif WORD_SIZE_IN_BITS == 64
{-@
assume GHC.Prim.+# :: x:Int# -> y:Int# -> {v:Int# | v = ((x + y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808}
assume GHC.Prim.-# :: x:Int# -> y:Int# -> {v:Int# | v = ((x - y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808}
assume GHC.Prim.*# :: x:Int# -> y:Int# -> {v:Int# | v = ((x * y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808}
assume GHC.Prim.negateInt# :: x:Int# -> {v:Int# | v = ((-x + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808}

define GHC.Prim.+# x y = ((x + y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808
define GHC.Prim.-# x y = ((x - y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808
define GHC.Prim.*# x y = ((x * y + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808
define GHC.Prim.negateInt# x = ((-x + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808
@-}
#else
#error Unsupported GHC target Int width
#endif

{-@
assume GHC.Prim.==# :: x:Int# -> y:Int# -> {v:Int# | v = (if x = y then 1 else 0)}
assume GHC.Prim./=# :: x:Int# -> y:Int# -> {v:Int# | v = (if x /= y then 1 else 0)}
assume GHC.Prim.>=# :: x:Int# -> y:Int# -> {v:Int# | v = (if x >= y then 1 else 0)}
assume GHC.Prim.<=# :: x:Int# -> y:Int# -> {v:Int# | v = (if x <= y then 1 else 0)}
assume GHC.Prim.<# :: x:Int# -> y:Int# -> {v:Int# | v = (if x < y then 1 else 0)}
assume GHC.Prim.># :: x:Int# -> y:Int# -> {v:Int# | v = (if x > y then 1 else 0)}

define GHC.Prim.==# x y = if x = y then 1 else 0
define GHC.Prim./=# x y = if x /= y then 1 else 0
define GHC.Prim.>=# x y = if x >= y then 1 else 0
define GHC.Prim.<=# x y = if x <= y then 1 else 0
define GHC.Prim.<# x y = if x < y then 1 else 0
define GHC.Prim.># x y = if x > y then 1 else 0
@-}
