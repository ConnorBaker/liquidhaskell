{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Base_LHAssumptions (module GHC.Base_LHAssumptions, Semigroup (..)) where

import GHC.Base (NonEmpty, Semigroup (..), assert)
import GHC.CString_LHAssumptions()
import GHC.Exts_LHAssumptions()
import GHC.Types_LHAssumptions()
import Data.Tuple_LHAssumptions()

{-@ LIQUID "--higherorder" @-}
{-@ reflect comp @-}
{-@ assume reflect . as comp @-}
comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)


{-@

// Only the stimes domain is narrowed here; append and sconcat retain their
// existing plain interface requirements. This is not an audit or a proof of
// arbitrary imported Semigroup implementations.
//
// GHC 9.14.1's default stimes (GHC.Internal.Base:635-647) uses the supplied
// comparison, remainder and quotient fields. A positive-looking multiplier
// alone proves neither that division by two is admitted nor that it decreases.
// No nonempty common domain follows from the current Integral requirements.
// Stronger explicit instance arrows remain subject to ordinary body checking.
// This conservative boundary does not establish useful native default calls.
class Semigroup a where
  (<>) :: a -> a -> a
  sconcat :: NonEmpty a -> a
  stimes :: forall b. Integral b => {n:b | false} -> a -> a

assume . :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>.
                   {xcmp::a, wcmp::b<q xcmp> |- c<p wcmp> <: c<r xcmp>}
                   (ycmp:b -> c<p ycmp>)
                -> (zcmp:a -> b<q zcmp>)
                ->  xcmp:a -> c<r xcmp>

measure autolen :: forall a. a -> Int

//  Useless as compiled into GHC primitive, which is ignored
assume assert :: {v:Bool | v } -> a -> a

instance measure len :: forall a. [a] -> Int
  len []     = 0
  len (y:ys) = 1 + len ys

invariant {v: [a] | len v >= 0 }
assume map       :: (a -> b) -> xs:[a] -> {v: [b] | len v == len xs}
assume ++        :: xs:[a] -> ys:[a] -> {v:[a] | len v == len xs + len ys}

assume $         :: (a -> b) -> a -> b
define $             f          x = (f x)

assume id        :: x:a -> {v:a | v = x}

qualif IsEmp(v:Bool, xs: [a])  { v <=> (len xs > 0) }
qualif IsEmp(v:Bool, xs: [a])  { v <=> (len xs = 0) }

qualif ListZ(v: [a])           { len v =  0 }
qualif ListZ(v: [a])           { len v >= 0 }
qualif ListZ(v: [a])           { len v >  0 }

qualif CmpLen(v:[a], xs:[b])   { len v  =  len xs  }
qualif CmpLen(v:[a], xs:[b])   { len v  >= len xs  }
qualif CmpLen(v:[a], xs:[b])   { len v  >  len xs  }
qualif CmpLen(v:[a], xs:[b])   { len v  <= len xs  }
qualif CmpLen(v:[a], xs:[b])   { len v  <  len xs  }

qualif EqLen(v:int, xs: [a])   { v = len xs  }
qualif LenEq(v:[a], x: int)    { x = len v  }

qualif LenDiff(v:[a], x:int)   { len v  = x + 1 }
qualif LenDiff(v:[a], x:int)   { len v  = x - 1 }
qualif LenAcc(v:int, xs:[a], n: int) { v = len xs  + n }

@-}
