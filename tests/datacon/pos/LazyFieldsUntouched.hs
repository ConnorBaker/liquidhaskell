{-# OPTIONS_GHC -O1 #-}

-- | Control: NO strict field, so nothing is unboxed at any optimisation level
-- and the worker's type equals the spec's.
--
-- 'RefType.expandProductType' must short-circuit on its @isTrivial'@ guard,
-- and 'unpackedFields' must answer 'False' for an @HsLazy@ bang. This is
-- @UnpackedFieldBinders.hs@ with the bang removed from @tN@: the same
-- expandable second field, the same claim, and no seam.
--
-- A red here would mean the seam machinery fires on a constructor GHC left
-- entirely alone.
module LazyFieldsUntouched where

data Extent = Extent Int Int Int

data T = T { tN :: Int, tE :: Extent }

{-@ measure tN @-}

{-@ mk :: n:Int -> {v:T | tN v == n} @-}
mk :: Int -> T
mk n = T n (Extent 0 0 0)
