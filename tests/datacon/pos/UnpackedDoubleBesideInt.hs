{-# OPTIONS_GHC -O1 #-}

-- | Control: two unpacked fields with DIFFERENT non-trivial embedded sorts.
-- @!Double@ becomes @Double#@, which embeds to @real@; @!Int@ becomes @Int#@,
-- which embeds to @int@.
--
-- 19414eea's "two components, distinct binders" fix -- 'mkProductTy''s
-- single-component branch keeping each field's own binder -- was pinned by
-- @UnpackedFieldBinders.hs@ with two @int@-sorted fields, where a binder
-- collision is silent (a field equality nobody wrote). Here a collision would
-- be LOUD, @Cannot unify real with int@, and this is the first module in the
-- suite with a @Double@ field at all.
--
-- A red here would mean @Double#@ is not carried through the expansion the way
-- @Int#@ is.
module UnpackedDoubleBesideInt where

data T = T { tD :: !Double, tN :: !Int }

{-@ measure tD @-}
{-@ measure tN @-}

{-@ mk :: d:Double -> n:Int -> {v:T | tD v == d && tN v == n} @-}
mk :: Double -> Int -> T
mk d n = T d n
