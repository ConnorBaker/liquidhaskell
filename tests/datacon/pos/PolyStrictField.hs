{-# OPTIONS_GHC -O1 #-}

-- | Control: a POLYMORPHIC strict field @!a@ beside an unboxed @!Int@.
--
-- GHC cannot unbox a field whose representation it does not know, so the
-- bang on @tA@ is @HsStrict@ and only @tN@ is @HsUnpack@: exactly one field
-- expands, and 'Bare.resortedFields' compares a type-variable field against
-- itself. No module under @tests/datacon@ had a type variable in a strict
-- field before this one.
--
-- A red here would mean a type-variable field is mishandled by the expansion
-- or by the sort comparison.
module PolyStrictField where

data T a = T { tA :: !a, tN :: !Int }

{-@ measure tA @-}
{-@ measure tN @-}

{-@ mk :: x:a -> n:Int -> {v:T a | tA v == x && tN v == n} @-}
mk :: a -> Int -> T a
mk x n = T x n
