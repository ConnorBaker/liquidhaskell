{-# OPTIONS_GHC -O1 #-}

-- | A field's OWN refinement must survive the field being unpacked.
--
-- @expandProductType@ rewrites a data constructor's spec so its argument types
-- match the WORKER's, which is what LiquidHaskell sees from @-O1@ up once
-- @-funbox-small-strict-fields@ has rewritten a strict field to its
-- representation. @mkProductTy@ did that rewrite with @ofType@ alone, which
-- returns the component's type carrying a TRIVIAL refinement -- so the
-- @{v : Int | v <= flim}@ written on 'F''s second field below was silently
-- dropped, and only from @-O1@ up.
--
-- The failure is quiet in both directions, which is why it needs a test rather
-- than a crash report. The declaration is ACCEPTED; nothing is reported at the
-- data type at all. What happens instead is that every obligation the field's
-- bound would have discharged becomes unprovable at the CONSUMER -- 'useF'
-- here -- so the error names a call site far from the decision, and reads like
-- a missing precondition on the consumer rather than a lost one on the
-- producer.
--
-- @-O1@ is required: at @-O0@ the worker's type still equals the spec's,
-- @expandProductType@ short-circuits on its own @isTrivial@ guard, and this
-- module is SAFE with or without the fix. The @[Int]@ field is not decoration
-- -- it keeps 'F' a MULTI-field constructor, so the expansion is the ordinary
-- per-field one and not a whole-constructor special case.
module UnpackedFieldReft where

{-@ inline flim @-}
flim :: Int
flim = 1024

{-@ data F = F [Int] {v : Int | v <= flim} @-}
data F = F ![Int] !Int

{-@ needBounded :: {v : Int | v <= flim} -> Int @-}
needBounded :: Int -> Int
needBounded x = x

useF :: F -> Int
useF (F _ n) = needBounded n

-- The same bound reached through a constructor APPLICATION, so the worker's
-- own spec is exercised and not only the pattern match.
{-@ mkF :: [Int] -> {v : Int | v <= flim} -> F @-}
mkF :: [Int] -> Int -> F
mkF xs n = F xs n
