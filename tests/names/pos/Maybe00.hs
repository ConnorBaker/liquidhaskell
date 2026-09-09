{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The @define@s in `Data.Maybe_LHAssumptions`: `isJust`, `isNothing` and
--   `fromJust` applied INSIDE a reflected body.
--
--   An @assume@ links the Haskell function to the measure only at a program
--   call site. A reflected body is lifted by @CoreToLogic@, where a call to a
--   function carrying no @define@ becomes an application of the HASKELL symbol
--   (@GHC.Internal.Data.Maybe.isJust@), about which the logic knows nothing --
--   every fact in scope is about the MEASURE @isJust@. So without the define
--   @hasSel (R (Just n) False)@ is UNDECIDED under PLE, and each claim below is
--   a Liquid Type Mismatch; with it each unfolds to the measure and is proved.
--
--   One reflected body per function, so an absent define reddens exactly the
--   binder that names it.
module Maybe00 where

import Data.Maybe (fromJust, isJust, isNothing)

{-@ data R = R { sel :: Maybe Int, flag :: Bool } @-}
data R = R { sel :: Maybe Int, flag :: Bool }

{-@ reflect hasSel @-}
hasSel :: R -> Bool
hasSel r = isJust (sel r) || flag r

{-@ reflect lacksSel @-}
lacksSel :: R -> Bool
lacksSel r = isNothing (sel r)

{-@ reflect unwrap @-}
{-@ unwrap :: { m : Maybe Int | isJust m } -> Int @-}
unwrap :: Maybe Int -> Int
unwrap m = fromJust m

-- `isJust` under a literal record whose field is `Just`.
{-@ hasSelJust :: n : Int -> { v : () | hasSel (R (Just n) False) } @-}
hasSelJust :: Int -> ()
hasSelJust _ = ()

-- `isNothing` under a literal record whose field is `Nothing`.
{-@ lacksSelNothing :: { v : () | lacksSel (R Nothing True) } @-}
lacksSelNothing :: ()
lacksSelNothing = ()

-- `fromJust` reads the payload back.
{-@ unwrapJust :: n : Int -> { v : () | unwrap (Just n) == n } @-}
unwrapJust :: Int -> ()
unwrapJust _ = ()
