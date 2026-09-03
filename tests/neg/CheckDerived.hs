-- | The body GHC generates for @deriving Read@ builds a @Pos@ out of whatever
-- integer it parsed, so it cannot establish the field's refinement.
--
-- Without @--check-derived@ that body is trusted and this module is SAFE at 0
-- constraints -- so this file is a test of the flag, not only of the
-- refinement. With the flag it is UNSAFE at 51.
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--expect-any-error" @-}
module CheckDerived where

{-@ data Pos = Pos { posVal :: { v : Int | 0 < v } } @-}
data Pos = Pos { posVal :: Int }
  deriving (Read)
