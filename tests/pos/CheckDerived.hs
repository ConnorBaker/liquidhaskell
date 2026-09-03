-- | @--check-derived@ makes LiquidHaskell check the bodies GHC generates for a
-- @deriving@ clause, which are trusted without it.
--
-- Nothing in this module is written by hand, so every constraint it raises
-- comes from a derived binder: it is SAFE at 65 constraints with the flag and
-- SAFE at 0 without it, which attributes all 65 to the flag.
--
-- It is an attribution and not a guard. A build in which the flag parses but
-- does nothing leaves this module SAFE at 0 and this test still PASSES; it is
-- neg/CheckDerived.hs that fails in that case. Measured both ways.
{-@ LIQUID "--check-derived" @-}
module CheckDerived where

data Nat' = Zero | Succ Nat'
  deriving (Eq, Ord, Show, Read)
