{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The wrapper's selector equations are an EQUALITY, not a licence.
--
-- @tests/datacon/pos/UnpackedFieldUpdate.hs@ is the attribution for the fix:
-- it is @UNSAFE@ before and @SAFE@ after, at an identical constraint count,
-- with @-O0@ a free control. This module is the guard in the other direction
-- -- it claims the update leaves 'sFlag' TRUE while writing 'False', and must
-- stay @UNSAFE@ afterwards.
--
-- It is deliberately NOT the attribution, and saying so is the point: before
-- the fix this module also failed, because nothing about the wrapper was
-- provable either way. Read a red arm here as "the equation did not become a
-- free pass", never as evidence the fix took effect.
module UnpackedFieldUpdate where

{-@ data S = S
      { sUnpacked :: Int
      , sFlag :: Bool
      } @-}
data S = S
  { sUnpacked :: !Int
  , sFlag :: !Bool
  }

{-@ keepFlag :: s:S -> {v : S | sFlag v} @-}
keepFlag :: S -> S
keepFlag s = s {sFlag = False}
