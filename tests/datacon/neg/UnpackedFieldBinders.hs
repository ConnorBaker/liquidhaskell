{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldBinders.hs@: an
-- unpacked strict field is still CHECKED, not merely well-sorted.
--
-- @--expect-error-containing@ rather than @--expect-any-error@, and that is the
-- whole point of the module. Before the fix this file also failed -- with
-- @Illegal type specification@, raised on the data declaration -- so
-- @--expect-any-error@ was discharged by the very defect the pos module exists
-- to catch, and the test passed while proving nothing. Naming the error keeps
-- it honest: only a real refutation of the false @n + 1@ claim satisfies it.
module UnpackedFieldBinders where

data Extent = Extent Int Int Int

data Section = Section
  { sectionOrdinal :: !Int
  , sectionExtent :: Extent
  }

{-@ measure sectionOrdinal @-}

-- FALSE: 'mkSection' stores @n@, not @n + 1@.
{-@ mkSection :: n:Int -> {v:Section | sectionOrdinal v == n + 1} @-}
mkSection :: Int -> Section
mkSection n = Section n (Extent 0 0 0)
