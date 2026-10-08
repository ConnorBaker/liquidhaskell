{-# LANGUAGE CPP #-}

module TextAppendOverflowBad where

#include "MachDeps.h"

import Data.Text (Text)
import Data.Text qualified as Text

#if WORD_SIZE_IN_BITS == 32
{-@ expression TestMaxInt = 2147483647 @-}
#elif WORD_SIZE_IN_BITS == 64
{-@ expression TestMaxInt = 9223372036854775807 @-}
#else
#error Unsupported GHC target Int width
#endif

-- Each operand is valid separately; their combined allocation overflows Int.
-- This control is checked symbolically, never evaluated on an unsafe buffer.
{-@ disproved :: {x:Text | tvalid x && tbytes x == TestMaxInt}
              -> {y:Text | tvalid y && tbytes y == 1} -> Text @-}
disproved :: Text -> Text -> Text
disproved = Text.append
