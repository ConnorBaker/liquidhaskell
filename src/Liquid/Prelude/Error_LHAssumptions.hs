{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Error_LHAssumptions where

import GHC.Err (error)

-- A single owner shared by Prelude and the import-independent totality policy.
-- Keeping Prelude's dependency preserves its existing no-totality behavior.
{-@ assume error :: {v:_ | false} -> a @-}
