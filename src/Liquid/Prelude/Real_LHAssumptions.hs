{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Liquid.Prelude.Real_LHAssumptions where

-- Prelude imports this module automatically. A generic Num multiplication
-- equation would override the actual supplied dictionary's meaning.
-- Concrete Integer and machine Int/Word contracts belong to their resolved
-- instances in GHC.Num_LHAssumptions; IEEE operations have opaque results.
