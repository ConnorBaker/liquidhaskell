{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Liquid.Prelude.Error_LHAssumptions where

import GHC.Err (error)

-- One contract owner shared by Prelude and import-independent totality.
-- Prelude retains this dependency even when totality checking is disabled.
{-@ assume error :: {v:_ | false} -> a @-}
