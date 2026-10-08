{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Totality_LHAssumptions where

import Control.Exception.Base
import GHC.Prim
-- The policy also loads without Prelude; primitive arguments need their own
-- embeddings, including Addr# in generated pattern-match failures.
import GHC.Types_LHAssumptions ()
import GHC.Err (errorWithoutStackTrace)
import Liquid.Prelude.Error_LHAssumptions ()

{-@
measure totalityError :: a -> Bool

// Pure exceptions are not total values. This does not restrict throwIO.
// Inherit the complete GHC context, including its implicit call stack.
assume throw :: {v:e | false} -> a

assume errorWithoutStackTrace :: {v:_ | false} -> a

assume patError :: {v:Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume recSelError :: {v:Addr# | totalityError "Use of partial record field selector"} -> a

assume nonExhaustiveGuardsError :: {v:Addr# | totalityError "Guards are non-exhaustive"} -> a

assume noMethodBindingError :: {v:Addr# | totalityError "Missing method(s) on instance declaration"} -> a

assume recConError :: {v:Addr# | totalityError "Missing field in record construction"} -> a
@-}
