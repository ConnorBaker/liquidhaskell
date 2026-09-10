{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Liquid.Prelude.Totality_LHAssumptions where

import Control.Exception.Base
import GHC.Prim
-- This policy is also loaded without Prelude. Its primitive argument types
-- (notably Addr# in call stacks and pattern failures) need their own embeddings.
import GHC.Types_LHAssumptions ()
-- Strict checking of generated Semigroup defaults needs their admitted domain,
-- including in clients that do not import Prelude.
import GHC.Base_LHAssumptions ()
import GHC.Err (errorWithoutStackTrace)
import Liquid.Prelude.Error_LHAssumptions ()

{-@
measure totalityError :: a -> Bool

// A pure exception cannot inhabit an arbitrary refinement. In particular,
// evaluate/catch does not make its suspended argument a total pure value.
assume throw :: Exception e => {v:e | false} -> a

assume errorWithoutStackTrace :: {v:_ | false} -> a

assume patError :: {v:Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume recSelError :: {v:Addr# | totalityError "Use of partial record field selector"} -> a

assume nonExhaustiveGuardsError :: {v:Addr# | totalityError "Guards are non-exhaustive"} -> a

assume noMethodBindingError :: {v:Addr# | totalityError "Missing method(s) on instance declaration"} -> a

assume recConError :: {v:Addr# | totalityError "Missing field in record construction"} -> a
@-}
