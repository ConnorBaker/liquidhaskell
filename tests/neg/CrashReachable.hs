{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module CrashReachable where

import Language.Haskell.Liquid.Prelude (crash)

-- crash diverges on every argument: a reachable call is an error even when
-- its argument is True.
boom :: Int
boom = crash True
