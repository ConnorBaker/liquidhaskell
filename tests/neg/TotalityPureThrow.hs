{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityPureThrow (observed) where

import Control.Exception (throw)

-- Keep the partial binding private so this exercises inferred refinements.
partial :: Int
partial = throw (userError "intentional")

observed :: Int
observed = partial
