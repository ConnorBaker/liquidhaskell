{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityThrowDefiningNoPrelude (value) where

import GHC.Internal.Exception (throw)
import GHC.Types (Int)
import System.IO.Error (userError)

value :: Int
value = throw (userError "intentional")
