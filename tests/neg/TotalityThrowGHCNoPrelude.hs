{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityThrowGHCNoPrelude (value) where

import GHC.Exception (throw)
import GHC.Types (Int)
import System.IO.Error (userError)

value :: Int
value = throw (userError "intentional")
