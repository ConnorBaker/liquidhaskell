{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityThrowBaseNoPrelude (value) where

import Control.Exception.Base (throw)
import GHC.Types (Int)
import System.IO.Error (userError)

value :: Int
value = throw (userError "intentional")
