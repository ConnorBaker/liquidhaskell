{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--no-totality" @-}

module TotalityDisabledThrowNoPrelude (value) where

import Control.Exception (throw)
import GHC.Types (Int)
import System.IO.Error (userError)

-- The import-independent loader must preserve the existing policy switch.
value :: Int
value = throw (userError "intentional")
