{-# LANGUAGE NoImplicitPrelude #-}

module TotalityThrowIONoPrelude (action) where

import Control.Exception (SomeException, throwIO, try)
import Data.Either (Either)
import GHC.Types (Bool(False), IO, Int)
import System.IO.Error (userError)

-- IO exception handling remains supported without an implicit Prelude.
action :: IO (Either SomeException Int)
action = try (throwIO (userError "intentional"))

{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
