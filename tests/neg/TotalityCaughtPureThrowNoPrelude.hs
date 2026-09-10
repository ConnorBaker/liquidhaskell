{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityCaughtPureThrowNoPrelude (action) where

import Control.Exception (SomeException, evaluate, throw, try)
import Data.Either (Either)
import GHC.Types (IO, Int)
import System.IO.Error (userError)

action :: IO (Either SomeException Int)
action = try (evaluate (throw (userError "intentional")))
