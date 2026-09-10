{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityCaughtUndefined (action) where
import Control.Exception (SomeException, evaluate, try)
import Data.Either (Either)
import GHC.Err (undefined)
import GHC.Types (Bool(False), IO, Int)
action :: IO (Either SomeException Int)
action = try (evaluate undefined)
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
