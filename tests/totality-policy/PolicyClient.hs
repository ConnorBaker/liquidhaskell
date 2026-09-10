{-# LANGUAGE NoImplicitPrelude #-}
module PolicyClient (value) where
import Control.Exception (throw)
import GHC.Types (Bool(False), Int)
import System.IO.Error (userError)
value :: Int
value = throw (userError "reachable pure bottom")
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
