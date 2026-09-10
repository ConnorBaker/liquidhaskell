{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityErrorWithoutStackNoPrelude (value) where
import GHC.Internal.Err (errorWithoutStackTrace)
import GHC.Types (Bool(False), Int)
value :: Int
value = errorWithoutStackTrace "reachable pure bottom"
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
