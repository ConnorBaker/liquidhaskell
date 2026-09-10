{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityUndefinedNoPrelude (value) where
import GHC.Internal.Err (undefined)
import GHC.Types (Bool(False), Int)
value :: Int
value = undefined
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
