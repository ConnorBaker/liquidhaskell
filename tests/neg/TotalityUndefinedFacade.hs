{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityUndefinedFacade (value) where
import GHC.Types (Bool(False), Int)
import TotalityExceptionFacade (undefined)
value :: Int
value = undefined
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
