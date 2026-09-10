{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityErrorFacade (value) where
import GHC.Types (Bool(False), Int)
import TotalityExceptionFacade (error)
value :: Int
value = error "reachable pure bottom"
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
