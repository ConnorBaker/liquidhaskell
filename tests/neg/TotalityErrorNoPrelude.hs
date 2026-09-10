{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityErrorNoPrelude (value) where
import GHC.Err (error)
import GHC.Types (Bool(False), Int)
value :: Int
value = error "reachable pure bottom"
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
