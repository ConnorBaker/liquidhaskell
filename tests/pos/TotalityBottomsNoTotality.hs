{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--no-totality" @-}
module TotalityBottomsNoTotality (plain, stackless, absent) where
import GHC.Err (error, errorWithoutStackTrace, undefined)
import GHC.Types (Bool(False), Int)

plain, stackless, absent :: Int
plain = error "no totality policy requested"
stackless = errorWithoutStackTrace "no totality policy requested"
absent = undefined

{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
