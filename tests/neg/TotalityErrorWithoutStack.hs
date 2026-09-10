{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityErrorWithoutStack (value) where
import GHC.Err (errorWithoutStackTrace)
value :: Int
value = errorWithoutStackTrace "reachable pure bottom"
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
