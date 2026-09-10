{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityUndefined (value) where
value :: Int
value = undefined
{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
