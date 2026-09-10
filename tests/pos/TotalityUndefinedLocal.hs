module TotalityUndefinedLocal (value) where
import Prelude hiding (undefined)

{-@ undefined :: {v:Int | v == 3} @-}
undefined :: Int
undefined = 3

{-@ value :: {v:Int | v == 3} @-}
value :: Int
value = undefined

{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
