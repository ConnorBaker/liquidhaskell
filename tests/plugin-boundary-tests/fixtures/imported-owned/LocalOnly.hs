module LocalOnly (outer) where

{-@ outer :: value:Bool -> {result:Bool | result == value} @-}
outer :: Bool -> Bool
outer value = local value
  where
    {-@ local :: inner:Bool -> {result:Bool | result == inner} @-}
    local :: Bool -> Bool
    local inner = inner
