-- TAG: instances

-- | Typing class-instances
module Inst00 where

-- | Step 1: Refine type dictionaries:
class Compare a where
    cmax :: a -> a -> a
    cmin :: a -> a -> a

instance Compare Int where
    {-@ instance Compare Int where
            cmax :: x:Int -> y:Int -> {v:Int | (x mod 2 == 1 && y mod 2 == 1) => v mod 2 == 1} ;
            cmin :: Int -> Int -> Int
      @-}

    cmax y x = if x >= y then x else y
    cmin y x = if x >= y then x else y

-- The instance accepts the entire class input domain. Its stronger result
-- condition still specializes to Odd -> Odd -> Odd for an odd-input caller;
-- dictionary checking must not erase the class's unrestricted input domain.

{-@ foo :: Odd -> Odd -> Odd @-}
foo :: Int -> Int -> Int
foo x y = cmax x y
