module LogicalCarrierGood where

import Data.Kind (Type)

type Token :: forall {k}. k -> Type
data Token a = Token

{-@ measure value :: Token a -> a @-}
{-@ class measure logicalSize :: forall f a. f a -> Int @-}

{-@ same :: token:Token a -> {v:Bool | value token == value token} @-}
same :: Token (a :: Type) -> Bool
same _ = True

{-@ echo :: token:Token a -> x:{v:a | v == value token} -> {v:a | v == value token} @-}
echo :: Token a -> a -> a
echo _ x = x

{-@ kinded :: xs:[a] -> {v:Bool | logicalSize xs == logicalSize xs} @-}
kinded :: [a] -> Bool
kinded _ = True

data Flag = forall a. (Show a) => Flag Bool a

{-@ measure flag :: Flag -> Bool
      flag (Flag b _) = b
  @-}
