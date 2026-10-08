module ImportedDeclaredConstructorFalse where

import ImportedConstructors (T (..))

{-@ measure metadata :: T -> Int @-}
{-@ data T where
      A :: T
      B :: n:Int -> {t:T | metadata t == n}
  @-}

{-@ untouched :: T -> {v:T | False} @-}
untouched :: T -> T
untouched t = t
