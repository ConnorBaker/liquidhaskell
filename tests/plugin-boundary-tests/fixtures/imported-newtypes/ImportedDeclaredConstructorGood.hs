module ImportedDeclaredConstructorGood where

import ImportedConstructors (T (..))

{-@ measure metadata :: T -> Int @-}
{-@ data T where
      A :: T
      B :: n:Int -> {t:T | metadata t == n}
  @-}

{-@ untouched :: t:T -> {v:T | v == t} @-}
untouched :: T -> T
untouched t = t
