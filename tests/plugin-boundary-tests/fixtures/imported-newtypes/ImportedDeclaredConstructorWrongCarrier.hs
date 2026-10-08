module ImportedDeclaredConstructorWrongCarrier where

import ImportedConstructors (T (..))

{-@ data Bool where
      A :: Bool
      B :: n:Int -> Bool
  @-}

untouched :: T -> T
untouched t = t
