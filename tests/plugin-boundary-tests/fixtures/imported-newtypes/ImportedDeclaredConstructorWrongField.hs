module ImportedDeclaredConstructorWrongField where

import ImportedConstructors (T (..))

{-@ data T where
      A :: T
      B :: Integer -> T
  @-}

untouched :: T -> T
untouched t = t
