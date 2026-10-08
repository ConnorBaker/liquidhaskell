module ImportedConstructorClient where

import ImportedConstructors (T (A))

{-@ value :: T @-}
value :: T
value = A
