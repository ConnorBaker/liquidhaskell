module ImportedConstructorFalse where

import ImportedConstructors (T (A))

{-@ value :: {v:T | False} @-}
value :: T
value = A
