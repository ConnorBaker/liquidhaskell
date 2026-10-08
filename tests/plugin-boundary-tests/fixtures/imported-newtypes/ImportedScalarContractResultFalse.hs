module ImportedScalarContractResultFalse where

import ImportedConstructors (Packed (..))

{-@ measure metadata :: Packed a -> Int @-}
{-@ data Packed a where
      Packed :: n:Nat -> payload:a -> {t:Packed a | metadata t == n}
  @-}

{-@ create :: n:Nat -> a -> {t:Packed a | metadata t == n + 1} @-}
create :: Int -> a -> Packed a
create n payload = Packed n payload
