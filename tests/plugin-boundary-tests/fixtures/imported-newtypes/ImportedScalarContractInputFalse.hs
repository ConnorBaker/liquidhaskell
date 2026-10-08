module ImportedScalarContractInputFalse where

import ImportedConstructors (Packed (..))

{-@ measure metadata :: Packed a -> Int @-}
{-@ data Packed a where
      Packed :: n:Nat -> payload:a -> {t:Packed a | metadata t == n}
  @-}

{-@ create :: Int -> a -> Packed a @-}
create :: Int -> a -> Packed a
create n payload = Packed n payload
