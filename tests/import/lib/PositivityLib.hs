-- | `T` is positive. `[]` is one level out from `T`, so it lands in this
--   module's `tycons'` and gets its real variance here.
module PositivityLib where

data T = A [T] | B

-- | Contravariant in @a@, and positive as a type -- @Pred@ does not occur in
--   its own fields. Imported by PositivityImportNeg to place a negative occurrence behind a
--   container the client must get the variance of.
newtype Pred a = Pred (a -> Bool)
