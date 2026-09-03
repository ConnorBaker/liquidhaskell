-- | The `Foldable` variant of #1693: `foldMap` takes the `Foldable` dictionary
--   before the refined `Monoid` one. The refinement must sit on the `Monoid` of
--   the fold's RESULT type -- a `Semigroup`-only spec does not reach this path,
--   and `mconcat`, which takes only the `Monoid` dictionary, never did.
module T1693A where

data Acc = Acc Int

instance Semigroup Acc where
  Acc x <> Acc y = Acc (x + y)

{-@ instance Monoid Acc where
      mappend :: Acc -> Acc -> Acc
  @-}
instance Monoid Acc where
  mempty  = Acc 0
  mappend = (<>)

total :: [Acc] -> Acc
total = foldMap id
