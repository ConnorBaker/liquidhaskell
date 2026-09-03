{-@ LIQUID "--expect-any-error" @-}

-- | Making `getExprFun` total must not make the application it used to panic
--   on verify for free. `foldMap` reaches the fallback, which checks the
--   application with the method's ordinary type, so a result refinement that
--   type cannot establish is still reported.
module T1693B where

data Acc = Acc Int

{-@ measure accVal @-}
accVal :: Acc -> Int
accVal (Acc n) = n

instance Semigroup Acc where
  Acc x <> Acc y = Acc (x + y)

{-@ instance Monoid Acc where
      mappend :: Acc -> Acc -> Acc
  @-}
instance Monoid Acc where
  mempty  = Acc 0
  mappend = (<>)

{-@ total :: [Acc] -> { v : Acc | accVal v == 0 } @-}
total :: [Acc] -> Acc
total = foldMap id
