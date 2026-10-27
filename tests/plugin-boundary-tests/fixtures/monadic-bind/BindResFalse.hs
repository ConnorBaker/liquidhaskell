module BindResFalse where

-- A one-argument short-circuiting monad whose failure carries an Int.
data Res a = Bad Int | Good a

instance Functor Res where
  fmap _ (Bad n) = Bad n
  fmap f (Good a) = Good (f a)

instance Applicative Res where
  pure = Good
  Bad n <*> _ = Bad n
  Good f <*> r = fmap f r

instance Monad Res where
  Bad n >>= _ = Bad n
  Good a >>= k = k a

{-@ measure badPos @-}
badPos :: Res a -> Bool
badPos (Bad n) = n > 0
badPos (Good _) = True

{-@ good :: a -> {v:Res a | badPos v} @-}
good :: a -> Res a
good = Good

-- bindBad (Bad (-1)) == Bad (-1), and badPos (Bad (-1)) == False.
{-@ bindBad :: Res Int -> {v:Res Int | badPos v} @-}
bindBad :: Res Int -> Res Int
bindBad e = do
  x <- e
  good x
