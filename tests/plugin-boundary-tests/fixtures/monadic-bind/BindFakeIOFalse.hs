module BindFakeIOFalse where

import Prelude hiding (IO)

-- A short-circuiting monad that is only named IO (not GHC.Types.IO).
data IO e a = Fail e | Ok a

instance Functor (IO e) where
  fmap _ (Fail e) = Fail e
  fmap f (Ok a) = Ok (f a)

instance Applicative (IO e) where
  pure = Ok
  Fail e <*> _ = Fail e
  Ok f <*> r = fmap f r

instance Monad (IO e) where
  Fail e >>= _ = Fail e
  Ok a >>= k = k a

-- bindFail (Fail (-1)) == Fail (-1).
{-@ bindFail :: IO Int Int -> IO {v:Int | v > 0} Int @-}
bindFail :: IO Int Int -> IO Int Int
bindFail e = do
  x <- e
  Ok x
