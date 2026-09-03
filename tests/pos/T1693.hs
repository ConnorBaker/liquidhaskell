-- | Applying a class method whose FIRST dictionary argument is not the refined
--   one must not crash constraint generation. `mapM` takes the `Traversable`
--   dictionary before the `Monad` one, which used to reach `getExprFun`'s
--   `panic` equation with "getFunName on Data.Traversable.mapM @ [] ...".
--
--   https://github.com/ucsd-progsys/liquidhaskell/issues/1693
module T1693 where

data T a = T a

instance Functor T where
  fmap f (T x) = T (f x)

instance Applicative T where
  pure = T
  T f <*> T x = T (f x)

{-@ instance Monad T where
      >>= :: T a -> (a -> T b) -> T b
  @-}
instance Monad T where
  T x >>= f = f x

ris :: (a -> T b) -> [a] -> T [b]
ris = mapM
