module NoncutExportNoShow where

newtype Gen a = Gen (Int -> a)

runGen :: Gen a -> Int -> a
runGen (Gen f) = f

instance Functor Gen where
  fmap f (Gen g) = Gen (\n -> f (g n))

instance Applicative Gen where
  pure x = Gen (\_ -> x)
  Gen f <*> Gen x = Gen (\n -> f n (x n))

instance Monad Gen where
  Gen g >>= k = Gen (\n -> runGen (k (g n)) n)

listOfG :: Gen a -> Gen [a]
listOfG g = Gen (\n -> [runGen g n])

chooseG :: Int -> Int -> Gen Int
chooseG lo _ = pure lo

class Arb a where
  arb :: Gen a

instance Arb Bool where
  arb = pure True

newtype Prov = Prov Int

provG :: Gen Prov
provG = Prov <$> chooseG 0 1

data Db = Db [Int] [Bool]

emptyDb :: Db
emptyDb = Db [] []

insertA :: Int -> Prov -> Db -> Db
insertA r _ (Db as bs) = Db (r : as) bs

insertB :: Bool -> Prov -> Db -> Db
insertB b _ (Db as bs) = Db as (b : bs)

instance Semigroup Db where
  Db a b <> Db c d = Db (a ++ c) (b ++ d)

newtype Wrap = Wrap Db

instance Arb Wrap where
  arb = do
    ints <- listOfG ((,) <$> chooseG 0 3 <*> provG)
    bools <- listOfG ((,) <$> arb <*> provG)
    let db =
          foldr (\(r, p) -> insertA r p) emptyDb ints
            <> foldr (\(b, p) -> insertB b p) emptyDb bools
    pure (Wrap db)

data Build = Build [(Int, Prov)] [(Bool, Prov)] [Db]

instance Arb Build where
  arb =
    Build
      <$> listOfG ((,) <$> chooseG 0 3 <*> provG)
      <*> listOfG ((,) <$> arb <*> provG)
      <*> listOfG ((\(Wrap db) -> db) <$> arb)

{-@ property :: Gen Bool @-}
property :: Gen Bool
property = (\(Build ints _ _) -> null ints) <$> arb
