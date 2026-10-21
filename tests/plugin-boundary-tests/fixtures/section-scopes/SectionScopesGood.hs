{-@ LIQUID "--eliminate=all" @-}
module SectionScopesGood where

-- Each operator section binds GHC's template locals v_B1 and v_B3 (and the
-- lambda's v_B2), so the two sections below bind v_B3 at Char and at [Char].
-- A-normalization floats both bindings into the body's let chain.

newtype G a = G (Int -> a)

instance Functor G where
  fmap f (G g) = G (\i -> f (g i))

instance Applicative G where
  pure x = G (\_ -> x)
  G f <*> G x = G (\i -> f i (x i))

instance Monad G where
  G x >>= k = G (\i -> let G y = k (x i) in y i)

{-@ elements :: {xs:[a] | len xs > 0} -> G a @-}
elements :: [a] -> G a
elements (x : _) = G (\_ -> x)

mutated :: String -> G String
mutated value = do
  edit <- elements [filter (/= '.'), id]
  keep <- elements [(/= "x"), const True]
  pure (if keep value then edit value else value)
