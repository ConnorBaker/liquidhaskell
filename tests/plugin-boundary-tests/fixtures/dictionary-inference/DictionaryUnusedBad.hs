module DictionaryUnusedBad () where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return (assert (x > 0) x)

posM :: Monad m => m Int
posM = return 0

yM :: Monad m => m Int
yM = gpp posM
