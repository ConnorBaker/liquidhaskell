module HigherKindedCallbackBad where

data Box a = Box a

{-@ measure content @-}
content :: Box a -> a
content (Box x) = x

{-@ positive :: {v:Box Int | content v > 0} -> Bool @-}
positive :: Box Int -> Bool
positive _ = True

{-@ invoke :: value:f a -> ({v:f a | v = value} -> b) -> b @-}
invoke :: f a -> (f a -> b) -> b
invoke value callback = callback value

bad :: Bool
bad = invoke (Box 0) positive
