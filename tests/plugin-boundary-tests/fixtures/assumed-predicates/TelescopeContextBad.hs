module TelescopeContextBad where

{-@ probe :: forall a <p :: a -> Bool>. b:Bool -> (x:a<p> -> {v:a | b => v == x}) -> a<p> -> a<p> @-}
probe :: Bool -> (a -> a) -> a -> a
probe _ callback value = callback value
