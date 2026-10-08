module LogicalCarrierCallbackBad where

data Token a = Token

{-@ measure value :: Token a -> a @-}

{-@ probe :: token:Token (Int -> Int) -> {v:Bool | value token 0 == 0} @-}
probe :: Token (Int -> Int) -> Bool
probe _ = True
