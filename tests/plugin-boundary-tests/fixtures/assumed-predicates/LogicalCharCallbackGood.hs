module LogicalCharCallbackGood where

{-@ LIQUID "--higherorder" @-}

data Token = Token

{-@ measure observed :: Token -> Char @-}

{-@ applyObserved :: p:(Char -> Bool) -> token:Token
      -> {c:Char | c == observed token}
      -> {v:Bool | v <=> p (observed token)} @-}
applyObserved :: (Char -> Bool) -> Token -> Char -> Bool
applyObserved predicate _ character = predicate character
