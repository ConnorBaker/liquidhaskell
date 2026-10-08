module LogicalCharCallbackBad where

{-@ LIQUID "--higherorder" @-}

data Token = Token

{-@ measure observed :: Token -> Char @-}

{-@ witness :: allowed:Char -> p:({c:Char | c == allowed} -> Bool)
      -> token:Token -> {v:Bool | p (observed token)} -> Bool @-}
witness :: Char -> (Char -> Bool) -> Token -> Bool -> Bool
witness _ _ _ answer = answer
