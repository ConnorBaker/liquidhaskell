module ProjectionSharingFalse where

data Box a = Box a

{-@ measure field :: Box a -> a
      field (Box x) = x @-}

{-@ falseResult :: n:Integer -> flag:Bool
      -> {v:Bool | not v && field (Box n) == n && field (Box flag) == flag} @-}
falseResult :: Integer -> Bool -> Bool
falseResult _ _ = True
