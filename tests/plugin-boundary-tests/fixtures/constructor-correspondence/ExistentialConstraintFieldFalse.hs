module ExistentialConstraintFieldFalse where

data Encoder input = forall field. (Show field) => Encoder Int (input -> Maybe field)

{-@ data Encoder input where
      Encoder :: forall input field. (Show field) => {key:Int | key > 0} -> (input -> Maybe field) -> Encoder input @-}

encoder :: Encoder Int
encoder = Encoder 0 Just
