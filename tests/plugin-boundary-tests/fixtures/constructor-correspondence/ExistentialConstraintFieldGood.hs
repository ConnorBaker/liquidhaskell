module ExistentialConstraintFieldGood where

-- The constraint is not a field: the specification refines the two fields.
data Encoder input = forall field. (Show field) => Encoder Int (input -> Maybe field)

{-@ data Encoder input where
      Encoder :: forall input field. (Show field) => {key:Int | key > 0} -> (input -> Maybe field) -> Encoder input @-}

{-@ encoderKey :: Encoder input -> {key:Int | key > 0} @-}
encoderKey :: Encoder input -> Int
encoderKey (Encoder key _) = key

encoder :: Encoder Int
encoder = Encoder 1 Just
