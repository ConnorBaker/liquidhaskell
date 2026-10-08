{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ClassMethodScopeGood where

class Scoped a where
    scoped :: forall b. (Integral b) => b -> a -> a

{-@ class Scoped a where
      scoped :: forall b. Integral b => {n:b | false} -> a -> a @-}

class ScopedPair left right where
    scopedPair :: forall n. (Integral n) => n -> left -> right -> left

{-@ class ScopedPair left right where
      scopedPair :: forall n. Integral n => {n:n | false} -> left -> right -> left @-}
