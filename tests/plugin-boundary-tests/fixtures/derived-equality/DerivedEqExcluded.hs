{-# LANGUAGE DerivingVia #-}

module DerivedEqExcluded where

import Data.Text (Text)

-- No derived contract: each claim below is UNSAFE at its body.

-- Text's (==) compares content; its logical values are representations.
data Named = Named Text deriving (Eq)

{-@ sameNamed :: x:Named -> y:Named -> {v:Bool | v <=> x == y} @-}
sameNamed :: Named -> Named -> Bool
sameNamed x y = x == y

-- Double's (==) is not reflexive at NaN.
data Measure = Measure Double deriving (Eq)

{-@ sameMeasure :: x:Measure -> y:Measure -> {v:Bool | v <=> x == y} @-}
sameMeasure :: Measure -> Measure -> Bool
sameMeasure x y = x == y

-- A hand-written instance means what its body says.
data Coarse = Fine | Rough

instance Eq Coarse where
  _ == _ = True

{-@ sameCoarse :: x:Coarse -> y:Coarse -> {v:Bool | v <=> x == y} @-}
sameCoarse :: Coarse -> Coarse -> Bool
sameCoarse x y = x == y

-- Derived via another type's (==), not structurally.
newtype Always a = Always a

instance Eq (Always a) where
  _ == _ = True

data Via = Via Int deriving (Eq) via (Always Via)

{-@ sameVia :: x:Via -> y:Via -> {v:Bool | v <=> x == y} @-}
sameVia :: Via -> Via -> Bool
sameVia x y = x == y

-- A parameter's instance is unknown at the declaration.
data Box a = Box a deriving (Eq)

{-@ sameBox :: x:Box Int -> y:Box Int -> {v:Bool | v <=> x == y} @-}
sameBox :: Box Int -> Box Int -> Bool
sameBox x y = x == y
