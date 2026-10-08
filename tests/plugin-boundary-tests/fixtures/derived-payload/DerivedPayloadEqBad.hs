module DerivedPayloadEqBad where

data Domain = DomainA !Bool !Integer | DomainB !Integer !Bool deriving (Eq)

{-@ requireTrue :: {value:Bool | value} -> () @-}
requireTrue :: Bool -> ()
requireTrue _ = ()

wrong :: ()
wrong = requireTrue False
