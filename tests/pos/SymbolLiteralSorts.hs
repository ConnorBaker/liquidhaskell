{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--total-Haskell" @-}
module SymbolLiteralSorts where

import GHC.TypeLits (Symbol)

newtype Tagged (domain :: Symbol) = Tagged { taggedValue :: Int }
type Component = Tagged "component id"
type Platform = Tagged "platform name"
data Package = Package { component :: Component, platform :: Platform }

{-@ measure taggedValue @-}
{-@ measure component @-}
{-@ measure platform @-}

{-@ pack :: c:Component -> p:Platform -> {v:Package | taggedValue (component v) == taggedValue c && taggedValue (platform v) == taggedValue p} @-}
pack :: Component -> Platform -> Package
pack c p = Package c p

-- Exercise a higher-order partial constructor with two distinct label types.
packMaybe :: Component -> Maybe Platform -> Maybe Package
packMaybe c platforms = Package c <$> platforms

{-@ apply :: f:(Component -> Platform -> Package) -> c:Component -> p:Platform -> {v:Package | v == f c p} @-}
apply :: (Component -> Platform -> Package) -> Component -> Platform -> Package
apply function c p = function c p

{-@ fail wrongPayload @-}
{-@ wrongPayload :: c:Component -> p:Platform -> {v:Package | taggedValue (component v) == taggedValue c} @-}
wrongPayload :: Component -> Platform -> Package
wrongPayload c p = Package (Tagged (taggedValue c + 1)) p

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
