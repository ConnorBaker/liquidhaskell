{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module LiteralProducer where

import GHC.TypeLits (Nat, Symbol)

type role SymbolKey nominal
newtype SymbolKey (label :: Symbol) = SymbolKey Int
type role NatKey nominal
newtype NatKey (label :: Nat) = NatKey Int
type role CharKey nominal
newtype CharKey (label :: Char) = CharKey Int
type Named = SymbolKey "$LH_RHOLE"
type Counted = NatKey 7
type Lettered = CharKey 'a'

{-@ symbolIdentity :: x:Named -> {v:Named | v == x} @-}
symbolIdentity :: Named -> Named
symbolIdentity x = x

{-@ natIdentity :: x:Counted -> {v:Counted | v == x} @-}
natIdentity :: Counted -> Counted
natIdentity x = x

{-@ charIdentity :: x:Lettered -> {v:Lettered | v == x} @-}
charIdentity :: Lettered -> Lettered
charIdentity x = x

-- Inference must not invent predicates on the non-runtime index kinds.
indexIdentity :: NatKey index -> NatKey index
indexIdentity value = value

namedIndexIdentity :: SymbolKey index -> SymbolKey index
namedIndexIdentity value = value

inferredCounted :: Counted -> Counted
inferredCounted value = let use = indexIdentity in use value

inferredNamed :: Named -> Named
inferredNamed value = let use = namedIndexIdentity in use value
