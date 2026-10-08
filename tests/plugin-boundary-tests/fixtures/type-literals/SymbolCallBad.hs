{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module SymbolCallBad where

import GHC.TypeLits (Symbol)

type role Key nominal
newtype Key (domain :: Symbol) = Key Int
type CandidateKey = Key "candidate_key"
type OtherKey = Key "other_key"

{-@ reflect accepts @-}
{-@ accepts :: CandidateKey -> {v:Bool | v} @-}
accepts :: Key "candidate_key" -> Bool
accepts _ = True

{-@ probe :: input:OtherKey -> {v:Bool | v == accepts input} @-}
probe :: OtherKey -> Bool
probe _ = True
