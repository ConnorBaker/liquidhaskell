{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module CharCallBad where

type role Key nominal
newtype Key (domain :: Char) = Key Int
type CandidateKey = Key 'a'
type OtherKey = Key 'b'

{-@ reflect accepts @-}
{-@ accepts :: CandidateKey -> {v:Bool | v} @-}
accepts :: Key 'a' -> Bool
accepts _ = True

{-@ probe :: input:OtherKey -> {v:Bool | v == accepts input} @-}
probe :: OtherKey -> Bool
probe _ = True
