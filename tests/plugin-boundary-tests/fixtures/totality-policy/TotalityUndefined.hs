module TotalityUndefined (value) where

-- GHC's undefined has no ordinary argument to carry an impossible domain.
-- Under totality, each use must prove that its context is unreachable.
value :: Int
value = undefined
