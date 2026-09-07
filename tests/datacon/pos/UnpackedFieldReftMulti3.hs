{-# OPTIONS_GHC -O1 #-}

-- | @UnpackedFieldReftMulti.hs@ with the two things that branch can get wrong
-- varied: THREE components rather than two, and the unpacked field in the
-- MIDDLE of the record rather than at its end.
--
-- Three components means the rebuilt application has two earlier binders to
-- name, not one, so an off-by-one in the split lands here and not there; a
-- later field means the refinement is attached to a component that is not the
-- constructor's last argument, so an attachment written as "the last binder of
-- the spec" rather than "the last component of this field" is wrong here and
-- right there. The measure reads the MIDDLE component for the same reason --
-- an application built in the wrong order is still well sorted when every
-- component is an @Int@, and only a projection that is not symmetric in them
-- can see it.
module UnpackedFieldReftMulti3 where

data P3 = P3 !Int !Int !Int

{-@ measure p3Snd @-}
p3Snd :: P3 -> Int
p3Snd (P3 _ b _) = b

{-@ data K = K [Int] {v : P3 | p3Snd v <= 10} Int @-}
data K = K ![Int] {-# UNPACK #-} !P3 !Int

{-@ needSmall :: {v : P3 | p3Snd v <= 10} -> Int @-}
needSmall :: P3 -> Int
needSmall (P3 _ b _) = b

useK :: K -> Int
useK (K _ p _) = needSmall p
