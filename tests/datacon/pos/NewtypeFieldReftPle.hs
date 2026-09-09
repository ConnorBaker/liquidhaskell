{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}

-- | The PLE arm of @tests/datacon/neg/NewtypeFieldReft.hs@: a strict field
-- whose type is a NEWTYPE over @Int@, carrying a written bound.
-- @-funbox-small-strict-fields@ sees through the newtype and the worker
-- takes @Int#@ where the source field is @Pos@.
--
-- The 'RepMap' commit makes the declaration well formed: the bound is
-- rebuilt over the component as @0 < posVal (Pos v)@ -- @Pos@ is the newtype
-- recorded in 'frVia', not the @I#@ that normalising through it produced --
-- and the selector @tp@ is kept with the equation @tp (T y) = Pos y@. What
-- the consumer 'useT' then needs is @posVal (Pos n) == n@, a MEASURE
-- EQUATION applied to a term the program never constructs, which without
-- PLE is opaque to the solver. With @--ple@ it is SAFE; the module without
-- the flag is the negative, pinning @Liquid Type Mismatch@ at 'useT'.
module NewtypeFieldReftPle where

newtype Pos = Pos Int

{-@ measure posVal @-}
posVal :: Pos -> Int
posVal (Pos n) = n

{-@ data T = T { tp :: {v:Pos | 0 < posVal v} } @-}
data T = T { tp :: !Pos }

{-@ mk :: {n:Int | 0 < n} -> T @-}
mk :: Int -> T
mk n = T (Pos n)

{-@ useT :: T -> {v:Int | 0 < v} @-}
useT :: T -> Int
useT (T (Pos n)) = n
