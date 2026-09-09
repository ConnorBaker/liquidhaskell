{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Illegal type specification" @-}

-- | A strict field whose type is a NEWTYPE over @Int@, carrying a written
-- bound. @-funbox-small-strict-fields@ sees through the newtype and unboxes
-- to @Int#@, so the worker takes @Int#@ where the source field is @Pos@.
--
-- 'RefType.mkProductTy' rebuilds the field's refinement over the component,
-- and asks 'deepSplitProductType' which constructor to rebuild with. That
-- descent normalises THROUGH the newtype, so the constructor it hands back is
-- @GHC.Types.I#@ -- not @Pos@ -- and the emitted refinement is
-- @0 < posVal (I# v)@. @I#@ is not a logic constructor and @posVal@ takes a
-- @Pos@, so the declaration is rejected: @Illegal type specification for `T`@
-- with @Cannot unify Pos with int in expression: posVal (I# v)@. The
-- selector 'tp' is rejected alongside it.
--
-- The comment at 'rebuiltOverComponent' records a newtype guard as "measured
-- INERT" -- on an @IORef@ field carrying a TRIVIAL refinement, which never
-- reaches the rebuild. This module carries a real bound, and it is not inert.
-- The right rebuild is @0 < posVal (Pos v)@: @Pos@ IS a logic constructor
-- (the measure equation @posVal (Pos n) = n@ is stated over it) and it takes
-- an @int@. A GREEN means the rebuild names the newtype the field was
-- declared with rather than the constructor GHC normalised to, and the module
-- moves to @pos@ with 'useT' as its claim.
--
-- @-O0@ is SAFE: no unboxing, no expansion.
module NewtypeFieldReft where

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
