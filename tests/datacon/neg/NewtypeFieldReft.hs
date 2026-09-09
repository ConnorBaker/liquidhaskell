{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | A strict field whose type is a NEWTYPE over @Int@, carrying a written
-- bound. @-funbox-small-strict-fields@ sees through the newtype and unboxes
-- to @Int#@, so the worker takes @Int#@ where the source field is @Pos@.
--
-- Until the 'RepMap' commit this pinned @Illegal type specification@: the
-- bound was rebuilt over the component with the constructor GHC normalised
-- to, @0 < posVal (I# v)@, and @I#@ is not a logic constructor. The rebuild
-- is now @0 < posVal (Pos v)@ -- @Pos@ is the newtype recorded in 'frVia' --
-- and the declaration is accepted; the selector @tp@ is kept with the
-- equation @tp (T y) = Pos y@.
--
-- What is pinned NOW is the half that remains: 'useT' needs
-- @posVal (Pos n) == n@, and a measure equation is not a rewrite the solver
-- applies to a term the program never constructs -- the @Pos n@ here exists
-- only inside a refinement. Without PLE that is @Liquid Type Mismatch@ at
-- 'useT', with the inferred @0 < posVal (Pos bx)@ visibly in the context;
-- @tests/datacon/pos/NewtypeFieldReftPle.hs@ is the same module under
-- @--ple@ and is SAFE. A GREEN here means the fact reaches the consumer
-- without PLE -- for instance by instantiating the newtype constructor's own
-- measure equations beside the rebuilt bound -- and the module moves to
-- @pos@.
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
