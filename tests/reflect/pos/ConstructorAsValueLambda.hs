{-@ LIQUID "--ple" @-}

-- | `tests/reflect/pos/ConstructorAsValue.hs` with the lambda written OUT in
--   the source: `apply (\x -> W x) n` is what the desugarer produces for
--   `apply W n`, so the two must lift to the same definition, `apply W n`.
--
--   This is the shape a user sees in an error message about the previous two
--   modules and might reasonably write by hand; it pins that eta-reduction
--   reads the LIFTED term and does not care whether the lambda was written or
--   manufactured. (`LambdaBetaReduced.hs` is the other half: a written lambda
--   GHC removes itself.)
--
--   Before: the fixpoint crash on the parent library, `Cannot lift Haskell
--   function mkW` with the refusal alone. After: SAFE (2 constraints checked).
module ConstructorAsValueLambda where

data W = W !Int

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = apply (\x -> W x) n

{-@ mkWIsW :: n:Int -> {v:() | mkW n == W n} @-}
mkWIsW :: Int -> ()
mkWIsW _ = ()
