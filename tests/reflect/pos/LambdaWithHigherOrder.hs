{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}

-- | The positive half of `tests/reflect/neg/LambdaWithoutHigherOrder.hs`: the
--   SAME source, with the flag the refusal asks for.
--
--   `\x -> x + 1` survives eta-reduction, so this is a lambda that really
--   reaches liquid-fixpoint. Under `--higherorder` it is defunctionalized
--   (binder renamed to `lam_arg##i` and declared), and `--etabeta` lets PLE
--   beta-reduce `(\x -> x + 1) n` once `apply` has been unfolded, so
--   `mkI n == n + 1` is PROVED. This is what makes the refusal in the negative
--   test honest: the lambda is representable, and the message names exactly
--   the flag that makes it so. Without `--etabeta` the same module is a
--   `Liquid Type Mismatch`: the flag alone makes the term representable, not
--   the claim provable.
--
--   Before the refusal this module was already SAFE under these flags; it is
--   here as the other side of the negative, not as a regression pin.
module LambdaWithHigherOrder where

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect mkI @-}
mkI :: Int -> Int
mkI n = apply (\x -> x + 1) n

{-@ mkIIsInc :: n:Int -> {v:() | mkI n == n + 1} @-}
mkIIsInc :: Int -> ()
mkIIsInc _ = ()
