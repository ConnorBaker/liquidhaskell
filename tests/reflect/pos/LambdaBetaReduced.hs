{-@ LIQUID "--ple" @-}

-- | A GUARD for the precision of `firstOrderOnly`: a lambda that is present
--   in the SOURCE but not in the lifted body is neither refused nor rewritten.
--
--   `(\x -> W x) n` is beta-reduced by GHC before anything is lifted, so the
--   body `coreToLg` sees is `W n` and the reflected equation carries no `ELam`
--   for eta-reduction or the refusal to act on. Without `--higherorder` this is
--   SAFE (2 constraints checked) on the parent library, with the refusal alone,
--   and now; it attributes nothing and pins that both steps read the LIFTED
--   term and not the source. `tests/reflect/pos/ConstructorAsValueLambda.hs`
--   differs only in routing the lambda through `apply`, where it survives to
--   the lifted term and eta removes it.
module LambdaBetaReduced where

data W = W !Int

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = (\x -> W x) n

{-@ mkWIsW :: n:Int -> {v:() | mkW n == W n} @-}
mkWIsW :: Int -> ()
mkWIsW _ = ()
