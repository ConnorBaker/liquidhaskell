{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--etabeta"    @-}

-- | GUARD: the constructor passed as a value inside an `inline` body, under
--   `--reflection`, must keep its lambda and verify -- SAFE (2 constraints
--   checked) on the parent and now.
--
--   `inline` bodies are lifted at stage 0 of `Bare.makeGhcSpec0`, before the
--   module's datatypes are declared, so `firstOrderOnly` has no `DataConMap`
--   there and cannot tell that the eta result `W` is a data constructor. A cut
--   that eta-reduced it anyway took this module from SAFE (2) on the parent to
--   `crash: SMTLIB2 respSat = Error "... unknown constant apply##0 (Int (Array
--   Int W))"` under `--reflection`, whose `--adt` half makes z3 read a bare
--   `declare-datatypes` constructor at an array sort. With no oracle, the
--   inline leaf withholds eta from every lambda under `--adt`; with
--   `--higherorder` on, as `--reflection` implies, the lambda `\ds -> $WW ds`
--   serializes as an `Int`-sorted `smt_lambda##` and the module is SAFE (2).
--   Its twin `tests/reflect/neg/InlineConstructorAsValueAdt.hs` is the same
--   source under `--ple --adt` alone, refused.
module InlineConstructorAsValue where

{-# NOINLINE apply #-}
{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

data W = W !Int

{-@ inline mkW @-}
mkW :: Int -> W
mkW n = apply W n

{-@ useIt :: n:Int -> {v:W | v == mkW n} @-}
useIt :: Int -> W
useIt n = apply W n
