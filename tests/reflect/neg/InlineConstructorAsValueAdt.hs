{-@ LIQUID "--ple" @-}
{-@ LIQUID "--adt" @-}
{-@ LIQUID "--expect-error-containing=requires the --higherorder flag" @-}

-- | The constructor passed as a value inside an `inline` body, under `--adt`
--   WITHOUT `--higherorder`: refused, not crashed.
--
--   Same source as `tests/reflect/pos/InlineConstructorAsValue.hs`. The
--   inline leaf is lifted before the module's datatypes are declared and
--   carries no `DataConMap`, so under `--adt` `firstOrderOnly` withholds eta
--   from every lambda in an inline body and refuses what is left:
--
--   > Cannot inline haskell function `mkW`
--   > the body contains a lambda, which requires the --higherorder flag
--
--   Before: the parent crashed with `unknown constant ds_dJo##1`; a cut that
--   eta-reduced the lambda here crashed with `unknown constant apply##1 (Int
--   (Array Int W))`. Pinned by substring, not `--expect-any-error`, because
--   both of those also fail the module.
module InlineConstructorAsValueAdt where

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
