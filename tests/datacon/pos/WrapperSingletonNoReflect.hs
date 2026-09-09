{-# OPTIONS_GHC -O1 #-}

-- | Control: a constructor SINGLETON stated over the bare constructor, with no
-- reflection and no PLE.
--
-- From @-O1@ up the construction 'mk' compiles to the wrapper @$WW@, and the
-- wrapper's spec entry gets its singleton from 'strengthenDataConType' via
-- 'workerApp' -- 0afb8b22's constraint-generation half -- as @{v | v == W n}@
-- over the worker symbol. @UnpackedFieldWorkerSingleton.hs@ pins that
-- mechanism through a REFLECTED function and @--ple@; this is the same
-- mechanism with nothing in between, on a field whose sort does not change.
--
-- A red here would mean @v == W n@ over a bare constructor is not an accepted
-- spelling at @-O1@ -- and every reflection-based arm is then measuring
-- reflection, not the seam.
module WrapperSingletonNoReflect where

data W = W !Int

{-@ mk :: n:Int -> {v:W | v == W n} @-}
mk :: Int -> W
mk n = W n
