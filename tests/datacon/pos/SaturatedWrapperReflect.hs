{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}

-- | Control: a REFLECTED construction through the wrapper, saturated, on a
-- field whose sort does NOT change (@!Int@ to @Int#@, both @int@).
--
-- 'CoreToLogic.toLogicApp' sees @C.App (C.Var $WW) n@, and 'workerApp'
-- rewrites it to @W n@ over the worker -- 0afb8b22's lifting half. That fix
-- is pinned by @UnpackedFieldWorkerApp.hs@ on a RESORTED field (@Notes@ over a
-- @Set@), where the rewrite also changes the argument's sort. Here it is a
-- pure rename: the same-sort control that shows the rewrite is not merely
-- about resorting.
--
-- A red here would mean the wrapper-to-worker rewrite does not fire on the
-- simplest saturated construction.
module SaturatedWrapperReflect where

data W = W !Int

{-@ reflect mkW @-}
mkW :: Int -> W
mkW n = W n

{-@ mkWIsW :: n:Int -> {v:() | mkW n == W n} @-}
mkWIsW :: Int -> ()
mkWIsW _ = ()
