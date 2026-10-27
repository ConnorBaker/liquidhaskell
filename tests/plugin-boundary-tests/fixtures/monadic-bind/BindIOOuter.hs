module BindIOOuter where

import Data.IORef (IORef, modifyIORef')

-- A model of the ticks an action performs. The assumed contracts hold of
-- their bodies: pureIO ticks 0 times and tick ticks once.
{-@ measure effects :: IO a -> Int @-}

{-@ assume pureIO :: x:a -> {v:IO a | effects v == 0} @-}
pureIO :: a -> IO a
pureIO = pure

{-@ assume tick :: IORef Int -> {v:IO () | effects v == 1} @-}
tick :: IORef Int -> IO ()
tick r = modifyIORef' r (+ 1)

type MyIO = IO

{-@ quietOk :: {v:IO () | effects v == 0} @-}
quietOk :: IO ()
quietOk = pureIO ()

{-@ loud :: IORef Int -> {v:IO () | effects v == 0} @-}
loud :: IORef Int -> IO ()
loud r = tick r

-- quiet r ticks once: the bind's action is not the continuation's action.
{-@ quiet :: IORef Int -> {v:IO () | effects v == 0} @-}
quiet :: IORef Int -> IO ()
quiet r = do
  _ <- tick r
  pureIO ()

-- The same claim through a synonym of IO.
{-@ quietSyn :: IORef Int -> {v:MyIO () | effects v == 0} @-}
quietSyn :: IORef Int -> MyIO ()
quietSyn r = do
  _ <- tick r
  pureIO ()

-- quietRev r ticks once too: the bind's action is not e1's action either.
{-@ quietRev :: IORef Int -> {v:IO () | effects v == 0} @-}
quietRev :: IORef Int -> IO ()
quietRev r = do
  _ <- pureIO ()
  tick r
