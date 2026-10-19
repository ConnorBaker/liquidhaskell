module IORefCallbackBad (Handle, newHandle, record, readSnapshot) where

import Data.IORef (IORef, modifyIORef', newIORef, readIORef)

data Snapshot = Snapshot {snapshotEvents :: [Int]}

data Handle = Handle
  { handleState :: !(IORef Snapshot)
  , handleLimit :: !Int
  }

{-@ impossible :: {v:Int | false} -> Int @-}
impossible :: Int -> Int
impossible n = n

newHandle :: Int -> IO Handle
newHandle limit = do
  state <- newIORef (Snapshot [])
  pure (Handle state limit)

record :: Handle -> Int -> IO ()
record handle x =
  modifyIORef' (handleState handle) $ \snapshot ->
    snapshot {snapshotEvents = take (impossible (handleLimit handle)) (x : snapshotEvents snapshot)}

readSnapshot :: Handle -> IO Snapshot
readSnapshot = readIORef . handleState
