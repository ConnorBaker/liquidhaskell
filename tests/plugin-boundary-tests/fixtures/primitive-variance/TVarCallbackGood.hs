module TVarCallbackGood (Handle, newHandle, record, readSnapshot) where

import GHC.Conc (TVar, atomically, newTVarIO, readTVar, readTVarIO, writeTVar)

data Snapshot = Snapshot {snapshotEvents :: [Int]}

data Handle = Handle
  { handleState :: !(TVar Snapshot)
  , handleLimit :: !Int
  }

{-@ impossible :: {v:Int | false} -> Int @-}
impossible :: Int -> Int
impossible n = n

modify :: TVar a -> (a -> a) -> IO ()
modify tv f = atomically (readTVar tv >>= writeTVar tv . f)

newHandle :: Int -> IO Handle
newHandle limit = do
  state <- newTVarIO (Snapshot [])
  pure (Handle state limit)

record :: Handle -> Int -> IO ()
record handle x =
  modify (handleState handle) $ \snapshot ->
    snapshot {snapshotEvents = take (handleLimit handle) (x : snapshotEvents snapshot)}

readSnapshot :: Handle -> IO Snapshot
readSnapshot = readTVarIO . handleState
