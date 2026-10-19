module LocalRefCallbackBad (Handle, newHandle, record, readSnapshot) where

data Ref a = Ref a

modifyRef :: Ref a -> (a -> a) -> IO ()
modifyRef (Ref a) f = f a `seq` pure ()

newRef :: a -> IO (Ref a)
newRef a = pure (Ref a)

readRef :: Ref a -> IO a
readRef (Ref a) = pure a

data Snapshot = Snapshot {snapshotEvents :: [Int]}

data Handle = Handle
  { handleState :: !(Ref Snapshot)
  , handleLimit :: !Int
  }

{-@ impossible :: {v:Int | false} -> Int @-}
impossible :: Int -> Int
impossible n = n

newHandle :: Int -> IO Handle
newHandle limit = do
  state <- newRef (Snapshot [])
  pure (Handle state limit)

record :: Handle -> Int -> IO ()
record handle x =
  modifyRef (handleState handle) $ \snapshot ->
    snapshot {snapshotEvents = take (impossible (handleLimit handle)) (x : snapshotEvents snapshot)}

readSnapshot :: Handle -> IO Snapshot
readSnapshot = readRef . handleState
