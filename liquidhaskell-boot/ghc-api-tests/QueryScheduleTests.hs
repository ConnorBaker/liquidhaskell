module QueryScheduleTests (tests) where

import Control.Concurrent (myThreadId, threadDelay)
import Control.Exception (ErrorCall (..), onException, throwIO, try)
import Control.Monad (when)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.List as L
import Language.Haskell.Liquid.Constraint.Schedule
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

-- The sequential fold over a module's query sequence is the authority. With
-- several jobs, a node observes only its dependencies and starts once they
-- have finished; results and failures still follow the sequence, and no more
-- than the given number of nodes run at once. The delays only make an
-- out-of-order completion possible; no assertion depends on how long a
-- builder takes, except where a slot or a dependency forbids the alternative.
tests :: TestTree
tests =
    testGroup
        "query schedule"
        [ testCase "one job runs every node in order on the caller's thread, observing every earlier node" $ do
            caller <- myThreadId
            seen <- newIORef []
            let node i = Node [] $ \observed -> do
                    thread <- myThreadId
                    record seen (i, observed, thread == caller)
                    pure i
            results <- runNodes 1 (map node [0 .. 3 :: Int])
            results @?= [0 .. 3]
            readIORef seen >>= (@?= [(i, [0 .. i - 1], True) | i <- [0 .. 3]]) . reverse
        , testCase "several jobs: each node observes its dependencies, in sequence order" $ do
            results <- runNodes 3
                [ Node [] (\_ -> pure [0 :: Int])
                , Node [] (\_ -> pure [1])
                , Node [1, 0] (\observed -> pure (2 : concat observed))
                , Node [2] (\observed -> pure (3 : concat observed))
                ]
            results @?= [[0], [1], [2, 0, 1], [3, 2, 0, 1]]
        , testCase "results keep sequence order when a later node finishes first" $ do
            finished <- newIORef []
            results <- runNodes 2
                [ Node [] (\_ -> threadDelay 300000 >> record finished (0 :: Int) >> pure 'a')
                , Node [] (\_ -> record finished 1 >> pure 'b')
                ]
            results @?= "ab"
            readIORef finished >>= (@?= [0, 1])
        , testCase "a node starts only after its dependencies have finished" $ do
            finished <- newIORef []
            observedFinished <- newIORef []
            _ <- runNodes 4
                [ Node [] (\_ -> threadDelay 300000 >> record finished (0 :: Int))
                , Node [] (\_ -> threadDelay 100000 >> record finished 1)
                , Node [0, 1] (\_ -> readIORef finished >>= record observedFinished >> record finished 2)
                , Node [2] (\_ -> readIORef finished >>= record observedFinished)
                ]
            readIORef observedFinished >>= (@?= [[2, 0, 1], [0, 1]])
        , testCase "exactly the given number of independent nodes run at once" $ do
            current <- newIORef (0 :: Int)
            highest <- newIORef 0
            let node = Node [] $ \_ -> do
                    now <- atomicModifyIORef' current (\n -> (n + 1, n + 1))
                    atomicModifyIORef' highest (\m -> (max m now, ()))
                    threadDelay 100000
                    atomicModifyIORef' current (\n -> (n - 1, ()))
            _ <- runNodes 3 (replicate 8 node)
            readIORef highest >>= (@?= 3)
        , testCase "the earliest failure is raised, though a later node fails first" $ do
            outcome <- try $ runNodes 3
                [ Node [] (\_ -> threadDelay 300000 >> throwIO (ErrorCall "earlier") :: IO ())
                , Node [] (\_ -> throwIO (ErrorCall "later"))
                ]
            outcome @?= Left (ErrorCall "earlier")
        , testCase "an earlier node still runs after a later one fails, and its failure wins" $ do
            outcome <- try $ runNodes 3
                [ Node [] (\_ -> threadDelay 200000)
                , Node [0] (\_ -> throwIO (ErrorCall "middle"))
                , Node [] (\_ -> throwIO (ErrorCall "last"))
                ]
            outcome @?= Left (ErrorCall "middle")
        , testCase "after a failure no later node starts, and running later nodes are cancelled" $ do
            started <- newIORef []
            cancelled <- newIORef False
            outcome <- try $ runNodes 2
                [ Node [] (\_ -> record started (0 :: Int) >> threadDelay 100000 >> throwIO (ErrorCall "first"))
                , Node [] (\_ -> (record started 1 >> threadDelay 10000000) `onException` atomicModifyIORef' cancelled (const (True, ())))
                , Node [] (\_ -> record started 2)
                ]
            outcome @?= Left (ErrorCall "first")
            -- Both slots are taken before the failure, so node 2 can only
            -- have started after it.
            readIORef started >>= (@?= [0, 1]) . L.sort
            readIORef cancelled >>= assertBool "the running later node was cancelled"
        , testCase "a dependency on a node that is not earlier is refused" $ do
            outcome <- try (runNodes 2 [Node [1] (\_ -> pure ()), Node [] (\_ -> pure ())])
            case outcome of
                Left (ErrorCall _) -> pure ()
                Right _ -> assertFailure "accepted a dependency on a later node"
        , testCase "one job raises the first failure in sequence, running nothing after it" $ do
            started <- newIORef []
            outcome <- try $ runNodes 1 [Node [] (\_ -> record started (i :: Int) >> failAt i) | i <- [0 .. 3]]
            outcome @?= Left (ErrorCall "1")
            readIORef started >>= (@?= [1, 0])
        ]
  where
    record :: IORef [a] -> a -> IO ()
    record ref x = atomicModifyIORef' ref (\xs -> (x : xs, ()))
    failAt :: Int -> IO ()
    failAt i = when (i == 1) (throwIO (ErrorCall (show i)))
