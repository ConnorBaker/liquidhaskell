{-# LANGUAGE ScopedTypeVariables #-}

-- | Bounded, dependency-ordered checking of a module's query sequence.
--
-- A source module is checked as a sequence of nodes (proof groups and the
-- queries around them), each consuming what earlier nodes established. That
-- sequential fold is the authority. With one job every node runs in sequence
-- and observes every earlier node's result; nothing is forked. With more jobs
-- a node observes only the results of its declared dependencies, starts once
-- they have finished (earliest ready node first), and at most @jobs@ nodes run
-- at once. The two agree when no node's result depends on an earlier node
-- outside its dependencies. The caller owns that claim; comparing the two
-- schedules tests it.
--
-- Results are returned in sequence order, whatever order nodes finish in. A
-- failure is the one the sequential fold raises: that of the earliest failing
-- node. Once a node fails, no later node is started and running later nodes
-- are cancelled; earlier nodes still run, since one of them may fail first.
-- Every started node has finished, or been cancelled and has stopped, before
-- 'runNodes' returns or raises a node's failure. An asynchronous exception to
-- the caller cancels every running node and propagates at once.
module Language.Haskell.Liquid.Constraint.Schedule
  ( Node (..)
  , runNodes
  ) where

import           Control.Concurrent      (ThreadId, forkIOWithUnmask, killThread)
import           Control.Concurrent.Chan (newChan, readChan, writeChan)
import qualified Control.Exception       as Ex
import           Control.Monad           (forM, unless)
import qualified Data.IntMap.Strict      as IntMap
import qualified Data.IntSet             as IntSet

data Node a = Node
  { nodeDependencies :: [Int]
    -- ^ Earlier nodes (sequence indices) whose results this node observes.
  , nodeRun          :: [a] -> IO a
    -- ^ Checks the node, given the observed results in sequence order.
  }

type Failure = Ex.ExceptionWithContext Ex.SomeException

data State a = State
  { pending :: !IntSet.IntSet
  , running :: !(IntMap.IntMap ThreadId)
  , done    :: !(IntMap.IntMap a)
  , failure :: !(Maybe (Int, Failure))
  }

-- | Check the nodes with at most the given number running at once.
runNodes :: Int -> [Node a] -> IO [a]
runNodes jobs nodes
  | jobs <= 1 = sequential [] nodes
  | otherwise = do
      unless (and [all (\j -> j >= 0 && j < i) (nodeDependencies node) | (i, node) <- indexed]) $
        Ex.throwIO (Ex.ErrorCall "Schedule.runNodes: a node depends on a node that is not earlier")
      concurrent
  where
    indexed = zip [0 :: Int ..] nodes
    table = IntMap.fromList indexed
    count = length nodes
    dependencies = IntMap.map (IntSet.toAscList . IntSet.fromList . nodeDependencies) table

    sequential earlier [] = pure (reverse earlier)
    sequential earlier (node : rest) = do
      result <- nodeRun node (reverse earlier)
      sequential (result : earlier) rest

    concurrent = do
      events <- newChan
      let start i observed = Ex.mask_ $ forkIOWithUnmask $ \unmask -> do
            outcome <- Ex.tryWithContext (unmask (nodeRun (table IntMap.! i) observed))
            writeChan events (i, outcome)
          -- No node after the earliest failure can change the outcome.
          cutoff state = maybe count fst (failure state)
          ready state i = all (`IntMap.member` done state) (dependencies IntMap.! i)
          step state = do
            let slots = jobs - IntMap.size (running state)
                chosen = take slots [i | i <- IntSet.toAscList (pending state), i < cutoff state, ready state i]
            started <- forM chosen $ \i -> (,) i <$> start i [done state IntMap.! j | j <- dependencies IntMap.! i]
            let state' = state {pending = pending state `IntSet.difference` IntSet.fromList chosen, running = running state `IntMap.union` IntMap.fromList started}
            if IntMap.null (running state')
              then finish state'
              else do
                (i, outcome) <- readChan events `Ex.onException` mapM_ killThread (IntMap.elems (running state'))
                let state'' = state' {running = IntMap.delete i (running state')}
                case outcome of
                  _ | i > cutoff state'' -> step state''
                  Right result -> step state'' {done = IntMap.insert i result (done state'')}
                  Left caught -> do
                    let (later, _) = IntMap.partitionWithKey (\k _ -> k > i) (running state'')
                    mapM_ killThread (IntMap.elems later) `Ex.onException` mapM_ killThread (IntMap.elems (running state''))
                    step state'' {failure = Just (i, caught)}
          finish state = case failure state of
            Just (_, caught) -> Ex.rethrowIO caught
            Nothing
              | IntMap.size (done state) == count -> pure (IntMap.elems (done state))
              | otherwise -> Ex.throwIO (Ex.ErrorCall "Schedule.runNodes: a node was never ready")
      Ex.mask_ (step State {pending = IntSet.fromList [0 .. count - 1], running = IntMap.empty, done = IntMap.empty, failure = Nothing})
