{-# LANGUAGE TypeApplications #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityCaughtPureThrow (action) where

import Control.Exception (SomeException, evaluate, throw, try)

action :: IO Bool
action = caught

-- Catching the runtime exception does not satisfy the pure throw precondition.
-- Keep this private: an exported default contract hides the inferred false CAF.
caught :: IO Bool
caught = do
  result <- try @SomeException (evaluate (throw (userError "intentional") :: Int))
  pure (either (const True) (const False) result)
