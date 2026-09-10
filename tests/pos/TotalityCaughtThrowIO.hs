{-# LANGUAGE TypeApplications #-}

module TotalityCaughtThrowIO (action) where

import Control.Exception (SomeException, throwIO, try)

action :: IO Bool
action = caught

-- An exception-producing IO action is a value, unlike a pure thrown exception.
caught :: IO Bool
caught = do
  result <- try @SomeException (throwIO (userError "intentional") :: IO Int)
  pure (either (const True) (const False) result)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
