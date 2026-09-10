module Main where

import Test.Tasty
import ErrorFilterReportTests
import TidyTests

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" $
        errorFilterReportTests ++ tidyTests
