module SourceImportTests (tests) where

import CompilerFixture
import Control.Monad (forM_)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: IO Compiler -> Optimization -> TestTree
tests compiler optimization =
    testGroup
        "source import provenance"
        $ [ testGroup
                label
                [ sourceCase "reflexive concrete field" declaration operator True [] Safe
                , sourceCase "concrete field counterclaim" declaration operator False [] (UnsafeAt [failureLine])
                ]
          | (label, declaration, operator, failureLine) <-
                [ ("package re-export", "import GHC.Classes ((==))", "==", 9)
                , ("qualified source alias", "import qualified GHC.Classes as Chosen", "Chosen.==", 9)
                , ("package-qualified re-export", "import \"ghc-prim\" GHC.Classes ((==))", "==", 9)
                , ("facade before defining owner", "import qualified GHC.Classes as Chosen\nimport \"ghc-internal\" GHC.Internal.Classes ((==))", "Chosen.==", 10)
                , ("defining owner before facade", "import \"ghc-internal\" GHC.Internal.Classes ((==))\nimport qualified GHC.Classes as Chosen", "Chosen.==", 10)
                ]
          ]
            ++ [ sourceCase
                    "defining module does not invent a facade companion"
                    "import \"ghc-internal\" GHC.Internal.Classes ((==))"
                    "=="
                    True
                    []
                    (UnsafeAt [9])
               , sourceCase "exact defining package excludes a facade companion" "import \"ghc-prim\" GHC.Classes ((==))" "==" True ["--exclude-automatic-assumptions-for=ghc-internal"] (UnsafeAt [9])
               , sourceCase "unit display prefix is not its package name" "import GHC.Classes ((==))" "==" True ["--exclude-automatic-assumptions-for=ghc"] Safe
               , sourceCase "exposing package exclusion does not change the defining owner" "import \"ghc-prim\" GHC.Classes ((==))" "==" True ["--exclude-automatic-assumptions-for=ghc-prim"] Safe
               , testCase "local same spelling does not acquire native field meaning" $
                    withSystemTempDirectory "lh-source-import-local" $ \directory -> do
                        tool <- compiler
                        writeFixture "local operator" directory "SourceImport" $
                            source "import GHC.Types (Bool(False))" "==" True
                                ++ "\n(==) :: Int -> Int -> Bool\n_ == _ = False\n"
                        _ <- compile tool Strict optimization ObjectCode directory "SourceImport" [] [] (UnsafeAt [9])
                        pure ()
               , testCase "ordinary re-export retains selected companion dependencies" $
                    withSystemTempDirectory "lh-source-import-reexport" $ \directory -> do
                        tool <- compiler
                        let provider = directory </> "producer"
                        writeFixture "source facade" provider "SourceFacade" $
                            unlines
                                [ "{-# LANGUAGE NoImplicitPrelude #-}"
                                , "module SourceFacade (module GHC.Classes) where"
                                , "import GHC.Classes"
                                ]
                        _ <- compile tool Strict optimization ObjectCode provider "SourceFacade" [] [] Safe
                        forM_ [(True, Safe), (False, UnsafeAt [9])] $ \(good, expected) -> do
                            let client = directory </> if good then "good" else "bad"
                            writeFixture "source facade client" client "SourceImport" $ source "import SourceFacade ((==))" "==" good
                            _ <- compile tool Strict optimization ObjectCode client "SourceImport" [provider </> "objects"] [] expected
                            pure ()
               , testCase "regular companion ambiguity cannot fall back to a plugin provider" $
                    withSystemTempDirectory "lh-source-import-ambiguity" $ \directory -> do
                        tool <- compiler
                        configurations <- mapM (companion tool directory) ["left", "right"]
                        selected <- withPackageDatabase tool (directory </> "package-db") configurations
                        let client = directory </> "client"
                        writeFixture "ambiguous companion" client "SourceImport" $ source "import \"ghc-prim\" GHC.Classes ((==))" "==" True
                        _ <-
                            compile selected Strict optimization ObjectCode client "SourceImport" [] [] $
                                DependencyAmbiguity "GHC.Classes_LHAssumptions" ["source-companion-left", "source-companion-right"]
                        pure ()
               ]
  where
    sourceCase label declaration operator good options expected =
        testCase label $
            withSystemTempDirectory "lh-source-import" $ \directory -> do
                tool <- compiler
                writeFixture label directory "SourceImport" $ source declaration operator good
                _ <- compile tool Strict optimization ObjectCode directory "SourceImport" [] options expected
                pure ()
    companion tool directory side = do
        let provider = directory </> side
            name = "GHC/Classes_LHAssumptions"
            packageName = "source-companion-" ++ side
        createDirectoryIfMissing True (provider </> "GHC")
        createDirectoryIfMissing True (provider </> "objects/GHC")
        writeFixture "plain companion" provider name $
            unlines ["{-# LANGUAGE NoImplicitPrelude #-}", "module GHC.Classes_LHAssumptions where"]
        _ <- compileHaskell tool optimization provider name ["-this-unit-id", packageName]
        let configuration = provider </> "package.conf"
        writeFile configuration $
            unlines
                [ "name: " ++ packageName
                , "version: 0"
                , "id: " ++ packageName
                , "key: " ++ packageName
                , "exposed: True"
                , "exposed-modules: GHC.Classes_LHAssumptions"
                , "import-dirs: " ++ provider </> "objects"
                ]
        pure configuration

source :: String -> String -> Bool -> String
source declaration operator good =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude, PackageImports #-}"
        , "module SourceImport where"
        , ""
        , "import GHC.Types (Int, Bool)"
        , declaration
        , ""
        , "{-@ check :: x:Int -> y:Int -> {v:Bool | v} @-}"
        , "check :: Int -> Int -> Bool"
        , "check x y = x " ++ operator ++ if good then " x" else " y"
        ]
