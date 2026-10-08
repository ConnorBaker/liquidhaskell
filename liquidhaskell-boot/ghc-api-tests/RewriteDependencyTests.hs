module RewriteDependencyTests (tests) where

import qualified Data.HashSet as S
import Data.List (sort)
import Language.Haskell.Liquid.UX.DiffCheck (proofDependents)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    withResource (compileToCore "RewriteDependencies" source) (const (pure ())) $ \getProgram ->
        testGroup
            "rewrite proof dependencies"
            [ testCase "recursive members retain their actual call edges" $ do
                program <- getProgram
                owner <- named program "f"
                names (proofDependents program (const S.empty) [owner]) @?= ["f", "g"]
            , testCase "indirect callers cannot rewrite their prerequisite" $ do
                program <- getProgram
                owner <- named program "leaf"
                names (proofDependents program (const S.empty) [owner]) @?= ["leaf", "middle", "outer", "sibling"]
            , testCase "a shared callee is not a circular proof" $ do
                program <- getProgram
                owner <- named program "middle"
                names (proofDependents program (const S.empty) [owner]) @?= ["middle", "outer"]
            , testCase "local names do not create top-level dependencies" $ do
                program <- getProgram
                owner <- named program "outer"
                names (proofDependents program (const S.empty) [owner]) @?= ["outer"]
            , testCase "non-circular helper proof remains available" $ do
                program <- getProgram
                owner <- named program "helperA"
                rule <- named program "ruleA"
                let rewrites caller = if caller == owner then S.singleton rule else S.empty
                names (proofDependents program rewrites [owner] `S.intersection` rewrites owner) @?= []
            , testCase "explicit rewrite cycles need no Core cycle" $ do
                program <- getProgram
                first <- named program "ruleA"
                second <- named program "ruleB"
                let rewrites caller
                        | caller == first = S.singleton second
                        | caller == second = S.singleton first
                        | otherwise = S.empty
                names (proofDependents program rewrites [first]) @?= ["ruleA", "ruleB"]
            , testCase "global rewrites cannot mediate a proof cycle through helpers" $ do
                program <- getProgram
                owner <- named program "helperA"
                globals <- S.fromList <$> mapM (named program) ["theoremA", "theoremB"]
                let rewrites caller = if caller `S.member` globals then S.empty else globals
                names (proofDependents program rewrites [owner] `S.intersection` globals) @?= ["theoremA", "theoremB"]
            ]
  where
    names = sort . map G.getOccString . S.toList
    named program name = case [v | (v, _) <- G.flattenBinds program, G.getOccString v == name] of
        [owner] -> pure owner
        _ -> assertFailure ("missing or ambiguous actual owner: " ++ name) >> fail name
    source =
        unlines
            [ "module RewriteDependencies where"
            , "f, g, leaf, middle, outer, sibling, shadowed, ruleA, ruleB, helperA, helperB, theoremA, theoremB :: Bool -> Bool"
            , "f x = g x"
            , "g x = if x then f False else False"
            , "leaf x = x"
            , "middle x = leaf x"
            , "outer x = middle x"
            , "sibling x = leaf x"
            , "shadowed x = let outer y = y in outer x"
            , "ruleA x = x"
            , "ruleB x = x"
            , "helperA x = x"
            , "helperB x = x"
            , "theoremA x = helperA x"
            , "theoremB x = helperB x"
            ]
