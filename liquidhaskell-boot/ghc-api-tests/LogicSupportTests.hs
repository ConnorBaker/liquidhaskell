{-# LANGUAGE OverloadedStrings #-}

module LogicSupportTests (tests) where

import Control.Exception (throw)
import qualified Data.List as L
import Data.String (fromString)
import qualified GHC.Types.Name as Name
import qualified GHC.Unit.Types as Unit
import qualified Language.Fixpoint.Types as F
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Types
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Liquid.GHC.API as G
import Test.Tasty
import Test.Tasty.HUnit

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore = withResource prepare (const (pure ())) $ \fixture ->
    testGroup
        "typed logical support"
        [ testCase "actual source owner and established declaration sort" $ do
            (owner, _, _) <- fixture
            let (meaning, support) = interpret mempty (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
            map fst support @?= [owner]
            map snd support @?= [rTypeSort mempty (classRFInfoType True (ofType (G.varType owner) :: SpecType))]
        , testCase "lambda ownership does not become free support" $ do
            (_, body, _) <- fixture
            let (meaning, support) = interpret mempty body
            assertBool "source lambda meaning lost" (case meaning of F.ELam{} -> True; _ -> False)
            retainLogicSupport (F.syms meaning) support @?= []
        , testCase "actual alias disappears but its source dependency remains" $ do
            (owner, G.Lam argument _, _) <- fixture
            let alias = G.setVarType argument (G.varType owner)
                expression = G.Let (G.NonRec alias (G.Var owner)) (G.Var alias)
                (meaning, support) = interpret mempty expression
            meaning @?= F.EVar (F.symbol owner)
            map fst (retainLogicSupport (F.syms meaning) support) @?= [owner]
        , testCase "unused support does not force its embedding" $ do
            (owner, _, _) <- fixture
            let (meaning, _) = interpret (error "support-only embedding forced") (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
        , testCase "synonym, equality evidence and method dictionary retain declaration schemas" $ do
            (_, _, program) <- fixture
            mapM_ (checkOwner program) ["aliased", "equality", "method"]
        , testCase "native boolean owners retain primitive meaning" $ do
            (_, _, program) <- fixture
            checkBoolean program "disjoin" (\x y -> F.EIte x F.PTrue (F.EIte y F.PTrue F.PFalse))
            checkBoolean program "conjoin" (\x y -> F.EIte x (F.EIte y F.PTrue F.PFalse) F.PFalse)
            checkBoolean program "constant" const
            checkBoolean program "disjoinList" (\x y -> F.EIte x F.PTrue (F.EIte y F.PTrue F.PFalse))
            checkBoolean program "conjoinList" (\x y -> F.EIte x (F.EIte y F.PTrue F.PFalse) F.PFalse)
            (_, negateBody) <- sourceBody program "negateBoolean"
            case fst (interpret mempty negateBody) of
                F.ELam (x, _) value -> value @?= F.PNot (F.EVar x)
                meaning -> assertFailure ("missing negation lambda: " ++ show meaning)
        , testCase "same operator occurrence from a different source owner is not intrinsic" $ do
            (_, _, program) <- fixture
            operator <- sourceBody program "||"
            (_, body) <- sourceBody program "fakeDisjoin"
            let (meaning, _) = interpret mempty body
                owner = fst operator
            assertBool "foreign boolean owner granted primitive meaning" (F.symbol owner `elem` F.syms meaning)
        , testCase "generalized Foldable operation retains its actual dictionary owner" $ do
            (_, _, program) <- fixture
            (_, body) <- sourceBody program "foldableDisjoin"
            case G.collectBinders body of
                (_, application) | (G.Var owner, arguments) <- G.collectArgs application -> do
                    let (_, support) = interpret mempty body
                        dictionaries = [dictionary | G.Var dictionary <- arguments, G.isDictId dictionary]
                    assertBool "generalized function owner erased" (owner `elem` map fst support)
                    assertBool "missing actual Foldable source dictionary" (not (null dictionaries))
                    mapM_ (\dictionary -> assertBool "Foldable dictionary owner erased" (dictionary `elem` map fst support)) dictionaries
                _ -> assertFailure "missing actual generalized Foldable source application"
        , testCase "nonliteral list keeps its typed operation rather than becoming a boolean" $ do
            (_, _, program) <- fixture
            (_, body) <- sourceBody program "unknownDisjoin"
            case G.collectBinders body of
                ([argument], application) | (G.Var owner, _) <- G.collectArgs application -> do
                    let (meaning, support) = interpret mempty body
                    case meaning of
                        F.ELam (_, _) value -> value @?= F.EApp (F.EVar (F.symbol owner)) (F.EVar (F.symbol argument))
                        _ -> assertFailure "missing actual list source lambda"
                    assertBool "actual list operation owner erased" (owner `elem` map fst support)
                _ -> assertFailure "missing actual list source application"
        , testCase "native module and occurrence in a different unit do not grant primitive authority" $ do
            (_, _, program) <- fixture
            (_, body) <- sourceBody program "disjoin"
            case G.collectBinders body of
                ([x, y], application) | (G.Var owner, _) <- G.collectArgs application -> do
                    let actualName = G.getName owner
                        origin = G.nameModule actualName
                        foreignOrigin = G.mkModule (Unit.stringToUnit "unrelated-intrinsic-provider") (G.moduleName origin)
                        foreignName = Name.mkExternalName (G.mkUnique 'z' 917) foreignOrigin (G.nameOccName actualName) G.noSrcSpan
                        foreignOwner = G.setVarName owner foreignName
                        expression = G.App (G.App (G.Var foreignOwner) (G.Var x)) (G.Var y)
                        (meaning, _) = interpret mempty expression
                    meaning @?= F.EApp (F.EApp (F.EVar (F.symbol foreignOwner)) (F.EVar (F.symbol x))) (F.EVar (F.symbol y))
                _ -> assertFailure "missing actual native boolean source application"
        , testCase "a shared match-failure handler is not part of the logical meaning" $ do
            -- GHC binds the two failing branches to one join point whose body
            -- is an empty case on patError; readback must drop, not translate, it.
            (_, _, program) <- fixture
            (_, body) <- sourceBody program "secondOf"
            let symbols = F.syms (fst (interpret mempty body))
            assertBool ("failure branch reached the logic: " ++ show symbols) $
                not (any (\symbol -> "patError" `L.isInfixOf` F.symbolString symbol) symbols)
        , testCase "same prelude module and operator spelling do not grant an unrelated source owner a logical alias" $ do
            program <- compileToCore "Language.Haskell.Liquid.Prelude" $ unlines
                [ "module Language.Haskell.Liquid.Prelude where"
                , "(==>), (<=>) :: Bool -> Bool -> Bool"
                , "x ==> _ = x"
                , "x <=> _ = x"
                , "implication, equivalence :: Bool -> Bool -> Bool"
                , "implication x y = x ==> y"
                , "equivalence x y = x <=> y"
                ]
            mapM_ (\(operator, caller) -> do
                (owner, _) <- sourceBody program operator
                (_, body) <- sourceBody program caller
                let (meaning, _) = interpret mempty body
                assertBool "unrelated prelude owner granted hardcoded meaning" (F.symbol owner `elem` F.syms meaning))
                [("==>", "implication"), ("<=>", "equivalence")]
        ]
  where
    prepare = do
        program <- compileToCore "LogicalSupport" $ unlines
            [ "{-# LANGUAGE GADTs #-}"
            , "module LogicalSupport where"
            , "import Prelude hiding ((||))"
            , "import qualified Prelude as P"
            , "import qualified GHC.List as L"
            , "identity :: Int -> Int"
            , "identity x = x"
            , "type Alias = Int"
            , "aliased :: Alias -> Alias"
            , "aliased x = x"
            , "equality :: (a ~ b) => a -> b"
            , "equality x = x"
            , "class C a where observe :: a -> Bool"
            , "method :: C a => a -> Bool"
            , "method = observe"
            , "disjoin, conjoin, constant, disjoinList, conjoinList, fakeDisjoin :: Bool -> Bool -> Bool"
            , "disjoin x y = (P.||) x y"
            , "conjoin x y = (P.&&) x y"
            , "constant x y = P.const x y"
            , "disjoinList x y = L.or [x, y]"
            , "conjoinList x y = L.and [x, y]"
            , "foldableDisjoin :: Bool -> Bool -> Bool"
            , "foldableDisjoin x y = P.or [x, y]"
            , "unknownDisjoin :: [Bool] -> Bool"
            , "unknownDisjoin xs = L.or xs"
            , "negateBoolean :: Bool -> Bool"
            , "negateBoolean x = P.not x"
            , "(||) :: Bool -> Bool -> Bool"
            , "(||) x _ = x"
            , "fakeDisjoin x y = (||) x y"
            , "secondOf :: [Int] -> Int"
            , "secondOf xs = case xs of (_ : y : _) -> y"
            ]
        case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "identity"] of
            [(owner, body)] -> pure (owner, body, program)
            _ -> fail "missing actual source identity"
    checkOwner program name = case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == name] of
        [owner] -> do
            let (meaning, support) = interpret mempty (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
            map fst support @?= [owner]
            map snd support @?= [rTypeSort mempty (classRFInfoType True (ofType (G.varType owner) :: SpecType))]
        _ -> assertFailure ("missing actual source owner " ++ name)

sourceBody :: G.CoreProgram -> String -> IO (G.Var, G.CoreExpr)
sourceBody program name = case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == name] of
    [binding] -> pure binding
    _ -> fail ("missing actual source binding " ++ name)

checkBoolean :: G.CoreProgram -> String -> (F.Expr -> F.Expr -> F.Expr) -> Assertion
checkBoolean program name expected = do
    (_, body) <- sourceBody program name
    let (meaning, _) = interpret mempty body
    case meaning of
        F.ELam (x, _) (F.ELam (y, _) value) -> value @?= expected (F.EVar x) (F.EVar y)
        _ -> assertFailure ("missing boolean lambdas: " ++ show meaning)

interpret :: F.TCEmb G.TyCon -> G.CoreExpr -> (F.Expr, LogicSupport)
interpret embeddings expression =
    either throw id $
        Logic.runToLogic
            mempty
            embeddings
            mempty
            mempty
            defConfig
            (\message -> ErrOther G.noSrcSpan (fromString message))
            (Logic.coreToLogic expression)
