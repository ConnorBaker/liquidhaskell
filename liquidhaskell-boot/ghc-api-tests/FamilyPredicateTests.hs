{-# LANGUAGE OverloadedStrings #-}

module FamilyPredicateTests (tests) where

import Control.Exception (evaluate, try)
import Control.Monad.IO.Class (liftIO)
import qualified Data.HashMap.Strict as M
import Data.IORef (newIORef)
import Data.List (isInfixOf)
import Data.String (fromString)
import qualified GHC.Builtin.Types as G
import qualified GHC.Paths
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Resolve (ofBareType)
import Language.Haskell.Liquid.Bare.ToBare (specToBare)
import Language.Haskell.Liquid.Bare.Types (Env (..), GHCTyLookupEnv (..))
import Language.Haskell.Liquid.Measure (definitionFitsInput)
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.Errors (TError (ErrOther), UserError)
import Language.Haskell.Liquid.Types.Names (makeGHCLHNameLocated)
import Language.Haskell.Liquid.Types.PredType (makeTyConInfo)
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RefType (appRTyCon, ofType, strengthen, uTop)
import Language.Haskell.Liquid.Types.Types (BodyV (..), DefV (..), TyConMap (..))
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import Language.Haskell.Liquid.UX.Config (Config (typeclass))
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit

data Fixture = Fixture G.TyCon G.TyCon G.TyCon G.TyCon G.DataCon G.DataCon G.CoreProgram

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    withResource prepare (const (pure ())) $ \fixture ->
        testGroup "family predicate dispatch" $
            [ testCase "all-empty family omits only predicate dispatch" $ do
                Fixture family key _ nested _ _ _ <- fixture
                let info = metadata [(key, []), (nested, [])]
                M.null (tcmFIRTy info) @?= True
                M.null (tcmFtcArity info) @?= True
                assertBool "representation metadata was dropped" (all (`M.member` tcmTyRTy info) [key, nested])
                keyArguments <- arguments key
                nestedArguments <- arguments nested
                selected info family keyArguments @?= []
                selected info family nestedArguments @?= []
            , testCase "origin predicates survive fallback but empty instances override them" $ do
                Fixture family key other _ _ _ _ <- fixture
                let info = metadata [(family, ["origin"]), (key, []), (other, [])]
                M.size (tcmFIRTy info) @?= 2
                M.lookup family (tcmFtcArity info) @?= Just 1
                keyArguments <- arguments key
                otherArguments <- arguments other
                selected info family keyArguments @?= []
                selected info family otherArguments @?= []
                selected info family [G.boolTy, G.boolTy] @?= ["origin"]
            , testCase "instance predicates retain their own dispatch and empty siblings" $ do
                Fixture family key other _ _ _ _ <- fixture
                let info = metadata [(family, ["origin"]), (key, ["instance"]), (other, [])]
                M.size (tcmFIRTy info) @?= 2
                M.lookup family (tcmFtcArity info) @?= Just 1
                keyArguments <- arguments key
                otherArguments <- arguments other
                selected info family keyArguments @?= ["instance"]
                selected info family otherArguments @?= []
                selected info family [G.boolTy, G.boolTy] @?= ["origin"]
            ]
                ++ [ testCase ("mixed arities remain rejected with " ++ owner ++ " predicates") $ do
                        Fixture family key _ nested _ _ _ <- fixture
                        let declarations = zip [family, key, nested] predicates
                        rejected <- try (evaluate (M.size (tcmFtcArity (metadata declarations)))) :: IO (Either UserError Int)
                        case rejected of
                            Left err@ErrOther{} ->
                                assertBool "wrong rejection" ("makeTyConInfo: Conflicting arities for TyCon:" `isInfixOf` F.showpp err)
                            Left err -> assertFailure ("wrong error category: " ++ F.showpp err)
                            Right _ -> assertFailure "an empty instance hid conflicting predicate-dispatch arities"
                   | (owner, predicates) <-
                        [ ("origin", [["origin"], [], []])
                        , ("prefix instance", [[], ["instance"], []])
                        , ("nested instance", [[], [], ["instance"]])
                        ]
                   ]
                ++ [ testCase "bare family resolution preserves an authored root judgment" $ do
                        Fixture family _ _ _ _ _ _ <- fixture
                        let original = strengthen (ofType (G.mkTyConApp family [G.boolTy, G.intTy])) (uTop (F.Reft ("result", F.PFalse)))
                        resolved <- resolveCarrier [family, G.boolTyCon, G.intTyCon] original
                        resolved @?= original
                   , testCase "source and worker family receivers share exact index instantiation" $ do
                        Fixture _ _ _ _ nested _ _ <- fixture
                        let representation = G.dataConTyCon nested
                            source = G.mkFamilyTyConApp representation [G.boolTy, G.intTy]
                            worker = G.mkTyConApp representation [G.boolTy, G.intTy]
                            phantomMismatch = G.mkFamilyTyConApp representation [G.charTy, G.intTy]
                            equation = Def (makeGHCLHNameLocated nested) nested (Just (ofType source)) [("field", Just (ofType G.intTy))] (E (F.EVar "field"))
                        mapM_
                            ( \target -> do
                                assertBool "source family receiver rejected" (definitionFitsInput source target equation)
                                assertBool "worker family receiver rejected" (definitionFitsInput worker target equation)
                                assertBool "phantom family index mismatch admitted" (not (definitionFitsInput phantomMismatch target equation))
                            )
                            [G.dataConWrapperType nested, G.varType (G.dataConWorkId nested)]
                   , testCase "family field and original receiver retain one substitution" $ do
                        Fixture _ _ _ _ nested _ _ <- fixture
                        let source = G.mkFamilyTyConApp (G.dataConTyCon nested) [G.boolTy, G.intTy]
                            equation = Def (makeGHCLHNameLocated nested) nested (Just (ofType source)) [("field", Just (ofType G.boolTy))] (E (F.EVar "field"))
                        mapM_
                            (\target -> assertBool "Integer receiver admitted a Bool field" (not (definitionFitsInput source target equation)))
                            [G.dataConWrapperType nested, G.varType (G.dataConWorkId nested)]
                   , testCase "repeated family index coordinates remain nominally equal" $ do
                        Fixture family _ _ _ _ repeated _ <- fixture
                        let source = G.mkFamilyTyConApp (G.dataConTyCon repeated) [G.boolTy, G.intTy]
                            mismatched = G.mkTyConApp family [G.mkTyConApp (G.tupleTyCon G.Boxed 2) [G.boolTy, G.charTy], G.intTy]
                            equation = Def (makeGHCLHNameLocated repeated) repeated (Just (ofType source)) [("field", Just (ofType G.intTy))] (E (F.EVar "field"))
                        mapM_
                            ( \target -> do
                                assertBool "lawful repeated family index rejected" (definitionFitsInput source target equation)
                                assertBool "different repeated family indices admitted" (not (definitionFitsInput mismatched target equation))
                            )
                            [G.dataConWrapperType repeated, G.varType (G.dataConWorkId repeated)]
                   , testCase "source family wrapper names the canonical source constructor" $ do
                        Fixture _ _ _ _ nested _ program <- fixture
                        checkConstructorMeaning program "makeNested" nested 1
                   , testCase "existential wrapper follows actual source value order" $ do
                        Fixture _ _ _ _ _ _ program <- fixture
                        ordered <- constructorTyCon program "extractReordered"
                        case G.tyConDataCons ordered of
                            [constructor] -> checkConstructorMeaning program "makeReordered" constructor 2
                            _ -> assertFailure "fixture lost its reordered constructor"
                   , testCase "wrapper retains runtime dictionary before ordered source fields" $ do
                        Fixture _ _ _ _ _ _ program <- fixture
                        constrained <- constructorTyCon program "extractConstrained"
                        case G.tyConDataCons constrained of
                            [constructor] -> checkConstructorMeaning program "makeConstrained" constructor 3
                            _ -> assertFailure "fixture lost its constrained constructor"
                   ]
  where
    prepare = do
        program <- compileToCore "FamilyPredicateFixture" source
        key <- constructorTyCon program "extractKey"
        other <- constructorTyCon program "extractOther"
        nested <- constructorTyCon program "extractNested"
        repeated <- constructorTyCon program "extractRepeated"
        case G.tyConFamInst_maybe key of
            Just (family, _) -> do
                assertBool "fixture instances have different families" $
                    all ((== Just family) . fmap fst . G.tyConFamInst_maybe) [other, nested]
                case (G.tyConDataCons nested, G.tyConDataCons repeated) of
                    ([nestedConstructor], [repeatedConstructor]) -> pure (Fixture family key other nested nestedConstructor repeatedConstructor program)
                    _ -> fail "fixture lost its single family constructors"
            Nothing -> fail "fixture lost its data-family instance"

checkConstructorMeaning :: G.CoreProgram -> String -> G.DataCon -> Int -> IO ()
checkConstructorMeaning program name constructor arity =
    case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == name] of
        [(owner, body)] ->
            case Logic.runToLogic mempty mempty mempty mempty defConfig{typeclass = True} (\message -> ErrOther G.noSrcSpan (fromString message)) (Logic.coreToFun (F.dummyLoc (F.symbol owner)) owner body) of
                Left err -> assertFailure (F.showpp err)
                Right ((arguments', meaning), _) -> do
                    length arguments' @?= arity
                    let values = map (F.EVar . F.symbol) arguments'
                        application fields = Right (F.mkEApp (F.dummyLoc (F.symbol constructor)) fields)
                    meaning @?= application values
                    if arity > 1
                        then assertBool "wrapper exchanged distinct source fields" (meaning /= application (reverse values))
                        else pure ()
        _ -> assertFailure ("missing fixture builder: " ++ name)

-- These closed carriers need only actual GHC name lookup, not module metadata.
resolveCarrier :: [G.TyCon] -> SpecType -> IO SpecType
resolveCarrier constructors original = G.runGhc (Just GHC.Paths.libdir) $ do
    session <- G.getSession
    reference <- liftIO (newIORef session)
    let unused = error "closed carrier resolution consulted unrelated source metadata"
        environment =
            RE
                { reTyLookupEnv = GHCTyLookupEnv (G.Session reference) (G.mkTypeEnv (map G.ATyCon constructors))
                , reTcGblEnv = unused
                , reInstEnvs = unused
                , reUsedExternals = unused
                , reLMap = unused
                , reDataConIds = unused
                , reCfg = unused
                , reLocalVars = unused
                , reGlobSyms = unused
                , reSrc = unused
                }
    liftIO $ evaluate $ ofBareType environment (F.dummyPos "family root judgment") Nothing (specToBare original)

metadata :: [(G.TyCon, [F.Symbol])] -> TyConMap
metadata declarations =
    makeTyConInfo mempty (filter G.isFamInstTyCon (map fst declarations)) (map fst declarations) (map declaration declarations)
  where
    declaration (constructor, predicates) =
        TyConP
            (F.dummyPos "family predicate test")
            constructor
            (map RTV (G.tyConTyVars constructor))
            [PV name (ofType G.boolTy :: RSort) [] | name <- predicates]
            []
            []
            Nothing

selected :: TyConMap -> G.TyCon -> [G.Type] -> [F.Symbol]
selected info family types =
    map pname $ snd $ appRTyCon mempty info (RTyCon family [] defaultTyConInfo) (map ofType types :: [SpecType])

arguments :: G.TyCon -> IO [G.Type]
arguments constructor = case G.tyConFamInst_maybe constructor of
    Just (_, types) -> pure types
    Nothing -> fail "fixture lost its family arguments"

constructorTyCon :: G.CoreProgram -> String -> IO G.TyCon
constructorTyCon program name = case [body | (owner, body) <- G.flattenBinds program, G.getOccString owner == name] of
    [body] -> go body
    _ -> fail ("missing fixture function: " ++ name)
  where
    go (G.Lam _ body) = go body
    go (G.Tick _ body) = go body
    go (G.Case _ _ _ alternatives) = case [G.dataConTyCon constructor | G.Alt (G.DataAlt constructor) _ _ <- alternatives] of
        [constructor] -> pure constructor
        _ -> fail ("missing fixture constructor: " ++ name)
    go _ = fail ("unexpected fixture body: " ++ name)

source :: String
source =
    unlines
        [ "{-# LANGUAGE TypeFamilies, GADTs, ExplicitForAll #-}"
        , "module FamilyPredicateFixture where"
        , "data Key = Key"
        , "data Other = Other"
        , "data family Family tag a"
        , "data instance Family Key a = FamilyValue a"
        , "data instance Family Other a = OtherValue a"
        , "data instance Family (Maybe tag) a = NestedFamily a"
        , "data instance Family (tag, tag) a = RepeatedFamily a"
        , "extractKey :: Family Key a -> a"
        , "extractKey (FamilyValue value) = value"
        , "extractOther :: Family Other a -> a"
        , "extractOther (OtherValue value) = value"
        , "extractNested :: Family (Maybe tag) a -> a"
        , "extractNested (NestedFamily value) = value"
        , "extractRepeated :: Family (tag, tag) a -> a"
        , "extractRepeated (RepeatedFamily value) = value"
        , "makeNested :: Integer -> Family (Maybe Bool) Integer"
        , "makeNested value = NestedFamily value"
        , "data Ordered a b where"
        , "  Reordered :: forall c a. c -> a -> Ordered a (Maybe c)"
        , "extractReordered :: Ordered a b -> a"
        , "extractReordered (Reordered _ value) = value"
        , "makeReordered :: Integer -> Bool -> Ordered Bool (Maybe Integer)"
        , "makeReordered first second = Reordered first second"
        , "class Evidence a"
        , "data Constrained a b where"
        , "  Constrained :: forall c a. Evidence c => c -> a -> Constrained a (Maybe c)"
        , "extractConstrained :: Constrained a b -> a"
        , "extractConstrained (Constrained _ value) = value"
        , "makeConstrained :: Evidence c => c -> Bool -> Constrained Bool (Maybe c)"
        , "makeConstrained first second = Constrained first second"
        ]
