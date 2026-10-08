module DefaultSchemaSharingTests (tests, schemas) where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (forM, void)
import Control.Monad.State (runState)
import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Types as F
import qualified Language.Haskell.Liquid.Constraint.Fresh as CGFresh
import Language.Haskell.Liquid.Constraint.Init (DefaultTypes, initCGI, prepareDefaultTypes)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import qualified Language.Haskell.Liquid.Types.Fresh as Fresh
import Language.Haskell.Liquid.Types.PredType (makeTyConInfo)
import Language.Haskell.Liquid.Types.RType (PVarBV (..), RSort, RTyCon (rtc_info), RTyVar (..), RTypeBV (..), SizeFunV (..), SpecType, TyConInfo (sizeFunction), TyConP (..), rTyConPVs)
import Language.Haskell.Liquid.Types.RefType (ofType, rTypeSort, toType)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (TyConMap (..))
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import Language.Haskell.Liquid.UX.Config (Config)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

-- Metadata belongs to the initializer; native row inventories belong to the
-- actual source being checked, including callers with a different base target.
schemas :: TargetInfo -> TargetInfo -> DefaultTypes
schemas base stage =
    let names = gsName (giSpec base)
     in prepareDefaultTypes
            (gsTyconEnv names)
            (gsTcEmbeds names)
            (giImpVars (giSrc stage))
            (gsDataConIds (gsName (giSpec stage)))

tests :: (Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
tests emptyTarget compileToCore =
    testGroup
        "ordered native schema sharing"
        [ testCase "preparing the product does not demand unused metadata or rows" $
            void (evaluate (prepareDefaultTypes (error "unused type metadata") (error "unused embedding") (error "unused imports") (error "unused constructors")))
        , testCase "empty inventories do not demand native metadata" $ do
            let (imports, constructors, conlike) = prepareDefaultTypes (error "empty metadata") (error "empty embedding") [] []
            map length [imports, constructors, conlike] @?= [0, 0, 0]
        , testCase "native rows retain duplicate order, conlike rows and exact fresh effects" $ withOwner $ \owner -> do
            let info = withInventories [owner, constructor, owner] [otherConstructor, otherConstructor] empty
                prepared = schemas empty info
                (imports, constructors, conlike) = prepared
            map fst imports @?= [owner, constructor, owner]
            map fst constructors @?= [otherConstructor, otherConstructor]
            map fst conlike @?= [constructor]
            mapM_ (comparePrefix info prepared) [(allow, start) | allow <- [False, True], start <- [0, 103]]
        , testCase "base metadata never substitutes the base native inventory" $ withOwner $ \owner -> do
            let base = withInventories [otherConstructor] [] empty
                stage = withInventories [owner, constructor] [constructor] empty
                prepared = schemas base stage
            map fst (firstRows prepared) @?= [owner, constructor]
            comparePrefixWith base stage prepared (False, 17)
        , testCase "captured predicates, family dispatch and embedding do not become stage metadata" $ do
            program <-
                compileToCore "DefaultFamilySchema" $
                    unlines
                        [ "{-# LANGUAGE TypeFamilies #-}"
                        , "module DefaultFamilySchema where"
                        , "data family Family tag a"
                        , "data instance Family (Maybe tag) a = Nested a"
                        , "value :: Family (Maybe Bool) Int"
                        , "value = Nested 1"
                        ]
            case [(owner, rhs) | (owner, rhs) <- G.flattenBinds program, G.getOccString owner == "value"] of
                [(owner, rhs)] -> case fst (G.collectArgs (withoutCast rhs)) of
                    G.Var worker | Just constructor <- G.isDataConId_maybe worker -> do
                        let representation = G.dataConTyCon constructor
                        case G.tyConFamInst_maybe representation of
                            Just (family, _) -> do
                                let metadata origin instancePredicate =
                                        makeTyConInfo
                                            mempty
                                            [representation]
                                            [family, representation]
                                            [ TyConP
                                                (F.dummyPos "default schema metadata")
                                                tc
                                                (map RTV (G.tyConTyVars tc))
                                                [PV predicate (ofType G.boolTy :: RSort) []]
                                                []
                                                []
                                                Nothing
                                            | (tc, predicate) <- [(family, origin), (representation, instancePredicate)]
                                            ]
                                    embedding sort = F.tceInsert family sort F.NoArgs (F.tceInsert representation sort F.NoArgs mempty)
                                    withMetadata predicates embed info =
                                        let spec = giSpec info
                                         in info{giSpec = spec{gsName = (gsName spec){gsTyconEnv = predicates, gsTcEmbeds = embed}}}
                                    base = withMetadata (metadata (F.symbol "baseOrigin") (F.symbol "baseInstance")) (embedding F.FInt) empty
                                    stage =
                                        withMetadata
                                            (metadata (F.symbol "stageOrigin") (F.symbol "stageInstance"))
                                            (embedding (F.fObj (F.dummyLoc (F.symbol "stageFamily"))))
                                            (withInventories [owner] [G.dataConWorkId constructor, G.dataConWrapId constructor] empty)
                                    prepared = schemas base stage
                                    (actual, _) = runState (preparedPrefix False prepared) (initCGI cfg base stage)
                                assertBool "family dispatch metadata was empty" (not (M.null (tcmFIRTy (gsTyconEnv (gsName (giSpec base))))))
                                case firstRows actual of
                                    [(_, ty@(RApp tc typeArguments arguments _))] -> do
                                        map pname (rTyConPVs tc) @?= [F.symbol "baseInstance"]
                                        length arguments @?= 1
                                        sizeFunction (rtc_info tc) @?= Just IdSizeFun
                                        rTypeSort (embedding F.FInt) ty @?= F.fApp F.FInt (map (rTypeSort (embedding F.FInt)) typeArguments)
                                        assertBool "the nested source family input changed" (G.eqType (toType False ty) (G.varType owner))
                                    _ -> assertFailure "expected the source family application with its instance predicate"
                                mapM_ (comparePrefixWith base stage prepared) [(allow, start) | allow <- [False, True], start <- [17, 103]]
                            Nothing -> assertFailure "expected a resolved data-family representation"
                    _ -> assertFailure "expected the actual family constructor worker"
                _ -> assertFailure "expected one concrete family source owner"
        , testCase "unselected checking obligations are not used to prepare schemas" $ withOwner $ \owner -> do
            let spec = giSpec empty
                poisoned = empty{giSpec = spec{gsSig = (gsSig spec){gsReftChecks = [error "unused checking obligation"]}, gsData = (gsData spec){gsUnsorted = [([], error "unused checking template")]}}}
                stage = withInventories [owner] [] empty
            void (evaluate (rnf (map snd (firstRows (schemas poisoned stage)))))
        , testCase "filtered Core and stage obligations retain the native declaration inventories" $ withOwner $ \owner -> do
            let original = withInventories [owner, constructor] [otherConstructor] empty
                source = original{giSrc = (giSrc original){giCbs = []}}
                spec = giSpec source
                stage = source{giSpec = spec{gsSig = (gsSig spec){gsTySigs = []}, gsData = (gsData spec){gsMeasures = []}, gsRefl = (gsRefl spec){gsMyAxioms = []}}}
            let observed info = let (a, b, c) = schemas original info in map (map (F.symbol . fst)) [a, b, c]
            observed stage @?= observed original
            comparePrefix stage (schemas original stage) (False, 0)
        ]
  where
    cfg = CmdLine.defConfig
    empty = emptyTarget cfg
    constructor = G.dataConWorkId G.trueDataCon
    otherConstructor = G.dataConWorkId G.falseDataCon
    firstRows :: DefaultTypes -> [(G.Var, SpecType)]
    firstRows (rows, _, _) = rows
    withoutCast (G.Cast expression _) = withoutCast expression
    withoutCast expression = expression
    withInventories imports constructors info =
        let spec = giSpec info
         in info{giSrc = (giSrc info){giImpVars = imports}, giSpec = spec{gsName = (gsName spec){gsDataConIds = constructors}}}
    withOwner :: (G.Var -> IO ()) -> IO ()
    withOwner action = do
        program <- compileToCore "DefaultSchema" "module DefaultSchema where\npoly :: (a -> a) -> a -> a\npoly f x = f x\n"
        case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == "poly"] of
            [owner] -> action owner
            _ -> assertFailure "expected one polymorphic callback source owner"
    comparePrefix info = comparePrefixWith info info
    comparePrefixWith base stage prepared (allow, start) = do
        let initial = (initCGI cfg base stage){CG.freshIndex = start}
            (expected, oldState) = runState (originalPrefix allow stage) initial
            (actual, newState) = runState (preparedPrefix allow prepared) initial
            rows (a, b, c) = [a, b, c]
        CG.freshIndex newState @?= CG.freshIndex oldState
        map (map (F.symbol . fst)) (rows actual) @?= map (map (F.symbol . fst)) (rows expected)
        map (map (F.showpp . snd)) (rows actual) @?= map (map (F.showpp . snd)) (rows expected)
        map (map (rTypeSort (CG.tyConEmbed initial) . snd)) (rows actual) @?= map (map (rTypeSort (CG.tyConEmbed initial) . snd)) (rows expected)
        assertBool "a native source telescope changed" $
            and [G.eqType (toType False actualType) (toType False expectedType) | (actualRows, expectedRows) <- zip (rows actual) (rows expected), ((_, actualType), (_, expectedType)) <- zip actualRows expectedRows]
    originalPrefix :: Bool -> TargetInfo -> CG.CG DefaultTypes
    originalPrefix allow info = do
        let imports = giImpVars (giSrc info)
            constructors = gsDataConIds (gsName (giSpec info))
            freshen :: [G.Var] -> CG.CG [(G.Var, SpecType)]
            freshen owners = forM owners $ \owner -> (\ty -> (owner, ty)) <$> CGFresh.trueTy allow (G.varType owner)
        a <- freshen imports
        b <- freshen constructors
        c <- freshen (filter G.isConLikeId imports)
        pure (a, b, c)
    preparedPrefix :: Bool -> DefaultTypes -> CG.CG DefaultTypes
    preparedPrefix allow (imports, constructors, conlike) = do
        let freshen :: [(G.Var, SpecType)] -> CG.CG [(G.Var, SpecType)]
            freshen = mapM (traverse (Fresh.true allow))
        a <- freshen imports
        b <- freshen constructors
        c <- freshen conlike
        pure (a, b, c)
