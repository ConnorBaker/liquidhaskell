{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module EmbeddingSortTests (tests) where

import Control.Monad.IO.Class (liftIO)
import Data.Binary qualified as B
import GHC qualified as G (Target (..), TargetId (..), depanal, getModSummary, parseModule)
import GHC.Data.Bag (unitBag)
import GHC.Core.Type qualified as G (mkAppTy)
import GHC.Driver.Session qualified as G (homeUnitId_)
import GHC.Paths (libdir)
import GHC.Tc.Types qualified as G (tcg_tcs)
import GHC.Types.Basic (ImportLevel (NormalLevel))
import GHC.Types.GREInfo (GREInfo (Vanilla))
import GHC.Types.Name (Name, mkExternalName, mkSystemName)
import GHC.Types.Name.Occurrence (mkTcOcc)
import GHC.Types.Name.Reader
import GHC.Types.PkgQual (PkgQual (NoPkgQual))
import GHC.Types.SrcLoc (noSrcSpan)
import GHC.Types.Unique (mkUnique)
import GHC.Unit.Module (mkModule, mkModuleName, moduleName)
import GHC.Unit.Types (stringToUnit)
import Language.Fixpoint.Types qualified as F
import Language.Fixpoint.SortCheck qualified as SortCheck
import Language.Haskell.Liquid.Bare.Resolve (makeLocalVars)
import Language.Haskell.Liquid.GHC.Misc ()
import Language.Haskell.Liquid.LHNameResolution (resolveEmbeddingSort, resolveLHNames)
import Language.Haskell.Liquid.Parse qualified as Parse
import Language.Haskell.Liquid.Types.Specs (Spec (embeds))
import Language.Haskell.Liquid.Types.RefType (interpretEmbedding, interpretEmbeddingSort, typeSort)
import Language.Haskell.Liquid.Types.Names
    ( lhNameToResolvedSymbol
    , getLHNameSymbol
    , makeGHCLHName
    , makeGHCLHNameLocated
    , makeGeneratedLogicLHName
    , makeLocalLHName
    , makeLogicLHName
    )
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import Language.Haskell.Syntax.ImpExp (IsBootInterface (NotBoot))
import Liquid.GHC.API qualified as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

tests :: TestTree
tests =
    testGroup "embedding sort origin" $
        testCase "parsed embedding keeps actual typechecked owner" sourceCheck
            : testCase "source aliases respect definitional equality before projection" sourceAliasCheck
            : testCase "constructor prefixes retain partial native application" sourcePrefixCheck
            : testCase "source embedding composition interprets aliases before publication" sourceEmbeddingCheck
            : map
                (uncurry check)
                [ ("unqualified source owner", normalize origin (atom "Evidence") == Right canonical)
                , ("qualified source owner", normalize origin (atom "BlobDeps.Evidence.Evidence") == Right canonical)
                , ("import alias retains owner", normalize aliasScope (atom "Alias.Evidence") == Right canonical)
                , ("repeated normalization", normalize origin canonical == Right canonical)
                , ("no source owner: custom carrier", normalize origin (atom "PrivateLogicalCarrier") == Right (atom "PrivateLogicalCarrier"))
                , ("same spelling follows existing source nominal namespace", normalize collisionScope (atom "PrivateLogicalCarrier") == Right (atom (F.symbol collisionOwner)))
                , ("qualified custom logical carrier without source owner", normalize origin (atom "Private.LogicalCarrier") == Right (atom "Private.LogicalCarrier"))
                , ("builtin set primitive", normalize shadowPrimitive (F.FTC F.setFTyCon) == Right (F.FTC F.setFTyCon))
                , ("bound and free coordinates", normalize origin coordinates == Right coordinates)
                , ("nested application", normalize origin applied == Right canonicalApplied)
                , ("function and abstraction", normalize origin (F.FAbs 8 (F.FFunc applied (F.FVar 8))) == Right (F.FAbs 8 (F.FFunc canonicalApplied (F.FVar 8))))
                , ("different package unit remains distinct", normalize otherOrigin (atom "Evidence") /= Right canonical)
                , ("ambiguous same-spelled units reject", rejects (normalize ambiguous (atom "Evidence")))
                , ("ambiguity does not become logical carrier", rejects (normalize ambiguous (atom "BlobDeps.Evidence.Evidence")))
                , ("precise import alias selects first unit", normalize twoAliases (atom "First.Evidence") == Right canonical)
                , ("precise import alias selects other unit", normalize twoAliases (atom "Second.Evidence") == Right otherCanonical)
                , ("numeric/string metadata preserved", sameBytes metadataObserved metadataExpected)
                , ("source locations preserved", sameLocation metadataObserved (F.symbol owner <$ sourceSpelling))
                , ("published binary roundtrip", roundtrip canonicalApplied)
                , ("published scope independence", normalize (mkGlobalRdrEnv []) canonicalApplied == Right canonicalApplied)
                , ("published carrier cannot be rebound by consumer scope", normalize otherOrigin canonicalApplied == Right canonicalApplied)
                , ("reflected logical identity is actual owner identity", project (makeLogicLHName "different authored spelling" originModule (Just owner)) == F.symbol owner)
                , ("reflected internal identity retains actual unique", project (makeLogicLHName "Evidence" originModule (Just internalOwner)) == F.symbol internalOwner)
                , ("authored logical identity retains origin unit", project (makeLogicLHName "measure" originModule Nothing) /= project (makeLogicLHName "measure" otherModule Nothing))
                , ("authored logical identity uses full origin module", project (makeLogicLHName "Evidence" originModule Nothing) == F.symbol owner)
                , ("local logical identity is unchanged", project (makeLocalLHName "local") == "local")
                , ("generated logical identity is unchanged", project (makeGeneratedLogicLHName "generated") == "generated")
                , ("display spelling is independent of source unit", display owner == "BlobDeps.Evidence.Evidence" && display owner == display otherOwner)
                , ("display equality does not collapse canonical identity", display owner == display otherOwner && project (F.val (makeGHCLHNameLocated owner)) /= project (F.val (makeGHCLHNameLocated otherOwner)))
                , ("explicit authored spelling is preserved", getLHNameSymbol (makeGHCLHName owner "Alias.Evidence") == "Alias.Evidence")
                ]
  where
    check label succeeded = testCase label (assertBool label succeeded)
    normalize = resolveEmbeddingSort
    owner = named 'a' "actual-package-a" "Evidence"
    project = lhNameToResolvedSymbol
    display = getLHNameSymbol . F.val . makeGHCLHNameLocated
    originModule = mkModule (stringToUnit "actual-package-a") (mkModuleName "BlobDeps.Evidence")
    otherModule = mkModule (stringToUnit "actual-package-b") (mkModuleName "BlobDeps.Evidence")
    internalOwner = mkSystemName (mkUnique 'i' 17) (mkTcOcc "Evidence")
    otherOwner = named 'b' "actual-package-b" "Evidence"
    collisionOwner = named 'd' "actual-package-a" "PrivateLogicalCarrier"
    collisionScope = mkGlobalRdrEnv [mkLocalGRE Vanilla NoParent collisionOwner]
    origin = mkGlobalRdrEnv [mkLocalGRE Vanilla NoParent owner]
    otherOrigin = mkGlobalRdrEnv [mkLocalGRE Vanilla NoParent otherOwner]
    ambiguous = mkGlobalRdrEnv [mkLocalGRE Vanilla NoParent owner, mkLocalGRE Vanilla NoParent otherOwner]
    aliasScope = mkGlobalRdrEnv [imported "Alias" owner]
    twoAliases = mkGlobalRdrEnv [imported "First" owner, imported "Second" otherOwner]
    shadowPrimitive = mkGlobalRdrEnv [mkLocalGRE Vanilla NoParent (named 'c' "actual-package-a" "Set_Set")]
    canonical = atom (F.symbol owner)
    otherCanonical = atom (F.symbol otherOwner)
    coordinates = F.FAbs 8 (F.FFunc (F.FVar 8) (F.FObj "free"))
    applied = F.FApp (F.FTC F.setFTyCon) (atom "BlobDeps.Evidence.Evidence")
    canonicalApplied = F.FApp (F.FTC F.setFTyCon) canonical
    sourceSpelling = F.atLoc (F.dummyPos "embedding-origin-source.hs") "Evidence"
    metadataHead = F.mappendFTC (F.symbolNumInfoFTyCon sourceSpelling True True) F.strFTyCon
    metadataInput = F.FTC metadataHead
    metadataExpected = Right (F.FTC (F.mappendFTC (F.symbolFTycon (F.symbol owner <$ F.fTyconSymbol metadataHead)) metadataHead))
    metadataObserved = normalize origin metadataInput

atom :: F.Symbol -> F.Sort
atom = F.FTC . F.symbolFTycon . F.dummyLoc

named :: Char -> String -> String -> Name
named tag unit occurrence =
    mkExternalName
        (mkUnique tag 1)
        (mkModule (stringToUnit unit) (mkModuleName "BlobDeps.Evidence"))
        (mkTcOcc occurrence)
        noSrcSpan

imported :: String -> Name -> GlobalRdrElt
imported alias owner =
    (mkLocalGRE Vanilla NoParent owner)
        { gre_lcl = False
        , gre_imp = unitBag (ImpSpec (ImpDeclSpec defining (mkModuleName alias) NoPkgQual True noSrcSpan NotBoot NormalLevel) ImpAll)
        }
  where
    defining = mkModule (stringToUnit (if alias == "Second" then "actual-package-b" else "actual-package-a")) (mkModuleName "BlobDeps.Evidence")

rejects :: Either a b -> Bool
rejects (Left _) = True
rejects (Right _) = False

constructor :: Either a F.Sort -> Maybe F.FTycon
constructor (Right (F.FTC c)) = Just c
constructor _ = Nothing

sameLocation :: Either a F.Sort -> F.LocSymbol -> Bool
sameLocation observed expected = case constructor observed of
    Just actual -> B.encode (F.fTyconSymbol actual) == B.encode expected
    Nothing -> False

sameBytes :: Either a F.Sort -> Either a F.Sort -> Bool
sameBytes (Right x) (Right y) = B.encode x == B.encode y
sameBytes _ _ = False

roundtrip :: F.Sort -> Bool
roundtrip original = case B.decodeOrFail (B.encode original) of
    Right (remaining, _, restored) -> remaining == mempty && restored == original
    Left _ -> False

sourceCheck :: IO ()
sourceCheck = withSourceOwner $ \environment -> do
    embedding <- case Parse.singleSpecP (F.dummyPos "embedding control") "embed Provenance as (Set_Set EmbeddingOwner.Evidence)" of
        Right (Parse.Embed (owner, meaning, arguments)) -> pure (owner, (meaning, arguments))
        _ -> fail "embedding control did not parse"
    let result =
            resolveLHNames
                defConfig
                (G.tcg_mod environment)
                (makeLocalVars [] [])
                (G.imp_mods (G.tcg_imports environment))
                (G.tcg_rdr_env environment)
                mempty{embeds = F.tceFromList [embedding]}
                mempty
        expectedOwner = case lookupGRE (G.tcg_rdr_env environment) (LookupOccName (mkTcOcc "Evidence") SameNameSpace) of
            [entry] -> F.symbol (greName entry)
            _ -> "missing actual typechecked owner"
    liftIO $ case result of
        Right (resolved, _, _)
            | [(_, (F.FApp (F.FTC primitive) (F.FTC actual), _))] <- F.tceToList (embeds resolved)
            , (_, (F.FApp _ (F.FTC parsed), _)) <- embedding
            , F.val (F.fTyconSymbol parsed) /= expectedOwner
            , primitive == F.setFTyCon
            , F.val (F.fTyconSymbol actual) == expectedOwner ->
                pure ()
        _ -> fail "parsed embedding did not retain actual typechecked owner"

sourcePrefixCheck :: IO ()
sourcePrefixCheck = do
    let catalog = F.tceInsert G.listTyCon (F.FTC F.setFTyCon) F.NoArgs mempty
        partial = G.mkTyConApp G.listTyCon []
        applied = G.mkAppTy partial G.boolTy
        saturated = G.mkTyConApp G.listTyCon [G.boolTy]
    assertBool "a constructor prefix was prematurely saturated" (typeSort catalog partial == F.FTC F.setFTyCon)
    assertBool "native application changed the constructor's meaning" (G.eqType applied saturated && typeSort catalog applied == typeSort catalog saturated)
    assertBool "native application did not apply the logical prefix" (typeSort catalog applied == F.FApp (F.FTC F.setFTyCon) (typeSort catalog G.boolTy))

sourceAliasCheck :: IO ()
sourceAliasCheck = withSourceOwner $ \environment -> do
    let findConstructor occurrence = case [c | c <- G.tcg_tcs environment, G.getOccString c == occurrence] of
            [constructor] -> pure constructor
            _ -> fail ("missing typechecked constructor: " ++ occurrence)
    evidence <- findConstructor "Evidence"
    alias <- findConstructor "EvidenceAlias"
    container <- findConstructor "ContainerAlias"
    let value = G.mkTyConApp alias []
        nested = G.mkTyConApp container [value]
        embedded = F.tceInsert evidence F.FInt F.NoArgs mempty
    liftIO $ mapM_ (check value nested) [mempty, embedded]
  where
    check value nested catalog = mapM_ agrees [value, nested]
      where
        agrees source = do
            let expanded = G.expandTypeSynonyms source
            assertBool "fixture did not retain source definitional equality" (G.eqType source expanded)
            assertBool "equivalent native types projected different meanings" (typeSort catalog source == typeSort catalog expanded)

sourceEmbeddingCheck :: IO ()
sourceEmbeddingCheck = withSourceOwner $ \environment -> do
    let findConstructor occurrence = case [c | c <- G.tcg_tcs environment, G.getOccString c == occurrence] of
            [constructor] -> pure constructor
            _ -> fail ("missing typechecked constructor: " ++ occurrence)
    evidence <- findConstructor "Evidence"
    alias <- findConstructor "EvidenceAlias"
    container <- findConstructor "ContainerAlias"
    nonPrefix <- findConstructor "NonPrefixAlias"
    repeated <- findConstructor "RepeatedAlias"
    identityAlias <- findConstructor "IdentityAlias"
    constantAlias <- findConstructor "ConstantAlias"
    actionA <- findConstructor "ActionA"
    actionB <- findConstructor "ActionB"
    let findCoordinate constructor = case G.tyConTyVars constructor of
            [formal] -> pure (F.FObj (F.symbol formal))
            _ -> fail "action fixture is not unary"
    coordinateA <- findCoordinate actionA
    coordinateB <- findCoordinate actionB
    set <- case G.splitTyConApp_maybe (G.expandTypeSynonyms (G.mkTyConApp container [G.mkTyConApp evidence []])) of
        Just (constructor, _) -> pure constructor
        _ -> fail "container alias did not retain its actual native constructor"
    let owners spelling = case [constructor | constructor <- [evidence, alias, container, nonPrefix, repeated, identityAlias, constantAlias, actionA, actionB, set, G.listTyCon], F.symbol constructor == spelling] of
            [constructor] -> Just constructor
            _ -> Nothing
        source constructor = atom (F.symbol constructor)
        catalog = F.tceInsert evidence F.FInt F.NoArgs $ F.tceInsert set (F.FTC F.setFTyCon) F.NoArgs mempty
        interpret = interpretEmbeddingSort owners
        canonical = source evidence
        identity = F.tceInsert evidence canonical F.NoArgs mempty
        expansive = F.tceInsert evidence (F.FApp (F.FTC F.setFTyCon) canonical) F.NoArgs mempty
        numericMeaning = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc (F.symbol evidence)) True True)
        numeric = F.tceInsert evidence numericMeaning F.NoArgs mempty
        located = F.atLoc (F.dummyPos "authored-embedding.hs") (F.symbol evidence)
        decorated = F.FTC (F.mappendFTC (F.symbolNumInfoFTyCon located True True) F.strFTyCon)
        logicalCarrier = F.symbolFTycon (F.dummyLoc "PrivateLogicalCarrier")
        destination = F.mappendFTC (F.symbolFTycon ("PrivateLogicalCarrier" <$ located)) (F.mappendFTC (F.symbolNumInfoFTyCon located True True) F.strFTyCon)
        redirected = F.tceInsert evidence (F.FTC logicalCarrier) F.NoArgs mempty
        -- These aliases are poly-kinded: source elaboration supplies the
        -- invisible kind argument before the visible Evidence argument.
        aliasArguments = [G.liftedTypeKind, G.mkTyConApp evidence []]
        aliasInput = F.fApp (source identityAlias) (typeSort mempty <$> aliasArguments)
        identityPrefix = F.FApp (source identityAlias) (typeSort mempty G.liftedTypeKind)
        nativeIdentityPrefix = G.mkTyConApp identityAlias [G.liftedTypeKind]
        discardedInput = F.fApp (source constantAlias) (typeSort mempty <$> aliasArguments)
        aliasIdentity = F.tceInsert evidence aliasInput F.NoArgs mempty
        actionInput = F.FApp (source actionA) canonical
        directAction = F.tceInsert actionA (F.FApp (source actionA) coordinateA) F.WithArgs mempty
        composedIdentity = F.tceInsert actionA (F.FApp (source actionA) (F.FApp (source actionB) coordinateA)) F.WithArgs $
            F.tceInsert actionB coordinateB F.WithArgs mempty
        returnedIdentity = F.tceInsert actionA (F.FApp (source actionB) (F.FApp (source actionA) coordinateA)) F.WithArgs $
            F.tceInsert actionB coordinateB F.WithArgs mempty
        expansiveAction = F.tceInsert actionA (F.FApp (source actionA) (F.FApp (F.FTC F.setFTyCon) coordinateA)) F.WithArgs mempty
        mutualActions = F.tceInsert actionA (F.FApp (source actionB) coordinateA) F.WithArgs $
            F.tceInsert actionB (F.FApp (source actionA) coordinateB) F.WithArgs mempty
        constantAction = F.tceInsert actionB F.FInt F.WithArgs expansive
        projectedAction = F.tceInsert actionB coordinateB F.WithArgs mempty
        locatedAction = F.atLoc (F.dummyPos "authored-action.hs") (F.symbol actionB)
        decoratedAction = F.mappendFTC (F.symbolNumInfoFTyCon locatedAction True True) F.strFTyCon
        projectedDestination = F.mappendFTC (F.symbolFTycon ("PrivateLogicalCarrier" <$ locatedAction)) decoratedAction
        theoryCarriers = [F.FApp (F.FTC F.setFTyCon) F.FInt, F.FApp (F.FApp (F.FTC F.mapFTyCon) F.FInt) F.FInt]
        prefixCatalog = F.tceInsert G.listTyCon (F.FTC F.setFTyCon) F.NoArgs mempty
        decoratedPrefix = F.FTC (F.symbolNumInfoFTyCon (F.atLoc (F.dummyPos "authored-prefix.hs") (F.symbol G.listTyCon)) True True)
    liftIO $ do
        assertBool "closed source alias did not compose its embedding" (interpret catalog (source alias) == Right F.FInt)
        assertBool "source alias application lost its embedded argument" (interpret catalog (F.FApp (source container) (source alias)) == Right (F.FApp (F.FTC F.setFTyCon) F.FInt))
        assertBool "logical Set carrier did not compose source Evidence embedding" (interpret catalog (F.FApp (F.FTC F.setFTyCon) canonical) == Right (F.FApp (F.FTC F.setFTyCon) F.FInt))
        assertBool "identity embedding was mistaken for expansive recursion" (interpret identity canonical == Right canonical)
        assertBool "poly-kinded identity fixture was not definitionally identity" (G.eqType (G.mkTyConApp identityAlias aliasArguments) (G.mkTyConApp evidence []))
        assertBool "partial poly-kinded constructor was mistaken for a recursive value" (interpret mempty identityPrefix == Right identityPrefix)
        assertBool "later native application changed the poly-kinded action" (G.eqType (G.mkAppTy nativeIdentityPrefix (G.mkTyConApp evidence [])) (G.mkTyConApp identityAlias aliasArguments))
        assertBool "later logical application failed to compose the retained native action" (interpret mempty (F.FApp identityPrefix canonical) == Right canonical)
        assertBool "source definitional identity was mistaken for recursion" (interpret aliasIdentity canonical == Right canonical)
        assertBool "poly-kinded constant fixture did not discard its operand" (G.eqType (G.mkTyConApp constantAlias aliasArguments) G.boolTy)
        assertBool "an alias evaluated an argument it discards" (interpret expansive discardedInput == Right (typeSort mempty G.boolTy))
        assertBool "a constant constructor action evaluated an argument it discards" (interpret constantAction (F.FApp (source actionB) canonical) == Right F.FInt)
        assertBool "formal projection discarded source carrier annotations" (sameBytes (interpret projectedAction (F.FApp (F.FTC decoratedAction) (F.FTC logicalCarrier))) (Right (F.FTC projectedDestination)))
        mapM_ (preservesTheoryRole interpret evidence decorated located) theoryCarriers
        assertBool "partial constructor prefix acquired a scalar numeric role" $ case interpret prefixCatalog decoratedPrefix of
            Right prefix -> not (F.isNumeric prefix) && rejectsNumericComparison prefix && rejectsNumericComparison (F.FApp prefix F.FInt)
            Left _ -> False
        assertBool "constructor action composition did not expose identity" (interpret composedIdentity actionInput == Right actionInput)
        assertBool "generic direct identity was mistaken for recursion" (interpret directAction actionInput == Right actionInput)
        assertBool "constructor action reinterpreted its already-interpreted operand" (interpret returnedIdentity actionInput == Right actionInput)
        assertBool "residual expansive constructor action was accepted" (rejects (interpret expansiveAction actionInput))
        assertBool "mutual constructor action recursion was accepted" (rejects (interpret mutualActions actionInput))
        assertBool "mutual constructor action recursion depended on the starting owner" (rejects (interpret mutualActions (F.FApp (source actionB) canonical)))
        assertBool "nominal equality discarded registered carrier metadata" (sameBytes (interpret numeric canonical) (Right numericMeaning))
        assertBool "carrier rewriting discarded source position or metadata" (sameBytes (interpret redirected decorated) (Right (F.FTC destination)))
        assertBool "expansive embedding recursion was accepted" (rejects (interpret expansive canonical))
        assertBool "source alias prefix was interpreted before native application" (interpretEmbedding owners catalog G.listTyCon (source container, F.NoArgs) == Right (F.FTC F.setFTyCon, F.NoArgs))
        mapM_ (retainsAction owners catalog source) [nonPrefix, repeated]
  where
    rejectsNumericComparison carrier = rejects $ SortCheck.sortExprE Nothing F.dummySpan (F.fromListSEnv [("carrier", carrier)]) mempty (F.PAtom F.Lt (F.EVar "carrier") (F.ECon (F.I 0)))
    preservesTheoryRole interpret evidence decorated located meaning = do
        let result = interpret (F.tceInsert evidence meaning F.NoArgs mempty) decorated
        assertBool "plain theory carrier unexpectedly admitted scalar comparison" (rejectsNumericComparison meaning)
        assertBool "source role transport admitted scalar comparison on a theory carrier" $ case result of
            Right carrier -> rejectsNumericComparison carrier
            Left _ -> False
        assertBool "source numeric role leaked onto a compound theory carrier" $ case result of
            Right carrier -> not (F.isNumeric carrier) && not (F.isReal carrier) && not (F.isString carrier)
            Left _ -> False
        assertBool "compound theory carrier lost the authored origin span" $ case result of
            Right carrier | F.FTC constructor : _ <- F.unFApp carrier -> F.loc (F.fTyconSymbol constructor) == F.loc located
            _ -> False
    retainsAction owners catalog source alias = do
        let formals = G.tyConTyVars G.listTyCon
            generic = G.mkTyConApp alias (G.mkTyVarTy <$> formals)
            expected = typeSort catalog generic
        assertBool "a non-prefix constructor action was mistaken for a constant prefix" (interpretEmbedding owners catalog G.listTyCon (source alias, F.NoArgs) == Right (expected, F.WithArgs))

withSourceOwner :: (G.TcGblEnv -> G.Ghc ()) -> IO ()
withSourceOwner action = G.runGhc (Just libdir) $ do
    flags <- G.getSessionDynFlags
    _ <- G.setSessionDynFlags flags{G.backend = G.interpreterBackend}
    G.setTargets
        [ G.Target
            (G.TargetFile "ghc-api-tests/fixtures/EmbeddingOwner.hs" Nothing)
            False
            (G.homeUnitId_ flags)
            Nothing
        ]
    _ <- G.depanal [] False
    summary <- G.getModSummary (mkModule G.mainUnit (mkModuleName "EmbeddingOwner"))
    checked <- G.parseModule summary >>= G.typecheckModule
    let (environment, _) = G.tm_internals_ checked
    action environment
