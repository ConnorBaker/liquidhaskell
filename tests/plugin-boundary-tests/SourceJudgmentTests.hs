module SourceJudgmentTests (tests) where

import CompilerFixture
import Control.Monad (when)
import DeclaredAliasFixtures (declaredAlias)
import QueryAssertions (assertUnmentionedEvidenceHidden, assertDefaultInterfaces, assertExternalFormationTag, assertJointInferenceCheck, assertSingleSourceCheck, compatibilityObligations)
import SourceVariantFixtures (copySourceFixture)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "source judgments"
        $ [ testGroup
                category
                [ sourceCase category flags name expected
                | (name, expected) <- cases
                ]
          | (category, flags, cases) <- groups
          ]
            ++ [ checkedInterfaces ObjectCode "type-literal interfaces" "lh-type-literal" "type-literals" "LiteralProducer" [] [("LiteralClient", Safe), ("LiteralClientFalse", UnsafeAt [9])]
               , checkedInterfaces ObjectCode "authored-assumption interfaces" "lh-assumption-interface" "assumed-predicates" "AssumptionProducer" ["--adt"] [("AssumptionClient", Safe), ("AssumptionClientBad", UnsafeAt [8])]
               , checkedInterfaces ObjectCode "logical-measure interfaces" "lh-logical-interface" "assumed-predicates" "LogicalCarrierGood" ["--adt"] [("LogicalCarrierClient", Safe), ("LogicalCarrierClientFalse", UnsafeAt [7, 11])]
               , checkedInterfaces ObjectCode "local map laws and imported counterclaim" "lh-map-composition" "map-composition" "MapCompositionLaws" ["--adt"] [("MapCompositionFalse", UnsafeAt [9])]
               , checkedInterfaces ObjectCode "imported opaque identity, explicit trust, and counterclaim" "lh-opaque-interface" "opaque-reflection" "OpaqueProducer" [] [("OpaqueClient", Safe), ("OpaqueClientAssumed", Safe), ("OpaqueClientFalse", UnsafeAt [8])]
               , checkedInterfaces ObjectCode "imported first-order measure selectors" "lh-selector-interface" "callback-projections" "SelectorProducer" [] [("SelectorClientGood", Safe), ("SelectorClientFalse", UnsafeAt [8])]
               , checkedInterfaces ObjectCode "imported higher-order callback selectors" "lh-callback-interface" "callback-projections" "CallbackProducer" [] [("CallbackClientGood", Safe), ("CallbackClientFalse", UnsafeAt [13])]
               , checkedInterfaces InterfaceOnly "interface-only higher-order callback publication" "lh-callback-interface-only" "callback-projections" "CallbackProducer" [] [("CallbackClientGood", Safe), ("CallbackClientFalse", UnsafeAt [13])]
               , testCase "home assumption precedes an imported non-home assumption" $ withSystemTempDirectory "lh-home-assumption" $ \directory -> do
                    tool <- compiler
                    let fixtures = "plugin-boundary-tests/fixtures/assumed-predicates"
                        alpha = directory </> "alpha"
                        zeta = directory </> "zeta"
                        objects = [alpha </> "objects", zeta </> "objects"]
                    copyFixture fixture (fixtures </> "HomeAssumptionAlpha.hs") alpha "HomeAssumptionAlpha"
                    _ <- compile tool Strict optimization ObjectCode alpha "HomeAssumptionAlpha" [] [] Safe
                    copyFixture fixture (fixtures </> "HomeAssumptionZeta.hs") zeta "HomeAssumptionZeta"
                    _ <- compile tool Strict optimization ObjectCode zeta "HomeAssumptionZeta" [alpha </> "objects"] [] Safe
                    mapM_
                        ( \(name, expected) -> do
                            let target = directory </> name
                            copyFixture fixture (fixtures </> name ++ ".hs") target name
                            compile tool Strict optimization ObjectCode target name objects [] expected
                        )
                        [("HomeAssumptionClientGood", Safe), ("HomeAssumptionClientBad", UnsafeAt [8])]
               , constructorInterfaces
               , importedInstanceInterfaces
               , naturalSourceGraphs
               , guardedImageInterfaces
               , testGroup
                    "checked imported measure staging"
                    [ sourceInterfaces
                        "authored Word8 model uses scoped constructor equations without PLE"
                        "ScopedAsciiProducer"
                        scopedAsciiProducer
                        [ ("ScopedAsciiGood", scopedAsciiClient "ScopedAsciiGood" "asciiModel r", Safe)
                        , ("ScopedAsciiFalse", scopedAsciiClient "ScopedAsciiFalse" "not (asciiModel r)", UnsafeAt [7])
                        , ("ScopedAsciiInt", scopedAsciiIsolation "ScopedAsciiInt" "Int", UnsafeAt [6, 7])
                        , ("ScopedAsciiGeneric", scopedAsciiIsolation "ScopedAsciiGeneric" "a", UnsafeAt [6, 7])
                        , ("ScopedAsciiIntUse", scopedAsciiNativeUse "ScopedAsciiIntUse" "Int", FormationRefusal 5 "GHC-83865")
                        , ("ScopedAsciiGenericUse", scopedAsciiNativeUse "ScopedAsciiGenericUse" "a", FormationRefusal 5 "Cannot unify")
                        ]
                    , sourceInterfaces
                        "specialized authored input membership guards scoped equations"
                        "ScopedNarrowProducer"
                        scopedNarrowProducer
                        [ ("ScopedNarrowGood", scopedNarrowClient "ScopedNarrowGood" "one byte", Safe)
                        , ("ScopedNarrowFalse", scopedNarrowClient "ScopedNarrowFalse" "[]", UnsafeAt [7])
                        ]
                    , testCase "source model use retains its narrowed input membership obligation" $
                        withSystemTempDirectory "lh-scoped-domain-refusal" $ \directory -> do
                            tool <- compiler
                            let name = "ScopedNarrowOutside"
                            writeFixture name directory name (scopedNarrowSource name "oneModel r")
                            _ <- compile tool Strict optimization ObjectCode directory name [] ["--higherorder"] (UnsafeAt [6])
                            pure ()
                    , sourceInterfaces
                        "concrete list equations retain their input domain"
                        "ImportedByteProducer"
                        importedByteProducer
                        [ ("ImportedByteBound", importedByteClient "ImportedByteBound" "{w:Word8 | w <= 127}" "[w]", Safe)
                        , ("ImportedByteBad", importedByteClient "ImportedByteBad" "Word8" "[w]", UnsafeAt [8])
                        , ("ImportedByteWitness", importedByteClient "ImportedByteWitness" "Word8" "if w <= 127 then [w] else []", Safe)
                        ]
                    , sourceInterfaces
                        "lifted data-family equations preserve nested source indices"
                        "LiftedFamilyProducer"
                        liftedFamilyProducer
                        [ ("LiftedFamilyResultGood", liftedFamilyResultClient "LiftedFamilyResultGood" "n", Safe)
                        , ("LiftedFamilyResultBad", liftedFamilyResultClient "LiftedFamilyResultBad" "n + 1", UnsafeAt [7])
                        , ("LiftedFamilyGood", liftedFamilyClient "LiftedFamilyGood" "==", Safe)
                        , ("LiftedFamilyBad", liftedFamilyClient "LiftedFamilyBad" "/=", UnsafeAt [7])
                        , ("LiftedFamilyWrongIndex", liftedFamilyWrongIndex, FormationRefusal 5 "Cannot unify bool with Char")
                        ]
                    , testCase "ordinary newtype casts cannot select a different measure carrier" $
                        withSystemTempDirectory "lh-measure-newtype-cast" $ \directory -> do
                            tool <- compiler
                            let name = "MeasureNewtypeCast"
                            writeFixture name directory name measureNewtypeCast
                            _ <- compile tool Strict optimization ObjectCode directory name [] ["--higherorder"] (FormationRefusal 9 "Case scrutinee is not the selected measure argument")
                            pure ()
                    , sourceInterfaces
                        "deferred lifted wildcard cannot erase an authored constructor"
                        "ImportedBoolProducer"
                        importedBoolProducer
                        [("ImportedMeasureCollision", importedMeasureCollision, FormationRefusal 6 "Illegal type specification")]
                    ]
               , instanceFormation
               , testGroup
                    "higher-kinded predicate scope"
                    [ testGroup
                        mode
                        [ sourceCase "callback-projections" flags "HigherKindedPredicateGood" Safe
                        , sourceCase "callback-projections" flags "HigherKindedPredicateFalse" (UnsafeAt [8])
                        , sourceCase "callback-projections" flags "HigherKindedPredicateCapability" Safe
                        , sourceCase "callback-projections" flags "PredicateOverapplicationBad" (FormationRefusal 7 "expects at most 1 arguments, but is given 2")
                        ]
                    | (mode, flags) <- [("default", []), ("typeclass", ["--typeclass"])]
                    ]
               , testGroup
                    "authored class field formation"
                    [ sourceCase "instance-formation" [] "ClassMethodScopeGood" Safe
                    , sourceCase "instance-formation" [] "ClassMethodWrongCarrier" (FormationRefusal 6 "source constructor contract does not match GHC carrier")
                    ]
               , testGroup
                    "native datatype carrier configuration"
                    [ testGroup "erased" [sourceCase "native-relations" [] "NativeCarrierDatatypeFormation" Safe]
                    , testGroup "native" [sourceCase "native-relations" ["--adt"] "NativeCarrierDatatypeFormation" (FormationRefusal 6 "Invalid Relation")]
                    ]
               , sourceCase "inferred-interface" ["--no-true-types"] "DefaultDomain" Safe
               , testGroup
                    "shared evidence scope"
                    [ sourceCase "shared-evidence" [] "SharedEvidenceScopeGood" Safe
                    , sourceCase "shared-evidence" [] "SharedEvidenceScopeFalse" (UnsafeAt [16, 21])
                    ]
               , testGroup
                    "instance-owned evidence"
                    [ sourceCase "shared-evidence" [] "SharedEvidenceNewtypeGood" Safe
                    , sourceCase "shared-evidence" [] "SharedEvidenceNewtypeNFDataGood" Safe
                    , sourceCase "shared-evidence" [] "SharedEvidenceViaGood" Safe
                    , sourceCase "shared-evidence" [] "SharedEvidenceNewtypeFalse" (UnsafeAt [10])
                    ]
               , testGroup
                    "represented value contracts"
                    [ sourceCase "represented-contracts" ["--higherorder"] "CallbackRootGood" Safe
                    , sourceCase "represented-contracts" ["--higherorder"] "CallbackRootBad" (UnsafeAt [3])
                    , sourceCase "represented-contracts" ["--higherorder"] "CallbackBoxGood" Safe
                    , sourceCase "represented-contracts" ["--higherorder"] "CallbackBoxBad" (UnsafeAt [7])
                    ]
               , testGroup
                    "totality policy configuration"
                    [ sourceCase "totality-policy" ["--higherorder", "--no-totality"] "TotalityErrorNoPrelude" (UnsafeAt [9])
                    , testCase "missing installed policy" $ withSystemTempDirectory "lh-missing-policy" $ \directory -> do
                        tool <- compiler
                        let name = "TotalityErrorNoPrelude"
                        copyFixture fixture ("plugin-boundary-tests/fixtures/totality-policy" </> name ++ ".hs") directory name
                        assertMissingTotalityPolicy tool optimization directory name
                    ]
               ]
  where
    sourceCase category flags name expected =
        testCase name $ withSystemTempDirectory "lh-source-judgment" $ \directory -> do
            tool <- compiler
            let relative = "plugin-boundary-tests/fixtures" </> category </> name ++ ".hs"
            if category == "declared-alias"
                then writeFixture relative directory name (declaredAlias name (if name == "DeclaredAliasGood" then "==" else "/="))
                else copySourceFixture fixture relative directory name
            compiled <- compile tool Strict optimization ObjectCode directory name [] flags expected
            when (name == "ForeignAssumptionBad") (assertExternalFormationTag compiled)
            when (name == "IgnoredNestedGood") (assertSingleSourceCheck compiled)
            when (name `elem` ["InferredFunctionGood", "InferredHoleGood"]) (assertJointInferenceCheck compiled)
            when (name == "DerivedDefaultGood") (assertDefaultInterfaces compiled)
            when (name == "SharedEvidenceScopeGood") (assertUnmentionedEvidenceHidden compiled)
    instanceFormation =
        testGroup
            "instance formation"
            [ testGroup
                mode
                [ sourceCase "instance-formation" flags name expected
                | (name, expected) <-
                    [ ("InstanceFormationGood", Safe)
                    , ("InstanceFormationBad", UnsafeAt [15])
                    , ("InstanceCarrierGood", Safe)
                    , ("InstancePlainCarrierGood", Safe)
                    , ("InstancePlainCarrierBad", UnsafeAt [16])
                    , ("InstanceCarrierDuplicateBad", FormationRefusal 6 "Multiple specifications for")
                    , ("InstanceCarrierBodyBad", UnsafeAt [12])
                    , ("InstanceCarrierGenericBad", UnsafeAt [23])
                    , ("InstanceResultGood", Safe)
                    , ("EqualityInstanceGood", Safe)
                    , ("EqualityInstanceBad", UnsafeAt [7])
                    ]
                ]
            | (mode, flags) <- [("default", []), ("typeclass", ["--typeclass"])]
            ]
    -- A class method named in a refinement. Without --typeclass, name
    -- resolution rejects it as upstream does, at the refinement's line.
    -- With --typeclass, the method at a known instance means that instance's
    -- contract, and at an abstract dictionary it is uninterpreted.
    methodQueries mode = case mode of
        "default" ->
            [ (name, FormationRefusal owner "This is a class method, but typeclass support is disabled.")
            | (name, owner) <-
                [ ("ImportedInstanceQueryOnlyGood", 11)
                , ("ImportedInstanceQueryOnlyBad", 11)
                , ("ImportedInstanceQueryClaimBad", 11)
                , ("ImportedAbstractMethodGood", 9)
                , ("ImportedAbstractMethodBad", 9)
                ]
            ]
        _ ->
            [ ("ImportedInstanceQueryOnlyGood", Safe)
            , ("ImportedInstanceQueryOnlyBad", UnsafeAt [13])
            , ("ImportedInstanceQueryClaimBad", UnsafeAt [13])
            , ("ImportedAbstractMethodGood", Safe)
            , ("ImportedAbstractMethodBad", UnsafeAt [11])
            ]
    checkedInterfaces backend label prefix category name flags cases =
        testCase label $ withSystemTempDirectory prefix $ \directory -> do
            tool <- compiler
            let producerDirectory = directory </> "producer"
                fixtures = "plugin-boundary-tests/fixtures" </> category
            copyFixture fixture (fixtures </> name ++ ".hs") producerDirectory name
            producer <- compile tool Strict optimization backend producerDirectory name [] flags Safe
            assertPublication tool producer True
            mapM_ (client tool directory fixtures producerDirectory flags) cases
    importedInstanceInterfaces =
        testGroup
            "imported instance domains"
            [ testGroup
                mode
                [ checkedInterfaces ObjectCode "checked dictionary publication" "lh-checked-instance" "instance-formation" "CheckedCarrier" flags [("CheckedCarrierGood", Safe), ("CheckedCarrierBad", UnsafeAt [10])]
                , sourceCase "instance-formation" flags "OwnedInstanceBad" (UnsafeAt [11])
                , -- The declaring module checks its instance against the class.
                  -- An importer, with or without the implicit Prelude's trusted
                  -- assumption instances, uses that result and never re-proves it.
                  testCase "instance compatibility belongs to its declaring module" $ withSystemTempDirectory "lh-instance-owner" $ \directory -> do
                    tool <- compiler
                    let producerDirectory = directory </> "producer"
                        fixtures = "plugin-boundary-tests/fixtures/instance-formation"
                    copyFixture fixture (fixtures </> "OwnedInstanceGood.hs") producerDirectory "OwnedInstanceGood"
                    producer <- compile tool Strict optimization ObjectCode producerDirectory "OwnedInstanceGood" [] flags Safe
                    owned <- compatibilityObligations producer
                    assertBool "the declaring module did not check its instance against the class" (owned > 0)
                    mapM_
                        ( \name -> do
                            compiled <- client tool directory fixtures producerDirectory flags (name, Safe)
                            imported <- compatibilityObligations compiled
                            imported @?= 0
                        )
                        ["OwnedInstanceClient", "OwnedInstancePreludeClient"]
                , testCase "assumed dictionary admission" $ withSystemTempDirectory "lh-imported-instance" $ \directory -> do
                    tool <- compiler
                    let producerDirectory = directory </> "producer"
                        fixtures = "plugin-boundary-tests/fixtures/instance-formation"
                    copyFixture fixture (fixtures </> "ImportedCarrier.hs") producerDirectory "ImportedCarrier"
                    _ <- compileHaskell tool optimization producerDirectory "ImportedCarrier" []
                    mapM_
                        (client tool directory fixtures producerDirectory flags)
                        ([("ImportedInstanceCarrierGood", Safe), ("ImportedInstanceCarrierGenericBad", UnsafeAt [13]), ("ImportedInstanceCarrierMethodBad", UnsafeAt [6, 9]), ("ImportedInstanceResultGood", Safe), ("ImportedInstancePredicateGood", Safe), ("ImportedInstancePredicateNarrowBad", UnsafeAt [10, 14]), ("ImportedInstancePredicateResultBad", UnsafeAt [14, 17])] ++ methodQueries mode)
                , testCase "nested predicate callback admission" $ withSystemTempDirectory "lh-imported-callback-instance" $ \directory -> do
                    tool <- compiler
                    let producerDirectory = directory </> "producer"
                        fixtures = "plugin-boundary-tests/fixtures/instance-formation"
                    copyFixture fixture (fixtures </> "ImportedCallbackCarrier.hs") producerDirectory "ImportedCallbackCarrier"
                    _ <- compileHaskell tool optimization producerDirectory "ImportedCallbackCarrier" []
                    mapM_
                        (client tool directory fixtures producerDirectory flags)
                        [("ImportedInstanceCallbackWideGood", Safe), ("ImportedInstanceCallbackRestrictedBad", UnsafeAt [15])]
                ]
            | (mode, flags) <- [("default", []), ("typeclass", ["--typeclass"])]
            ]
    naturalSourceGraphs =
        testGroup
            "native source-call graphs"
            [ testGroup
                mode
                [ checkedInterfaces ObjectCode "checked native unit and worker application" "lh-native-source-graph" "natural-source-graphs" "NaturalUnitProducer" flags [("NaturalUnitWorkerGood", Safe)]
                , sourceCase "natural-source-graphs" flags "NaturalUnitFalseRawDividendBad" (UnsafeAt [11])
                , sourceCase "natural-source-graphs" flags "NaturalUnitWorkerBad" (UnsafeAt [8])
                ]
            | (mode, flags) <- [("default", []), ("typeclass", ["--typeclass"])]
            ]
    guardedImageInterfaces =
        testGroup
            "source-call nominal carrier boundary"
            [ checkedInterfaces ObjectCode mode "lh-guarded-image" "guarded-source-graphs" "GuardedImageProducer" flags [("GuardedImageBad", UnsafeAt [16])]
            | (mode, flags) <- [("default", []), ("typeclass", ["--typeclass"])]
            ]
    sourceInterfaces label name source cases =
        testCase label $ withSystemTempDirectory "lh-measure-staging" $ \directory -> do
            tool <- compiler
            let provider = directory </> "producer"
                flags = ["--higherorder"]
            writeFixture label provider name source
            checked <- compile tool Strict optimization ObjectCode provider name [] flags Safe
            assertPublication tool checked True
            mapM_
                ( \(clientName, body, expected) -> do
                    let target = directory </> clientName
                    writeFixture label target clientName body
                    _ <- compile tool Strict optimization ObjectCode target clientName [provider </> "objects"] flags expected
                    pure ()
                )
                cases
    constructorInterfaces =
        testGroup
            "ordinary imported constructors"
            [ testCase label $ withSystemTempDirectory "lh-imported-constructor" $ \directory -> do
                tool <- compiler
                let producerDirectory = directory </> "producer"
                    fixtures = "plugin-boundary-tests/fixtures/imported-newtypes"
                copyFixture fixture (fixtures </> producer ++ ".hs") producerDirectory producer
                _ <- compileHaskell tool optimization producerDirectory producer []
                mapM_ (client tool directory fixtures producerDirectory flags) cases
            | (label, producer, flags, cases) <-
                [
                    ( "unused unpacked sibling"
                    , "ImportedConstructors"
                    , ["--adt"]
                    , [("ImportedConstructorClient", Safe), ("ImportedConstructorFalse", UnsafeAt [7])]
                    )
                ,
                    ( "declaration-only unpacked constructor"
                    , "ImportedConstructors"
                    , ["--adt"]
                    , [("ImportedDeclaredConstructorGood", Safe), ("ImportedDeclaredConstructorFalse", UnsafeAt [13]), ("ImportedDeclaredConstructorWrongCarrier", FormationRefusal 5 "Data constructors in refinement do not match original datatype")]
                    )
                ,
                    ( "source scalar domains and result share unpacked reconstruction"
                    , "ImportedConstructors"
                    , ["--adt"]
                    , [("ImportedScalarContractGood", Safe), ("ImportedScalarContractInputFalse", UnsafeAt [12]), ("ImportedScalarContractResultFalse", UnsafeAt [12]), ("ImportedDeclaredConstructorWrongField", FormationRefusal 5 "source constructor contract does not match GHC carrier")]
                    )
                ,
                    ( "data-family representation"
                    , "ImportedDataFamily"
                    , ["--adt", "--reflection", "--ple"]
                    , [("ImportedFamilyClient", Safe), ("ImportedFamilyFalse", UnsafeAt [7]), ("ImportedNestedFamilyFalse", UnsafeAt [7])]
                    )
                ]
            ]
    client tool directory fixtures producerDirectory flags (name, expected) = do
        let target = directory </> name
        copySourceFixture fixture (fixtures </> name ++ ".hs") target name
        compile tool Strict optimization ObjectCode target name [producerDirectory </> "objects"] flags expected
    groups =
        [
            ( "native-relations"
            , []
            , [("NativeCarrierCrossSourceFormation", Safe), ("NativeCarrierNominalCrossSourceFormation", FormationRefusal 11 "Cannot unify Map_t with Array_t"), ("NativeCarrierWrongRange", FormationRefusal 11 "Invalid Relation")]
            )
        ,
            ( "text-ingress"
            , ["--adt"]
            ,
                [ ("TextIngressGood", Safe)
                , ("TextIngressRawBad", UnsafeAt [11])
                , ("TextIngressGenericBad", UnsafeAt [9])
                ]
            )
        ,
            ( "text-observations"
            , ["--adt", "--higherorder", "--higherorderqs", "--ple", "--etabeta"]
            ,
                [ ("TextObservationsGood", Safe)
                , ("DependentNestedGood", Safe)
                , ("DependentNestedBad", UnsafeAt [6])
                , ("ByteStringWord8ModelGood", Safe)
                , ("ByteStringWord8ModelBad", UnsafeAt [18])
                , ("TextConstructionGood", Safe)
                , ("TextSingletonRawBad", UnsafeAt [8])
                , ("TextSingletonFalse", UnsafeAt [8])
                , ("TextPackGood", Safe)
                , ("TextPackFalse", UnsafeAt [9])
                , ("TextAppendRawLeftBad", UnsafeAt [8])
                , ("TextAppendRawRightBad", UnsafeAt [8])
                , ("TextAppendCapacityBad", UnsafeAt [8])
                , ("TextAppendOverflowBad", UnsafeAt [23])
                , ("TextObservationsFalse", UnsafeAt [8, 12, 20, 26, 32, 37, 41, 48])
                , ("TextObservationsRawBad", UnsafeAt [7])
                , ("TextRawSplitBad", UnsafeAt [7])
                , ("TextOrdGood", Safe)
                , ("TextOrdRawGood", Safe)
                , ("TextBoundsFalse", UnsafeAt [8, 14])
                , ("TextBoundsSplitBad", UnsafeAt [8])
                , ("TextBoundsNotUtf8Bad", UnsafeAt [7])
                , ("TextBoundsLengthBad", UnsafeAt [8])
                , ("TextConstructorBoundedGood", Safe)
                , ("TextConstructorUnboundedBad", UnsafeAt [9])
                , ("TextTakeWord8Bad", UnsafeAt [8])
                , ("TextUnsafeSliceGood", Safe)
                , ("TextSmartConstructorBad", UnsafeAt [9])
                , -- GHC-generated dictionary binders have no position of their
                  -- own; their obligations belong to the use that demands them.
                  ("TextGeneratedOrdGood", Safe)
                , ("GeneratedDictionaryBad", UnsafeAt [18])
                , ("GeneratedDictionaryNestedBad", UnsafeAt [18])
                ]
            )
        ,
            ( "bounds"
            , []
            ,
                [ ("BoundInstanceGood", Safe)
                , ("BoundInstanceFalse", UnsafeAt [9])
                ]
            )
        ,
            ( "byte-reads"
            , ["--adt"]
            ,
                [ ("LazyReadBoundGood", Safe)
                , ("LazyReadShortFalse", UnsafeAt [8])
                , ("StrictReadBoundGood", Safe)
                , ("StrictReadShortFalse", UnsafeAt [8])
                ]
            )
        ,
            ( "imported-newtypes"
            , ["--adt"]
            ,
                [ ("COffInterpretationGood", Safe)
                , ("COffInterpretationBodyBad", UnsafeAt [12])
                , ("COffInterpretationPlusBad", UnsafeAt [16])
                , ("COffInterpretationMinusBad", UnsafeAt [16])
                ]
            )
        ,
            ( "inferred-interface"
            , []
            ,
                [ ("InferredConstantGood", Safe)
                , ("InferredConstantFalse", UnsafeAt [14])
                , ("InferredFunctionGood", Safe)
                , ("InferredFunctionFalse", UnsafeAt [9])
                , ("InferredDomainGood", Safe)
                , ("InferredDomainFalse", UnsafeAt [10])
                , ("InferredHoleGood", Safe)
                , ("InferredHoleFalse", UnsafeAt [10])
                , ("DefaultDomain", UnsafeAt [10])
                , ("DefaultHoleGood", Safe)
                , ("DerivedDefaultGood", Safe)
                ]
            )
        ,
            -- A failing proof group does not hide later groups' diagnostics.
            -- Each expectation is upstream's report for the same source.
            ( "group-failures"
            , []
            ,
                [ ("GroupFailuresIndependent", UnsafeAt [9, 12])
                , ("GroupFailuresSwapped", UnsafeAt [9, 12])
                , ("GroupFailuresExpectedSafe", UnsafeAt [10, 13, 15])
                , ("GroupFailuresAuthoredResult", UnsafeAt [11, 17])
                , ("GroupFailuresAuthoredBody", UnsafeAt [11, 17])
                ]
            )
        ,
            ( "assumed-predicates"
            , ["--adt"]
            ,
                [ ("ForeignAssumptionGood", Safe)
                , ("ForeignAssumptionBad", UnsafeAt [10])
                , -- GHC 9.14.1 specializes away the supplied dictionary at O2:
                  -- actual (same, different) is (1,0) at O0 and (1,1) at O2.
                  -- Only O0 retains the distinct-dictionary rejection control.
                  ("AssumptionDictionary", case optimization of O0 -> UnsafeAt [31]; O2 -> Safe)
                , ("UnliftedPredicateGood", Safe)
                , ("UnliftedPredicateBad", UnsafeAt [9])
                , ("ProjectionValueGood", Safe)
                , ("ProjectionSharingGood", Safe)
                , ("ProjectionSharingFalse", UnsafeAt [11])
                , ("ProjectionIncompleteGood", Safe)
                , ("ProjectionIncompleteBad", UnsafeAt [15])
                , ("ProjectionDomainBad", UnsafeAt [11])
                , ("ProjectionCallbackBad", UnsafeAt [11])
                , ("LogicalCarrierGood", Safe)
                , ("LogicalCarrierFalse", UnsafeAt [11])
                , ("LogicalCarrierCallbackBad", FormationRefusal 7 "LHLogicalValue")
                , ("LogicalCharCallbackGood", Safe)
                , ("LogicalCharCallbackBad", UnsafeAt [9])
                , ("ObligationContextGood", Safe)
                , ("ObligationContextBad", UnsafeAt [8])
                , ("TelescopeContextGood", Safe)
                , ("TelescopeContextBad", UnsafeAt [5])
                ]
            )
        ,
            ( "set-composition"
            , ["--adt"]
            ,
                [ ("SetCompositionGood", Safe)
                , ("SetCompositionBad", UnsafeAt [7])
                , ("SetCardinalityGood", Safe)
                , ("SetCardinalityBad", UnsafeAt [9])
                , ("LogicalEmptyNestedGood", Safe)
                , ("LogicalEmptyNestedFalse", UnsafeAt [7])
                ]
            )
        ,
            ( "type-literals"
            , ["--reflection", "--ple"]
            ,
                [ ("SymbolSetUnionGood", Safe)
                , -- The query GHC type-checks the refinement call, not the
                  -- source body; preserving the Symbol index must reject it.
                  ("SymbolCallBad", FormationRefusal 19 "Couldn't match type")
                , ("CharCallBad", FormationRefusal 17 "Illegal type specification")
                ]
            )
        ,
            ( "totality-policy"
            , ["--higherorder"]
            ,
                [ ("TotalityErrorNoPrelude", UnsafeAt [9])
                , ("TotalityPureThrow", UnsafeAt [7])
                , ("TotalityCaughtThrowIO", Safe)
                , ("TotalityErrorUnreachable", Safe)
                , ("TotalityUndefined", UnsafeAt [6])
                , ("TotalityUndefinedUnreachable", Safe)
                ]
            )
        ,
            ( "higher-kinded"
            , ["--higherorder"]
            ,
                [ ("HigherKindedCallbackGood", Safe)
                , ("HigherKindedCallbackBad", UnsafeAt [18])
                ]
            )
        ,
            ( "integer-literals"
            , ["--reflection", "--ple", "--higherorder"]
            ,
                [ ("LargeIntegerGood", Safe)
                , ("LargeIntegerBad", UnsafeAt [7])
                , ("LargeIntegerNegativeBad", UnsafeAt [7])
                ]
            )
        ,
            ( "fixed-width"
            , ["--reflection", "--ple", "--higherorder"]
            ,
                [ ("FixedWidthFirstClassGood", Safe)
                , ("FixedWidthFirstClassFalse", UnsafeAt [7, 11])
                , ("LargeBoundaryInputsGood", Safe)
                , ("Int8PairOverflow", UnsafeAt [6])
                ]
            )
        ,
            ( "constructor-tags"
            , ["--higherorder", "--ple-local"]
            , [("ConstructorTagsGood", Safe), ("ConstructorTagsFalse", UnsafeAt [12])]
            )
        ,
            ( "primitive-domains"
            , ["--adt"]
            ,
                [ ("EnumDecoderBad", UnsafeAt [12])
                , ("TypedCharLiteralGood", Safe)
                , ("TypedCharLiteralFalse", UnsafeAt [5])
                , ("TypedCharLiteralSortBad", FormationRefusal 3 "Illegal type specification")
                , ("TypedCharLiteralPayloadBad", FormationRefusal 3 "Invalid typed Char literal")
                , ("TypedCharLiteralNegativeBad", FormationRefusal 3 "Invalid typed Char literal")
                , ("TypedCharLiteralRangeBad", FormationRefusal 3 "Invalid typed Char literal")
                , ("TypedCharLiteralCanonicalBad", FormationRefusal 3 "Invalid typed Char literal")
                ]
            )
        ,
            ( "logical-measure-values"
            , []
            ,
                [ ("LogicalMeasureValueGood", Safe)
                , ("LogicalMeasureValueFalse", UnsafeAt [12])
                ]
            )
        ,
            ( "constructor-correspondence"
            , ["--higherorder"]
            ,
                [ ("ExistentialSelectorGood", Safe)
                , ("ExistentialSelectorBad", UnsafeAt [12])
                , ("ExistentialMeasureGood", Safe)
                , ("ExistentialMeasureBad", UnsafeAt [13])
                , ("ExistentialDefaultMeasureGood", Safe)
                ]
            )
        ,
            ( "constructor-qualifiers"
            , ["--adt"]
            ,
                [ ("ConstructorSelfQualifierGood", Safe)
                , ("ConstructorSelfQualifierBad", TerminationCheckAt [18])
                , ("VectorDefaultHeightGood", Safe)
                , ("VectorDefaultHeightBad", TerminationCheckAt [18])
                ]
            )
        ,
            ( "ignored"
            , ["--reflection", "--ple", "--higherorder"]
            ,
                [ ("IgnoredNestedGood", Safe)
                , ("IgnoredNestedBad", UnsafeAt [15])
                , ("IgnoredExpectedFailure", FailureAt [4])
                ]
            )
        ,
            ( "opaque-reflection"
            , []
            ,
                [ ("OpaqueNullaryGood", Safe)
                , ("OpaqueNullaryFalse", UnsafeAt [6])
                , ("OpaqueUnaryFalse", UnsafeAt [6])
                , -- Opaque reflection consults every specification's logic
                  -- names, including the field of a newtype specification.
                  ("OpaqueNewtypeFieldGood", Safe)
                , ("OpaqueNewtypeFieldFalse", UnsafeAt [17])
                ]
            )
        ,
            ( "type-family-normalization"
            , []
            ,
                [ ("FamilyRootGood", Safe)
                , ("FamilyRootBad", UnsafeAt [16])
                , ("DirectRootBad", UnsafeAt [10])
                ]
            )
        ,
            ( "alias-domain"
            , []
            ,
                [ ("AliasDomainGood", Safe)
                , ("AliasDomainBad", UnsafeAt [12])
                ]
            )
        ,
            ( "declared-alias"
            , ["--reflection"]
            ,
                [ ("DeclaredAliasGood", Safe)
                , ("DeclaredAliasFalse", UnsafeAt [47, 51, 55, 59, 63, 67, 71])
                ]
            )
        ,
            ( "measure-domain"
            , ["--adt"]
            ,
                [ ("MeasureDomainForwardBad", UnsafeAt [4])
                , ("MeasureDomainBackwardBad", UnsafeAt [9])
                , ("MeasureDomainGood", Safe)
                ]
            )
        ,
            ( "method-domain"
            , ["--typeclass"]
            ,
                [ ("ConstrainedMethodDomainGood", Safe)
                , ("ConstrainedMethodDomainBad", UnsafeAt [21])
                , ("ConstrainedMethodDomainUnknown", UnsafeAt [21])
                ]
            )
        ,
            ( "expected-claims"
            , []
            ,
                [ ("ExpectedMeasureAfter", UnsafeAt [5, 6])
                , ("ExpectedMeasureGood", Safe)
                , ("ExpectedRewriteFalse", UnsafeAt [7])
                , ("ReturnedCallbackGood", Safe)
                , ("ReturnedCallbackFalse", UnsafeAt [5])
                , ("StagedMeasureCallable", Safe)
                , ("StagedMeasureCycleGood", Safe)
                , ("StagedMeasureCycleBad", UnsafeAt [12, 13])
                ]
            )
        ,
            ( "lexical"
            , ["--reflection", "--ple", "--ple-with-undecided-guards"]
            ,
                [ ("LexicalBranchTautologyGood", Safe)
                , ("LexicalBranchTautologyBad", UnsafeAt [15])
                , ("LexicalShadowTautologyGood", Safe)
                , ("LexicalShadowTautologyBad", UnsafeAt [16])
                , ("LexicalCallbackGood", Safe)
                , ("LexicalCallbackBad", UnsafeAt [7, 9])
                , ("LexicalTemplateNamesGood", Safe)
                , ("NominalTermScopeGood", Safe)
                , ("NominalTermScopeCastBad", FormationRefusal 7 "Illegal type specification")
                , ("NominalTermScopeRenamedCastBad", FormationRefusal 7 "Illegal type specification")
                ]
            )
        ,
            ( "arithmetic"
            , ["--higherorder"]
            ,
                [ ("LogicalArithmeticGood", Safe)
                , ("LogicalArithmeticFalse", UnsafeAt [5])
                , ("LogicalRealGood", Safe)
                , ("LogicalRealFalse", UnsafeAt [5])
                , ("LogicalRealModInvalid", FormationRefusal 3 "Illegal type specification")
                ]
            )
        ,
            ( "ordering"
            , []
            ,
                [ ("IntegerOrderingGood", Safe)
                , ("IntegerOrderingBad", UnsafeAt [5])
                ]
            )
        ,
            ( "derived-payload"
            , []
            ,
                [ ("DerivedPayloadEq", Safe)
                , ("DerivedPayloadEqBad", UnsafeAt [10])
                , ("DerivedNullaryGood", Safe)
                , ("DerivedNullaryBad", UnsafeAt [3])
                ]
            )
        ,
            ( "dictionary-values"
            , []
            ,
                [ ("DictionaryValueFieldGood", Safe)
                , ("DictionaryValueBottomBad", UnsafeAt [8])
                ]
            )
        ,
            ( "recursive-record"
            , []
            ,
                [ ("RecursiveMethodRecordGood", Safe)
                , ("RecursiveMethodRecordBad", TerminationCheckAt [16])
                ]
            )
        ,
            ( "rewrite-dependencies"
            , ["--reflection", "--ple"]
            ,
                [ ("TransitiveRewriteContractGood", Safe)
                , -- Rejected callees retain only their independently checked
                  -- contracts, so their callers cannot borrow the false claim.
                  ("TransitiveRewriteFalse", UnsafeAt [18])
                , ("MutualRewriteFalse", UnsafeAt [10, 16])
                , ("ExplicitRewriteCycleFalse", UnsafeAt [15])
                , ("MediatedRewriteCycleFalse", UnsafeAt [23])
                , -- A rule's precondition names its value, not the argument binder.
                  ("RewritePreconditionBinderGood", Safe)
                , ("RewritePreconditionBinderFalse", UnsafeAt [25])
                ]
            )
        ,
            ( "dictionary-reflection"
            , ["--reflection", "--ple"]
            ,
                [ ("DefaultStimesGood", Safe)
                , ("DefaultStimesBad", UnsafeAt [11])
                ]
            )
        ,
            ( "variance"
            , ["--adt", "--higherorder"]
            ,
                [ ("VarianceGood", Safe)
                , -- Reject both the invalid widening and its caller's negative
                  -- argument; recovery must not retain the rejected interface.
                  ("NestedVarianceBad", UnsafeAt [18])
                , ("HigherKindedVarianceBad", UnsafeAt [19])
                , ("DeclaredCovarianceBad", FormationRefusal 3 "Declared variance contradicts constructor-field occurrences")
                , ("DeclaredContravarianceBad", FormationRefusal 3 "Declared variance contradicts constructor-field occurrences")
                ]
            )
        ,
            ( "callback-projections"
            , []
            ,
                [ ("CallbackProjectionGood", Safe)
                , ("CallbackProjectionFalse", UnsafeAt [16])
                ]
            )
        ,
            ( "lambda-singletons"
            , -- PLE supplies beta equalities only when etabeta enables its rule.
              ["--higherorder", "--ple", "--etabeta"]
            ,
                [ ("DependentLambdaGood", Safe)
                , ("DependentLambdaFalse", UnsafeAt [11])
                ]
            )
        ,
            ( "function-coercions"
            , ["--higherorder"]
            ,
                [ ("FunctionCoercionGood", Safe)
                , ("FunctionCoercionBad", UnsafeAt [9])
                , ("FunctionCoercionDemandBad", TerminationCheckAt [9, 14])
                , ("EqualityEvidenceGood", Safe)
                , ("EqualityEvidenceBad", UnsafeAt [16, 20])
                , ("BoundEvidenceGood", Safe)
                , ("BoundEvidenceBad", UnsafeAt [13])
                , ("BoundDirectBad", UnsafeAt [9])
                , ("BoundComposeBad", UnsafeAt [9])
                , ("PartialContextBad", FormationRefusal 3 "Specified type does not refine Haskell type")
                ]
            )
        ,
            ( "newtype-evidence"
            , ["--adt", "--higherorder"]
            ,
                [ ("NewtypeEvidenceGood", Safe)
                , -- Construction also fails independent admission; isolate the
                  -- other claims so that recovery cannot stop before their checks.
                  ("NewtypeEvidenceBad", UnsafeAt [16])
                , ("NewtypeRangeBad", UnsafeAt [16])
                , ("NewtypeProjectionBad", UnsafeAt [16])
                , -- A constructor application is a cast; its expected refinement
                  -- is an obligation, never a premise of the cast.
                  ("NewtypeCastExpectedBad", UnsafeAt [12, 16])
                , -- Composed coercions are checked and interpreted at each
                  -- intermediate newtype boundary.
                  ("NewtypeComposedDomainGood", Safe)
                , ("NewtypeComposedDomainBad", UnsafeAt [13])
                ]
            )
        ,
            ( "termination"
            , []
            ,
                [ ("DictionaryConstructionGood", Safe)
                , ("DictionaryTerminationGood", Safe)
                , ("DictionaryTermination", TerminationAt [12])
                , ("RecursiveValueClaim", TerminationCheckAt [5])
                , ("RecursiveInvariantClaim", TerminationCheckAt [9])
                , ("RecursiveFunctionPrefixClaim", TerminationCheckAt [5, 10])
                , ("RecursiveProjectionClaim", TerminationCheckAt [10])
                ]
            )
        ]

importedByteProducer :: String
importedByteProducer =
    unlines
        [ "module ImportedByteProducer (asciiBytes) where"
        , ""
        , "import Data.Word (Word8)"
        , ""
        , "{-@ measure asciiBytes @-}"
        , "asciiBytes :: [Word8] -> Bool"
        , "asciiBytes [] = True"
        , "asciiBytes (byte : rest) = byte <= 127 && asciiBytes rest"
        ]

importedByteClient :: String -> String -> String -> String
importedByteClient name input body =
    unlines
        [ "module " ++ name ++ " where"
        , ""
        , "import ImportedByteProducer (asciiBytes)"
        , "import Data.Word (Word8)"
        , ""
        , "{-@ keepLow :: " ++ input ++ " -> {r:[Word8] | asciiBytes r} @-}"
        , "keepLow :: Word8 -> [Word8]"
        , "keepLow w = " ++ body
        ]

liftedFamilyProducer :: String
liftedFamilyProducer =
    unlines
        [ "{-# LANGUAGE TypeFamilies #-}"
        , ""
        , "module LiftedFamilyProducer (Family (..), nestedValue) where"
        , ""
        , "data family Family tag a"
        , "data instance Family (Maybe tag) a = NestedFamily a"
        , ""
        , "{-@ measure nestedValue @-}"
        , "nestedValue :: Family (Maybe Bool) Integer -> Integer"
        , "nestedValue (NestedFamily value) = value"
        ]

-- Explicit logical constructor applications require the ordinary equation
-- unfolding mechanism. Result-refinement clients below remain independent.
liftedFamilyClient :: String -> String -> String
liftedFamilyClient name relation =
    unlines
        [ "module " ++ name ++ " where"
        , "{-@ LIQUID \"--ple\" @-}"
        , "import LiftedFamilyProducer (Family (..), nestedValue)"
        , ""
        , "{-@ claim :: x:Integer -> {v:Integer | v " ++ relation ++ " nestedValue (NestedFamily x)} @-}"
        , "claim :: Integer -> Integer"
        , "claim value = value"
        ]

liftedFamilyResultClient :: String -> String -> String
liftedFamilyResultClient name expected =
    unlines
        [ "module " ++ name ++ " where"
        , ""
        , "import LiftedFamilyProducer"
        , ""
        , "{-@ make :: n:Integer -> {r:Family (Maybe Bool) Integer | nestedValue r == " ++ expected ++ "} @-}"
        , "make :: Integer -> Family (Maybe Bool) Integer"
        , "make n = NestedFamily n"
        ]

liftedFamilyWrongIndex :: String
liftedFamilyWrongIndex =
    unlines
        [ "module LiftedFamilyWrongIndex where"
        , ""
        , "import LiftedFamilyProducer (Family (..), nestedValue)"
        , ""
        , "{-@ claim :: x:Family (Maybe Char) Integer -> {v:Integer | v == nestedValue x} @-}"
        , "claim :: Family (Maybe Char) Integer -> Integer"
        , "claim (NestedFamily value) = value"
        ]

measureNewtypeCast :: String
measureNewtypeCast =
    unlines
        [ "module MeasureNewtypeCast where"
        , ""
        , "import Data.Coerce (coerce)"
        , ""
        , "data Choice = A | B"
        , "newtype Wrapped = Wrapped Choice"
        , ""
        , ""
        , "{-@ measure flag @-}"
        , "flag :: Wrapped -> Bool"
        , "flag wrapped = case (coerce wrapped :: Choice) of"
        , "    A -> True"
        , "    B -> False"
        ]

scopedAsciiProducer :: String
scopedAsciiProducer =
    unlines
        [ "module ScopedAsciiProducer (asciiBytes, lowerHexBytes) where"
        , "import Data.Word (Word8)"
        , "{-@ measure asciiModel :: [Word8] -> Bool"
        , "      asciiModel [] = true"
        , "      asciiModel (byte : rest) = byte <= 127 && asciiModel rest @-}"
        , "{-@ asciiBytes :: bytes:[Word8] -> {v:Bool | v <=> asciiModel bytes} / [len bytes] @-}"
        , "asciiBytes :: [Word8] -> Bool"
        , "asciiBytes [] = True"
        , "asciiBytes (byte : rest) = byte <= 127 && asciiBytes rest"
        , "{-@ digit :: {n:Word8 | n < 16} -> {v:Word8 | v <= 127} @-}"
        , "digit :: Word8 -> Word8"
        , "digit n = if n < 10 then 48 + n else 87 + n"
        , "{-@ lowerHexBytes :: bytes:[Word8] -> {r:[Word8] | asciiModel r} / [len bytes] @-}"
        , "lowerHexBytes :: [Word8] -> [Word8]"
        , "lowerHexBytes [] = []"
        , "lowerHexBytes (byte : rest) = digit (byte `quot` 16) : digit (byte `rem` 16) : lowerHexBytes rest"
        ]

scopedNarrowProducer :: String
scopedNarrowProducer = scopedNarrowSource "ScopedNarrowProducer" "len r == 1 && oneModel r"

scopedNarrowSource :: String -> String -> String
scopedNarrowSource name predicate =
    unlines
        [ "module " ++ name ++ " (one) where"
        , "import Data.Word (Word8)"
        , "{-@ measure oneModel :: {xs:[Word8] | len xs == 1} -> Bool"
        , "      oneModel [] = true"
        , "      oneModel (byte : rest) = true @-}"
        , "{-@ one :: Word8 -> {r:[Word8] | " ++ predicate ++ "} @-}"
        , "one :: Word8 -> [Word8]"
        , "one byte = [byte]"
        ]

scopedNarrowClient :: String -> String -> String
scopedNarrowClient name expression =
    unlines
        [ "module " ++ name ++ " where"
        , "import Data.Word (Word8)"
        , "import ScopedNarrowProducer"
        , ""
        , "{-@ claim :: byte:Word8 -> {r:[Word8] | len r == 1 && oneModel r} @-}"
        , "claim :: Word8 -> [Word8]"
        , "claim byte = " ++ expression
        ]

scopedAsciiClient :: String -> String -> String
scopedAsciiClient name predicate =
    unlines
        [ "module " ++ name ++ " where"
        , "import Data.Word (Word8)"
        , "import ScopedAsciiProducer"
        , ""
        , "{-@ claim :: bytes:[Word8] -> {r:[Word8] | " ++ predicate ++ "} @-}"
        , "claim :: [Word8] -> [Word8]"
        , "claim bytes = lowerHexBytes bytes"
        ]

scopedAsciiNativeUse :: String -> String -> String
scopedAsciiNativeUse name carrier =
    unlines
        [ "module " ++ name ++ " where"
        , "import Data.Word (Word8)"
        , "import ScopedAsciiProducer"
        , ""
        , "{-@ claim :: xs:[" ++ carrier ++ "] -> {v:Bool | v <=> asciiModel xs} @-}"
        , "claim :: [" ++ carrier ++ "] -> Bool"
        , "claim _ = True"
        ]

scopedAsciiIsolation :: String -> String -> String
scopedAsciiIsolation name carrier =
    unlines
        [ "module " ++ name ++ " where"
        , "import ScopedAsciiProducer ()"
        , ""
        , "{-@ impossible :: [" ++ carrier ++ "] -> {v:Bool | false} @-}"
        , "impossible :: [" ++ carrier ++ "] -> Bool"
        , "impossible [] = True"
        , "impossible (_ : _) = True"
        ]

importedBoolProducer :: String
importedBoolProducer =
    unlines
        [ "module ImportedBoolProducer (B (..), observed) where"
        , ""
        , "data B a = B a"
        , ""
        , "{-@ measure observed @-}"
        , "observed :: B Bool -> Bool"
        , "observed (B flag) = flag"
        ]

importedMeasureCollision :: String
importedMeasureCollision =
    unlines
        [ "module ImportedMeasureCollision where"
        , ""
        , "import ImportedBoolProducer"
        , ""
        , "{-@ data D = D { field :: {x:Int | observed x <=> (x == 0)} } @-}"
        , "data D = D Int"
        , ""
        , "unit :: ()"
        , "unit = ()"
        ]
