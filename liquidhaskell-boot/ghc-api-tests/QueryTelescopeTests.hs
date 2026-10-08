{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module QueryTelescopeTests (tests) where

import Control.Exception (evaluate, throw, try)
import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Data.Either (isLeft)
import Data.Generics (everywhere, mkT)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (find)
import Data.String (fromString)
import Data.Time (getCurrentTime)
import qualified GHC
import qualified GHC.Builtin.Types as G (integerTy)
import qualified GHC.Data.FastString as G (fsLit)
import qualified GHC.Data.StringBuffer as G (stringToStringBuffer)
import qualified GHC.Hs as G (mkHsLam, nlHsVar, nlVarPat)
import GHC.Paths (libdir)
import qualified GHC.Tc.Utils.Monad as Tc (initTcWithGbl)
import qualified GHC.Types.Name.Occurrence as G (mkDataOcc, mkVarOcc)
import qualified GHC.Types.Name.Reader as G (mkRdrUnqual)
import qualified GHC.Types.SrcLoc as G (mkRealSrcLoc, mkRealSrcSpan)
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import Language.Haskell.Liquid.Bare.Elaborate (alignQueryTelescope, elaborateSpecTypeWithPrimitives, freshenQueryTelescope)
import Language.Haskell.Liquid.Bare.Plugged (makePluggedSig)
import qualified Language.Haskell.Liquid.Bare.Types as Bare
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.Errors (Oblig (OCons), TError (ErrOther, ErrTySpec), UserError)
import Language.Haskell.Liquid.Types.RType (PVarBV (PV), PredicateBV (Pr), RTyCon (RTyCon), RTyVar (RTV), RTypeBV (RAllP, RApp, RHole, RRTy), SpecType, pattern MkUReft)
import Language.Haskell.Liquid.Types.RTypeOp
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, toType)
import Language.Haskell.Liquid.Types.Types (Error, MeasureKind (MsMeasure), ModName (..), ModType (..), TyConMap (..))
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore = withResource prepare (const (pure ())) $ \fixture ->
    testGroup
        "typed query telescope"
        [ testCase "opaque source projection restores independent forall owners and domains" $ do
            program <- fixture
            (owner, _) <- binding "mapped" program
            let original = symbolicSchema owner
                representation = toRTypeRep original
                domain = MkUReft (F.Reft ("vv", F.PFalse)) mempty
                narrowed = fromRTypeRep representation{ty_args = init (ty_args representation) ++ [strengthen (last $ ty_args representation) domain]}
                aligned = sourceProjection owner narrowed
            assertBool "independent source variables collapsed" (sameNative owner aligned)
            F.reftPred (rTypeReft $ last $ ty_args $ toRTypeRep aligned) @?= F.PFalse
        , testCase "opaque source projection rejects repeated or swapped coordinates" $ do
            program <- fixture
            (owner, _) <- binding "mapped" program
            let original = symbolicSchema owner
                representation = toRTypeRep original
            case ty_args representation of
                [evidence, RApp constructor [left, right] predicates reft, selected] -> do
                    let repeated = fromRTypeRep representation{ty_args = [evidence, RApp constructor [left, left] predicates reft, selected]}
                        swapped = fromRTypeRep representation{ty_args = [evidence, RApp constructor [right, left] predicates reft, selected]}
                    mapM_ (assertProjectionRefusal owner) [repeated, swapped]
                _ -> assertFailure "expected evidence, pair, and selected-coordinate telescope"
        , testCase "dictionary and value owners follow checked lambda positions" $ do
            program <- fixture
            (owner, core) <- binding "one" program
            let source = named ["evidence", "$dordinary"] owner
            (owners, _) <- either (\message -> assertFailure message >> pure ([], [])) pure (alignQueryTelescope source core)
            map snd owners @?= [F.EVar "evidence", F.EVar "$dordinary"]
        , testCase "distinct nominal inputs cannot share an embedding" $ do
            program <- fixture
            (owner, core) <- binding "ordinary" program
            let representation = toRTypeRep (named ["input"] owner)
                wrong = fromRTypeRep representation{ty_args = [ofType G.integerTy]}
            assertBool "Integer input matched actual Int" (isLeft (alignQueryTelescope wrong core))
        , testCase "missing dictionary cannot shift a value into its position" $ do
            program <- fixture
            (owner, core) <- binding "one" program
            let representation = toRTypeRep (named ["evidence", "input"] owner)
                wrong = fromRTypeRep representation{ty_binds = drop 1 (ty_binds representation), ty_info = drop 1 (ty_info representation), ty_args = drop 1 (ty_args representation), ty_refts = drop 1 (ty_refts representation)}
            assertBool "missing evidence admitted" (isLeft (alignQueryTelescope wrong core))
        , testCase "two explicit dictionary owners cannot collapse" $ do
            program <- fixture
            (owner, core) <- binding "two" program
            let source = named ["same", "same", "left", "right"] owner
            assertBool "two distinct checked givens acquired one logical owner" (isLeft (alignQueryTelescope source core))
        , testCase "two dictionary types retain their ordered owners" $ do
            program <- fixture
            (owner, core) <- binding "two" program
            let source = named ["first", "second", "left", "right"] owner
            (owners, _) <- either (\message -> assertFailure message >> pure ([], [])) pure (alignQueryTelescope source core)
            map snd owners @?= map F.EVar ["first", "second", "left", "right"]
        , testCase "anonymous owners are distinct and avoid the source catalog" $ do
            program <- fixture
            (owner, _) <- binding "two" program
            let original = named [F.dummySymbol, F.dummySymbol, "left", "right"] owner
                reserved = ["lh_query_owner", "left", "right"]
                names = take 2 (ty_binds (toRTypeRep (freshenQueryTelescope False reserved original)))
            case names of
                [first, second] -> assertBool "independent anonymous dictionaries collapsed" (first /= second)
                _ -> assertFailure "anonymous dictionary telescope changed arity"
            assertBool "anonymous owner captured a source-catalog symbol" (all (`notElem` reserved) names)
        , testCase "freshness observes term owners without forcing numeric sort capabilities" $ do
            let free = "lh_query_owner"
                bound = F.intSymbol free 0
                carrier = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "Carrier") (error "numeric capability forced by freshness") (error "real capability forced by freshness"))
                predicate = F.PAll [(bound, carrier)] (F.PAtom F.Eq (F.EVar free) (F.EVar bound))
                original = rFun F.dummySymbol (RHole mempty) (RHole (MkUReft (F.Reft ("vv", predicate)) mempty)) :: SpecType
                names = ty_binds (toRTypeRep (freshenQueryTelescope False [] original))
            case names of
                [name] -> assertBool "fresh owner captured a free or quantified term name" (name /= free && name /= bound)
                _ -> assertFailure "anonymous owner telescope changed arity"
        , testCase "constructor predicate defaults remain in the freshness inventory" $ do
            program <- fixture
            (owner, _) <- binding "ordinary" program
            case ty_res (toRTypeRep (ofType (G.varType owner) :: SpecType)) of
                RApp (RTyCon constructor _ info) arguments predicates reft -> do
                    let defaultName = "lh_query_owner"
                        schema = PV "schema" (toRSort (ofType G.intTy :: SpecType)) [(toRSort (ofType G.intTy :: SpecType), "formal", F.EVar defaultName)]
                        domain = RApp (RTyCon constructor [schema] info) arguments predicates reft
                        original = rFun F.dummySymbol domain (RHole mempty)
                        names = ty_binds (toRTypeRep (freshenQueryTelescope False [] original))
                    case names of
                        [name] -> assertBool "fresh owner captured a constructor predicate default" (name /= defaultName)
                        _ -> assertFailure "constructor default telescope changed arity"
                _ -> assertFailure "expected the Int result carrier"
        , testCase "explicit dictionary shadowing preserves outer domains and inner results" $ do
            program <- fixture
            (owner, _) <- binding "two" program
            let representation = toRTypeRep (named ["same", "same", "left", "right"] owner)
                dependent = MkUReft (F.Reft ("vv", F.PAtom F.Ne (F.EVar "same") (F.EVar "outerWitness"))) mempty
                arguments = case ty_args representation of
                    first : second : rest -> first : strengthen second dependent : rest
                    other -> other
                result = strengthen (ty_res representation) dependent
                original = fromRTypeRep representation{ty_args = arguments, ty_res = result}
                refreshed = toRTypeRep (freshenQueryTelescope False ["same", "outerWitness"] original)
            case (ty_binds refreshed, ty_args refreshed) of
                (outer : inner : _, _ : innerDomain : _) -> do
                    outer @?= "same"
                    assertBool "shadowing dictionaries collapsed" (inner /= outer)
                    assertBool "fresh dictionary captured a source symbol" (inner /= "outerWitness")
                    F.reftPred (rTypeReft innerDomain) @?= F.PAtom F.Ne (F.EVar outer) (F.EVar "outerWitness")
                    F.reftPred (rTypeReft (ty_res refreshed)) @?= F.PAtom F.Ne (F.EVar inner) (F.EVar "outerWitness")
                _ -> assertFailure "dictionary normalization changed the source telescope"
            (_, core) <- binding "two" program
            case alignQueryTelescope (fromRTypeRep refreshed) core of
                Left message -> assertFailure message
                Right (owners, _) -> map snd owners @?= map F.EVar (ty_binds refreshed)
        , testCase "a value shadowing dictionary evidence keeps distinct checked owners" $ do
            program <- fixture
            (owner, core) <- binding "one" program
            let representation = toRTypeRep (named ["same", "same"] owner)
                dependent = MkUReft (F.Reft ("vv", F.PAtom F.Ne (F.EVar "same") (F.EVar "outerWitness"))) mempty
                original = fromRTypeRep representation{ty_res = strengthen (ty_res representation) dependent}
                refreshed = toRTypeRep (freshenQueryTelescope False [] original)
            case ty_binds refreshed of
                [evidence, value] -> do
                    assertBool "value and evidence acquired one owner" (evidence /= value)
                    F.reftPred (rTypeReft (ty_res refreshed)) @?= F.PAtom F.Ne (F.EVar value) (F.EVar "outerWitness")
                _ -> assertFailure "value shadowing changed the telescope"
            case alignQueryTelescope (fromRTypeRep refreshed) core of
                Left message -> assertFailure message
                Right (owners, _) -> map snd owners @?= map F.EVar (ty_binds refreshed)
        , testCase "subtype endpoints do not bind each other's owner labels" $ do
            program <- fixture
            (owner, _) <- binding "two" program
            let representation = toRTypeRep (named ["same", "same", "left", "right"] owner)
                dependent = MkUReft (F.Reft ("vv", F.PAtom F.Ne (F.EVar "same") (F.EVar "outerWitness"))) mempty
                endpoint = strengthen (ty_res representation) dependent
                original = fromRTypeRep representation{ty_res = RRTy [("same", endpoint), ("rhs", endpoint)] mempty OCons endpoint}
                refreshed = toRTypeRep (freshenQueryTelescope False [] original)
            case (ty_binds refreshed, ty_res refreshed) of
                (_ : inner : _, RRTy [("same", lhs), ("rhs", rhs)] _ OCons payload) ->
                    map (F.reftPred . rTypeReft) [lhs, rhs, payload] @?= replicate 3 (F.PAtom F.Ne (F.EVar inner) (F.EVar "outerWitness"))
                _ -> assertFailure "subtype normalization changed endpoint ownership"
        , testCase "a refinement value binds its abstract predicate actuals" $ do
            program <- fixture
            (owner, _) <- binding "two" program
            let representation = toRTypeRep (named ["same", "same", "left", "right"] owner)
                abstract = Pr [PV "abstract" mempty [(mempty, "argument", F.EVar "same")]]
            case ty_res representation of
                RApp constructor arguments predicates _ -> do
                    let result = RApp constructor arguments predicates (MkUReft (F.Reft ("same", F.PTrue)) abstract)
                        refreshed = toRTypeRep (freshenQueryTelescope False [] (fromRTypeRep representation{ty_res = result}))
                    case ty_res refreshed of
                        RApp _ _ _ (MkUReft (F.Reft (value, predicate)) actuals) -> do
                            value @?= "same"
                            predicate @?= F.PTrue
                            actuals @?= abstract
                        _ -> assertFailure "abstract predicate normalization changed the carrier"
                _ -> assertFailure "expected the Bool result carrier"
        , testCase "container self scope masks arrow owners only when configured" $ do
            program <- fixture
            (owner, _) <- binding "selfList" program
            let representation = toRTypeRep (named ["same", "same"] owner)
            case ty_res representation of
                RApp constructor [element] predicates _ -> do
                    let refinement = MkUReft (F.Reft ("vv", F.PAtom F.Eq (F.EVar "vv") (F.EApp (F.EVar "len") (F.EVar "same")))) mempty
                        result = RApp constructor [strengthen element refinement] predicates (MkUReft (F.Reft ("same", F.PTrue)) mempty)
                        original = fromRTypeRep representation{ty_res = result}
                    mapM_
                        ( \bindSelf -> case toRTypeRep (freshenQueryTelescope bindSelf [] original) of
                            refreshed -> case (ty_binds refreshed, ty_res refreshed) of
                                (_ : inner : _, RApp _ [child] _ _) ->
                                    F.reftPred (rTypeReft child) @?= F.PAtom F.Eq (F.EVar "vv") (F.EApp (F.EVar "len") (F.EVar (if bindSelf then "same" else inner)))
                                _ -> assertFailure "self-scope normalization changed the list carrier"
                        )
                        [False, True]
                _ -> assertFailure "expected an actual list carrier"
        , testCase "abstract predicate names do not shadow concrete term owners" $ do
            program <- fixture
            (owner, _) <- binding "two" program
            let representation = toRTypeRep (named ["same", "same", "left", "right"] owner)
                predicate = PV "same" (toRSort (ofType G.intTy :: SpecType)) []
                dependent = MkUReft (F.Reft ("vv", F.PAtom F.Ne (F.EVar "same") (F.EVar "outerWitness"))) mempty
                original = fromRTypeRep representation{ty_res = RAllP predicate (strengthen (ty_res representation) dependent)}
                refreshed = toRTypeRep (freshenQueryTelescope False [] original)
            case (ty_binds refreshed, ty_res refreshed) of
                (_ : inner : _, RAllP (PV name _ _) result) -> do
                    name @?= "same"
                    F.reftPred (rTypeReft result) @?= F.PAtom F.Ne (F.EVar inner) (F.EVar "outerWitness")
                _ -> assertFailure "predicate normalization changed namespace ownership"
        , testCase "Storable predicate uses the actual checked-expression pipeline" $ do
            (source, core) <- checkedStorableQuery False
            case alignQueryTelescope source core of
                Left message -> assertFailure message
                Right _ -> pure ()
        , testCase "normalized primitive query still refuses a nominal source mismatch" $ do
            (source, core) <- checkedStorableQuery False
            let representation = toRTypeRep source
                arguments = case reverse (ty_args representation) of
                    _ : rest -> reverse (ofType G.integerTy : rest)
                    [] -> []
                wrong = fromRTypeRep representation{ty_args = arguments}
            assertBool "normalization weakened pointer carrier admission" (isLeft (alignQueryTelescope wrong core))
        , testCase "a represented value may shadow an enclosing query input" $ do
            (source, core) <- checkedStorableQuery True
            case alignQueryTelescope source core of
                Left message -> assertFailure message
                Right (owners, _) -> do
                    let names = map snd owners
                    assertBool "represented value reused the enclosing input owner" (length (filter (== F.EVar "input") names) == 1)
        , testCase "source catalog duplicates retain their last declaration" $
            void $
                checkedSourceQuery (const (pure (catalogType, duplicateCatalog, [])))
        , testCase "reversing conflicting source catalog declarations rejects the application" $
            assertQueryRefusal (checkedSourceQuery (const (pure (catalogType, reverse duplicateCatalog, []))))
        , testCase "a lexical refinement value shadows the fixed source catalog" $
            void $
                checkedSourceQuery (const (pure (shadowedType, [(F.intSymbol "shadow" 0, MsMeasure, integer)], [])))
        , testCase "sibling source queries independently instantiate one forall declaration" $
            void $
                checkedSourceQuery independentQueries
        , testCase "an invalid source query rejects after a valid sibling" $
            assertQueryRefusal (checkedSourceQuery (const (pure (invalidSibling, [], []))))
        , testCase "a failed source query cannot constrain a later independent query" $ do
            assertQueryRefusal (checkedSourceQuery (const (pure (invalidSibling, [], []))))
            void $ checkedSourceQuery independentQueries
        ]
  where
    integer = ofType G.intTy :: SpecType
    boolean = ofType G.boolTy :: SpecType
    refine :: SpecType -> F.Expr -> SpecType
    refine ty predicate = strengthen ty (MkUReft (F.Reft ("vv", predicate)) mempty)
    duplicateCatalog = [("duplicate", MsMeasure, rFun "input" boolean boolean), ("duplicate", MsMeasure, rFun "input" integer integer)]
    catalogType = refine integer (F.PAtom F.Eq (F.EApp (F.EVar "duplicate") (F.EVar "vv")) (F.EVar "vv"))
    shadowedType = strengthen boolean (MkUReft (F.Reft ("shadow", F.EVar "shadow")) mempty)
    validInteger = refine integer (F.PAtom F.Ge (F.EVar "vv") (F.ECon (F.I 0)))
    invalidSibling = rFun "first" validInteger (rFun "second" (refine boolean (F.PAtom F.Ge (F.EVar "vv") (F.ECon (F.I 0)))) boolean)
    independentQueries program = do
        (owner, _) <- binding "identity" program
        let application = F.EApp (F.EVar "identity") (F.EVar "vv")
            signature =
                rFun "first" (refine integer (F.PAtom F.Eq application (F.EVar "vv"))) $
                    rFun "second" (refine boolean (F.PIff application (F.EVar "vv"))) boolean
        pure (signature, [], [("identity", owner)])
    prepare =
        compileToCore "QueryTelescope" $
            unlines
                [ "{-# LANGUAGE ExplicitForAll #-}"
                , "module QueryTelescope where"
                , "class K a where k :: a -> Bool"
                , "class L a where l :: a -> Bool"
                , "one :: forall a. K a => a -> Bool"
                , "one x = k x"
                , "two :: forall a b. (K a, L b) => a -> b -> Bool"
                , "two x y = k x && l y"
                , "ordinary :: Int -> Bool"
                , "ordinary x = x == x"
                , "selfList :: [Int] -> [Int] -> [Int]"
                , "selfList _ _ = []"
                , "mapped :: forall a b. Ord a => (a, b) -> a -> Maybe b"
                , "mapped _ _ = Nothing"
                ]

symbolicSchema :: G.Var -> SpecType
symbolicSchema owner = everywhere (mkT symbolic) (ofType (G.varType owner) :: SpecType)
  where
    symbolic :: RTyVar -> RTyVar
    symbolic (RTV variable) = RTV (GM.symbolTyVar $ F.symbol variable)

sourceProjection :: G.Var -> SpecType -> SpecType
sourceProjection owner = F.val . makePluggedSig False (ModName Target $ G.mkModuleName "QueryTelescope") mempty (TyConMap mempty mempty mempty) mempty (Bare.HsTV owner) . F.dummyLoc

sameNative :: G.Var -> SpecType -> Bool
sameNative owner schema = G.eqType (toType False schema) (toType False $ (ofType $ G.varType owner :: SpecType))

assertProjectionRefusal :: G.Var -> SpecType -> Assertion
assertProjectionRefusal owner schema = do
    result <- try (evaluate $ sameNative owner $ sourceProjection owner schema) :: IO (Either Error Bool)
    case result of
        Left _ -> pure ()
        Right matched -> assertBool "incompatible original coordinates acquired native source identity" (not matched)

named :: [F.Symbol] -> G.Var -> SpecType
named names owner = fromRTypeRep (toRTypeRep (ofType (G.varType owner) :: SpecType)){ty_binds = names}

binding :: String -> G.CoreProgram -> IO (G.Var, G.CoreExpr)
binding name program = case find ((== name) . G.getOccString . fst) (G.flattenBinds program) of
    Just pair -> pure pair
    Nothing -> assertFailure ("missing fixture binding " ++ name) >> fail name

checkedStorableQuery :: Bool -> IO (SpecType, G.CoreExpr)
checkedStorableQuery shadowValue = do
    (readback, source, core) <- checkedSourceQuery $ \program -> do
        (owner, _) <- binding "query" program
        (plen, _) <- binding "plen" program
        let representation = toRTypeRep (named [F.dummySymbol, "input"] owner)
            predicate = MkUReft (F.Reft ("vv", F.PAtom F.Lt (F.ECon (F.I 0)) (F.EApp (F.EVar "plen") (F.EVar "vv")))) mempty
            arguments = case ty_args representation of
                evidence : pointer : rest -> evidence : strengthen pointer predicate : rest
                other -> other
            result =
                if shadowValue
                    then strengthen (ty_res representation) (MkUReft (F.Reft ("input", F.EVar "input")) mempty)
                    else ty_res representation
            refined = fromRTypeRep representation{ty_args = arguments, ty_res = result}
        pure (refined, [("plen", MsMeasure, ofType (G.varType plen))], [])
    assertBool "administrative alias lost the plen denotation during readback" ("plen" `elem` F.syms readback)
    if shadowValue
        then F.reftPred (rTypeReft (ty_res (toRTypeRep readback))) @?= F.EVar "input"
        else pure ()
    pure (source, core)

assertQueryRefusal :: IO a -> Assertion
assertQueryRefusal action = do
    result <- try (void action) :: IO (Either UserError ())
    case result of
        Left (ErrTySpec _ owner _ _ _) -> owner @?= Just "refinement formation"
        Left other -> assertFailure ("unexpected source-query error: " ++ show other)
        Right () -> assertFailure "ill-sorted source query was admitted"

checkedSourceQuery ::
    (G.CoreProgram -> IO (SpecType, [(F.Symbol, MeasureKind, SpecType)], [(F.Symbol, G.Var)])) ->
    IO (SpecType, SpecType, G.CoreExpr)
checkedSourceQuery inputs = GHC.runGhc (Just libdir) $ do
    now <- liftIO getCurrentTime
    flags <- GHC.getSessionDynFlags
    void $ GHC.setSessionDynFlags flags{GHC.backend = GHC.interpreterBackend}
    let source =
            unlines
                [ "{-# LANGUAGE ExplicitForAll #-}"
                , "module CheckedStorableQuery where"
                , "import Foreign.Storable"
                , "import Foreign.Ptr"
                , "query :: forall a. Storable a => Ptr a -> Bool"
                , "query _ = True"
                , "plen :: forall a. Ptr a -> Int"
                , "plen _ = 0"
                , "identity :: forall a. a -> a"
                , "identity x = x"
                ]
        target =
            GHC.Target
                { GHC.targetId = GHC.TargetFile "CheckedStorableQuery.hs" Nothing
                , GHC.targetUnitId = GHC.homeUnitId_ flags
                , GHC.targetAllowObjCode = False
                , GHC.targetContents = Just (G.stringToStringBuffer source, now)
                }
    GHC.setTargets [target]
    void $ GHC.depanal [] False
    summary <- GHC.getModSummary (GHC.mkModule G.mainUnit (GHC.mkModuleName "CheckedStorableQuery"))
    checked <- GHC.parseModule summary >>= GHC.typecheckModule
    desugared <- GHC.desugarModule checked
    let program = G.mg_binds (GHC.dm_core_module desugared)
    (owner, _) <- liftIO $ binding "query" program
    (refined, measures, sources) <- liftIO $ inputs program
    environment <- GHC.getSession
    let (global, _) = GHC.tm_internals_ checked
        location = G.mkRealSrcLoc (G.fsLit "CheckedStorableQuery.hs") 1 1
        input = G.mkRdrUnqual (G.mkVarOcc "input")
        body = G.mkHsLam (G.noLocA [G.nlVarPat input]) (G.nlHsVar (G.mkRdrUnqual (G.mkDataOcc "True")))
    captured <- liftIO $ newIORef Nothing
    let Just (integerConstructor, _) = G.splitTyConApp_maybe G.integerTy
        embeddings = F.tceInsert integerConstructor F.FInt F.WithArgs (F.tceInsert G.boolTyCon F.boolSort F.WithArgs (F.tceInsert G.intTyCon F.FInt F.WithArgs mempty))
        collect _ core ty _ = liftIO $ writeIORef captured (Just (ty, core))
    (_, result) <- liftIO $ Tc.initTcWithGbl environment global (G.mkRealSrcSpan location location) $ do
        _ <- GM.elabRnExprWithType body (G.varType owner)
        elaborateSpecTypeWithPrimitives
            False
            (FC.ElabFlags False False)
            Nothing
            embeddings
            measures
            []
            []
            sources
            []
            collect
            (\logicalEmbeddings definitions core -> either throw id (Logic.runToLogic mempty logicalEmbeddings mempty mempty defConfig (\message -> ErrOther G.noSrcSpan (fromString message)) (Logic.coreToLogicWithDefinitions definitions core)))
            refined
    liftIO $ case result of
        Nothing -> assertFailure "query elaboration failed" >> fail "query elaboration"
        Just readback -> do
            (source, core) <- readIORef captured >>= maybe (assertFailure "query not collected" >> fail "query collection") pure
            pure (readback, source, core)
