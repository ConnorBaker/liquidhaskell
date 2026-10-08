{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--diff"     @-}

module Language.Haskell.Liquid.Liquid (
   -- * Checking a single module
    checkTargetInfo
  ) where

import           Prelude hiding (error)
import qualified Control.Exception as Ex
import qualified Data.HashSet as S
import           Text.PrettyPrint.HughesPJ hiding ((<>))
import           Control.Monad (when)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Mb
import qualified Data.List  as L
import qualified Data.Graph as Graph
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import           Language.Haskell.Liquid.Misc
import qualified Language.Fixpoint.Misc as F
import           Language.Fixpoint.Solver
import qualified Language.Fixpoint.Horn.Info as Horn
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.GHC.Misc (showCBs, ignoreCoreBinds) -- howPpr)
import qualified Language.Haskell.Liquid.Bare.Measure as BareMeasure
import qualified Language.Haskell.Liquid.Bare as Bare
import           Language.Haskell.Liquid.Bare.DataType (dataConMap)
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as CoreToLogic
import qualified Language.Haskell.Liquid.Measure as Measure
import           Language.Haskell.Liquid.Types.Names (lhNameToResolvedSymbol, makeGHCLHNameLocatedFromId)
import           Language.Haskell.Liquid.Types.RTypeOp (foldReft)
import           Language.Haskell.Liquid.Constraint.Publication
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.Init (defaultTopVars, initCGI, prepareDefaultTypes)
import           Language.Haskell.Liquid.Constraint.Qualifier (giQuals)
import qualified Language.Fixpoint.Types.Config as FC
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.UX.Annotate (mkOutput)
import qualified Language.Haskell.Liquid.Termination.Structural as ST
import qualified Language.Haskell.Liquid.GHC.Misc          as GM
import           Liquid.GHC.API as GHC hiding (text, vcat, ($+$), (<+>))
import Language.Haskell.Liquid.Types.RType (SpecType, LocSpecType, RTypeBV (..))

-- RefCore annotations and complete raw publication evidence are separate
-- from the reported expected-failure result.
--------------------------------------------------------------------------------
checkTargetInfo :: TargetInfo -> IO (Output Doc, AnnInfo SpecType, Maybe PublicationCheck)
--------------------------------------------------------------------------------
checkTargetInfo info = do
  (out, infTypes, publication) <- check
  when (diffcheck cfg && not (compileSpec cfg)) $ DC.saveResult tgt out
  pure (out, infTypes, publication)
  where
    check :: IO (Output Doc, AnnInfo SpecType, Maybe PublicationCheck)
    check
      | compileSpec cfg = do
          -- donePhase Loud "Only compiling specifications [skipping verification]"
          pure (mempty{o_result = F.Safe mempty}, mempty, Nothing)
      | otherwise = do
          when (loggingVerbosity cfg == Normal) $ do
            F.donePhase F.Loud "Extracted Core using GHC"
            F.donePhase F.Loud "Transformed Core"
          when (loggingVerbosity cfg == Loud) $ do
            F.donePhase F.Loud "transformRecExpr-1773-hoho"
            putStrLn "*************** Transform Rec Expr CoreBinds *****************"
            putStrLn $ showCBs (untidyCore cfg) cbs'
          edcs <- newPrune cfg cbs' tgt info
          liquidQueries info edcs

    cfg :: Config
    cfg  = getConfig info

    tgt :: FilePath
    tgt  = giTarget (giSrc info)

    cbs' :: [CoreBind]
    cbs' = giCbs (giSrc info)

newPrune :: Config -> [CoreBind] -> FilePath -> TargetInfo -> IO (Either [CoreBind] [DC.DiffCheck])
newPrune cfg cbs tgt info
  | not (null vs) = return . Right $ [DC.thin cbs sp vs]
  | timeBinds cfg = return . Right $ [DC.thin cbs sp [v] | v <- expVars]
  | diffcheck cfg = maybeEither cbs <$> DC.slice tgt cbs sp
  | otherwise     = return $ Left (ignoreCoreBinds ignores cbs)
  where
    ignores       = gsIgnoreVars (gsVars sp)
    vs            = gsTgtVars    (gsVars sp)
    sp            = giSpec       info
    expVars       = exportedVars (giSrc info)

exportedVars :: TargetSrc -> [Var]
exportedVars src = filter (isExportedVar src) (giDefVars src)

maybeEither :: a -> Maybe b -> Either a [b]
maybeEither d Nothing  = Left d
maybeEither _ (Just x) = Right [x]

liquidQueries :: TargetInfo -> Either [CoreBind] [DC.DiffCheck] -> IO (Output Doc, AnnInfo SpecType, Maybe PublicationCheck)
liquidQueries info (Left cbs') = liquidQuery info (Left cbs')
liquidQueries info (Right dcs) = do
  results <- mapM (liquidQuery info . Right) dcs
  let (out, types) = mconcat [(result, annotations) | (result, annotations, _) <- results]
  -- Sliced/reused evidence reports normally, but cannot certify a library.
  pure (out, types, Nothing)

liquidQuery :: TargetInfo -> Either [CoreBind] DC.DiffCheck -> IO (Output Doc, AnnInfo SpecType, Maybe PublicationCheck)
liquidQuery info edc = do
  let names = either (const Nothing) (Just . map show . DC.checkedVars) edc
  let oldOut = either (const mempty) DC.oldOutput edc
  let info1 = either (const info) (\z -> info{giSpec = DC.newSpec z}) edc
  let cbs'' = either id DC.newBinds edc
  let info2 = info1{giSrc = (giSrc info1){giCbs = cbs''}}
  let info3 = updTargetInfoTermVars info2
  (out, types, publication) <- timedAction names $ checkSourceTarget info3
  pure (mappend oldOut out{o_vars = names}, types, publication)

-- Source judgments compose in proof-dependency order, including guarded Core
-- recursion. Consumer coupling alone does not create recursive proof authority.
-- Cyclic proof dependencies and source equations retain admission boundaries;
-- no judgment may borrow its own equations before they are established.
data SourceObligation
  = IndependentBodyAndFormation
  | AuthoredBody
  | AuthoredBodyAndFormation
  deriving (Eq)

checkSourceTarget :: TargetInfo -> IO (Output Doc, AnnInfo SpecType, Maybe PublicationCheck)
checkSourceTarget info = do
  -- Compatibility cannot borrow consumer postconditions whose use of an
  -- instance is justified by that very compatibility obligation.
  initial <- query ".compatibility" [] S.empty [] IndependentBodyAndFormation False
  (out, types, publication) <-
    checkGroups initial [] S.empty (proofGroups sourceInfo)
  let checkedOwners = S.fromList (letVars (giCbs (giSrc sourceInfo)))
      unowned = filter (not . (`S.member` checkedOwners) . F.val) (S.toList (gsFail (gsTerm (giSpec info))))
      complete = out{o_result = o_result out `addErrors` makeFailErrors unowned []}
  pure (complete, types, Just publication)
 where
  expected = S.map F.val (gsFail (gsTerm (giSpec info)))
  sourceInfo = info{giSrc = (giSrc info){giCbs = ignoreCoreBinds (gsIgnoreVars (gsVars (giSpec info))) (giCbs (giSrc info))}}
  authoredInitializer = initCGI (getConfig info) info
  sourceInitializer = initCGI (getConfig sourceInfo) sourceInfo
  authoredDefaultTypes = defaultTypes info
  sourceDefaultTypes = defaultTypes sourceInfo

  -- stageInfo changes obligations, never giImpVars or gsDataConIds. Keep the
  -- native declaration inventories with their producer, not with each query.
  defaultTypes target =
      let names = gsName (giSpec target)
       in prepareDefaultTypes
              (gsTyconEnv names)
              (gsTcEmbeds names)
              (giImpVars (giSrc target))
              (gsDataConIds names)
  local =
    S.fromList (giDefVars (giSrc info) ++ letVars (giCbs (giSrc info)))
      `S.difference` gsIgnoreVars (gsVars (giSpec info))

  checkGroups (initial, _) callables available groups
    | not (isSafe initial) = pure initial
    | otherwise = go initial callables available (zip [0 :: Int ..] groups)

  -- Each checked group establishes its callable only after its own body
  -- succeeds. The same ordered cut governs successful and failed claims.
  go result callables available [] =
    (result <>) . fst <$> query ".admission" callables available [] IndependentBodyAndFormation True
  go result callables available ((number, component) : groups)
    | Just ordered <- directGroup component = do
        (body, established) <- query checking callables available ordered AuthoredBodyAndFormation False
        let checked = result <> body
        if isSafe body
          then go checked (callables ++ established) available' groups
          else do
            -- A rejected interface cannot be used by downstream diagnostics.
            -- Infer an independent callable only when recovery needs one.
            (admission, inferred) <- query admissionName callables available group IndependentBodyAndFormation False
            if isSafe admission
              then go (checked <> admission) (callables ++ inferred) available' groups
              else pure (checked <> admission)
    | otherwise = do
        (admission, inferred) <- query admissionName callables available group IndependentBodyAndFormation False
        let admitted = result <> admission
        if not (isSafe admission)
          then pure admitted
          else do
            let assumed = callables ++ filter ((`S.member` expected) . fst) inferred
            (body, established) <- query checking assumed available' group AuthoredBody False
            -- A rejected claim stays an error. Continue diagnostics using the
            -- independently checked callable, never the rejected postcondition.
            let reusable = if isSafe body then established else inferred
            go (admitted <> body) (callables ++ reusable) available' groups
   where
    group = Graph.flattenSCC (fst component)
    available' = available `S.union` S.fromList (concatMap bindersOf group)
    admissionName = ".admission." ++ show number
    checking = ".checking." ++ show number

  directGroup (Graph.AcyclicSCC cb@(NonRec owner _), _)
    | owner `S.member` defaults || maybe False (all (not . hasHole) . F.val) (HashMap.lookup owner asserted)
    , all (not . (`S.member` expected)) (letVars cb) =
        Just [cb]
  directGroup (_, Just ordered)
    | all (not . (`S.member` expected)) owners
    , all (not . (`S.member` sourceFacts) . F.symbol) owners =
        Just ordered
   where
    owners = letVars ordered
  directGroup _ = Nothing

  -- A complete checking target needs no independently inferred result.
  -- Explicit assumptions retain their existing trust interpretation.
  signatures = gsSig (giSpec info)
  asserted = checkingSignatures signatures{gsAsmSigs = [], gsRefSigs = []}
  defaults = S.fromList (defaultTopVars info)

  -- These are the authority-bearing fields filtered by stageInfo, not the
  -- logical sort inventory gsMeas. Keep their admission boundary unchanged.
  sourceFacts =
    S.unions
      [ S.fromList (F.symbol . fst <$> gsRefSigs signatures)
      , S.fromList [F.symbol owner | (Just owner, _) <- gsInvariants dat]
      , S.fromList [lhNameToResolvedSymbol (F.val (msName measure)) | measure <- gsMeasures dat]
      , S.fromList (F.eqName <$> gsMyAxioms refl)
      , S.fromList [F.symbol owner | (owner, _, _) <- gsHAxioms refl]
      , S.map (F.symbol . F.val) (gsRewrites refl)
      , S.fromList (F.symbol <$> concat (HashMap.elems (gsRewritesWith refl)))
      ]
   where
    dat = gsData (giSpec info)
    refl = gsRefl (giSpec info)

  isSafe (out, _, _) = case o_result out of
    F.Safe _ -> True
    _ -> False

  -- Ordinary source checking retains its existing qualifier policy. Admission
  -- additionally mines candidates from its own body/formation/truth constraints;
  -- neither candidate source changes which predicates are assumptions or goals.
  query suffix callables available group obligation bodyless = do
      let stage = stageInfo callables available group obligation bodyless
          initialize = if obligation == IndependentBodyAndFormation then sourceInitializer else authoredInitializer
          schemas = if obligation == IndependentBodyAndFormation then sourceDefaultTypes else authoredDefaultTypes
          (prepared, cgi) = generateConstraints initialize schemas callables stage group
          spec = giSpec stage
          enriched
              | obligation == AuthoredBody = stage
              | otherwise = stage{giSpec = spec{gsQual = (gsQual spec){gsQualifiers = fixedQualifiers (fEnv cgi)}}}
          rewrites =
              Mb.mapMaybe
                  (admittedSignature (HashMap.fromList callables) (S.map F.val (gsFail (gsTerm spec))))
                  (gsTySigs (gsSig spec) ++ gsAsmSigs (gsSig spec))
      when False (dumpCs cgi)
      original <- cgInfoFInfo rewrites enriched cgi
      let cfg = getConfig enriched
          fcfg = fixConfig (giTarget (giSrc info) ++ suffix) cfg
          scraping = if obligation == AuthoredBody then FC.No else FC.Both
          finfo = original{F.quals = F.sortNub (giQuals enriched (fEnv cgi) ++ Horn.scrapeFInfo fcfg scraping original)}
      F.Result{resStatus = r0, resSolution = solCuts, resNonCutsSolution = solNonCuts, resScopes = scopes} <- solve fcfg finfo
      let rawResult = (ci_var . snd <$> r0) `addErrors` (Nothing <$ logErrors cgi)
          sol = HashMap.union (HashMap.map F.Delayed solCuts) solNonCuts
          failBs = gsFail $ gsTerm $ giSpec enriched
          (r, rf) = splitFails (S.map val failBs) r0
          completed = do
              resErr <- traverse (\(identifier, constraint) -> (,) identifier <$> applySolution scopes sol (cinfoError constraint)) r
              let resModel_ = cidE2u cfg <$> resErr
                  resModel' =
                      resModel_
                          `addErrors` (e2u cfg <$> logErrors cgi)
                          `addErrors` makeFailErrors (S.toList failBs) rf
                          `addErrors` makeFailUseErrors (S.toList failBs) (giCbs $ giSrc enriched)
              lErrors <- traverse (applySolution scopes sol) (logErrors cgi)
              let resModel = resModel' `addErrors` (e2u cfg <$> lErrors)
              -- Only authored checking describes source annotations. Independent inference
              -- establishes premises, not a competing displayed type or bottom warning.
              (out0, infTypes) <- case obligation of
                  IndependentBodyAndFormation -> Right (mempty{o_result = resModel}, mempty)
                  _ -> mkOutput cfg resModel scopes sol (annotMap cgi)
              -- Admission has no expected failures. Authored checking may reject an
              -- expected goal, but that owner's callable is already the independently
              -- checked type, never its failed claim. Every other constraint and CG
              -- error must pass, as must the complete result-scope correspondence.
              admitted <- case resModel of
                  F.Safe _ -> traverse (applySolution scopes sol) prepared
                  _ -> Right []
              pure ((out0{o_vars = Nothing, o_result = resModel}, infTypes, rawResult), admitted)
          failed diagnostic =
              let failure = F.Crash [(ErrOther GHC.noSrcSpan (text diagnostic), Nothing)] diagnostic
               in ((mempty{o_vars = Nothing, o_result = failure}, mempty, F.Crash [] diagnostic), [])
      pure (either failed id completed)

  stageInfo callables available group obligation bodyless =
    guardLocalMeasureEquations $
      base
        { giSpec =
            spec
              { gsSig =
                  signatures
                    { gsTySigs = selectSignatures (gsTySigs signatures)
                    , gsInSigs = selectSignatures (gsInSigs signatures)
                    , gsRefSigs = filter (visible . fst) (gsRefSigs originalSignatures)
                    , gsMethods = if preflight then gsMethods originalSignatures else filter selected (gsMethods signatures)
                    , gsRelation = if bodyless then gsRelation originalSignatures else []
                    , gsAsmRel = if bodyless then gsAsmRel originalSignatures else []
                    , gsReftChecks = if obligation == AuthoredBody then [] else filter formation (gsReftChecks originalSignatures)
                    }
              , gsData =
                  admittedData
                    { gsInvariants = filter (maybe True visible . fst) (gsInvariants admittedData)
                    , gsMeasures = filter measureVisible (gsMeasures (gsData spec))
                    }
              , gsRefl =
                  reflectionInfo
                    { gsMyAxioms = filter (symbolVisible . F.eqName) (gsMyAxioms reflectionInfo)
                    , gsHAxioms = filter (\(owner, _, _) -> visible owner) (gsHAxioms reflectionInfo)
                    , gsRewrites = S.filter (visible . F.val) (gsRewrites reflectionInfo)
                    , gsRewritesWith = fmap (filter visible) (gsRewritesWith reflectionInfo)
                    }
              , gsTerm = (gsTerm spec){gsFail = if authored then S.filter ((`S.member` owners) . F.val) (gsFail (gsTerm spec)) else S.empty}
              }
        }
   where
    authored = obligation /= IndependentBodyAndFormation
    base = if authored then info else sourceInfo
    spec = giSpec base
    admittedData = admittedInvariants callables (giSpec info)
    callableTypes = HashMap.fromListWith (flip const) callables
    originalSignatures = gsSig (giSpec info)
    signatures = originalSignatures{gsTySigs = map declared (gsTySigs originalSignatures ++ reflectionTargets)}

    -- Hiding a source equation must not discard its input domain. Check that
    -- domain with an independent result before the equation becomes available.
    -- Existing checking targets retain their ordinary precedence.
    reflectionTargets =
      [ signature
      | not authored
      , signature@(owner, _) <- gsRefSigs originalSignatures
      , owner `S.member` local
      , not (owner `S.member` checkingOwners)
      ]
    checkingOwners = HashMap.keysSet (checkingSignatures originalSignatures{gsRefSigs = []})
    declared (owner, signature)
      | not authored && owner `S.member` local = (owner, independentResult <$> signature)
      | otherwise = (owner, signature)
    reflectionInfo = gsRefl (giSpec info)
    owners = S.fromList (letVars group)
    symbols = S.map F.symbol available
    localSymbols = S.map F.symbol local
    preflight = null group && not bodyless
    selected (owner, _) = owner `S.member` owners || not (owner `S.member` local)
    selectSignatures = Mb.mapMaybe selectSignature
    selectSignature candidate@(owner, location)
      | selected candidate = Just candidate
      | Just ty <- HashMap.lookup owner callableTypes = Just (owner, ty <$ location)
      | otherwise = Nothing
    visible owner = not (owner `S.member` local) || owner `S.member` available
    symbolVisible name = not (name `S.member` localSymbols) || name `S.member` symbols
    formation check
      | bodyless = not (refinementCheckOwner check `S.member` local)
      | otherwise = refinementCheckOwner check `S.member` owners
    measureVisible measure =
      let name = lhNameToResolvedSymbol (F.val (msName measure))
       in symbolVisible name

  -- Force ordinary signature scraping, including reflected signatures.
  -- This separate view is used ONLY to generate candidate predicates.
  fixedQualifiers :: F.SEnv F.Sort -> [F.Qualifier]
  fixedQualifiers = giQuals qualifierInfo

  qualifierInfo :: TargetInfo
  qualifierInfo =
    info
      { giSpec =
          (giSpec info)
            { gsConfig = (getConfig info){eliminate = FC.None}
            , gsRefl = (gsRefl (giSpec info)){gsReflects = []}
            }
      }

-- Checking goals remain authored. Reusable contract projections instead use
-- the established callable, including measure invariants and rewrite theorems.
-- This also preserves honest diagnostic recovery after a rejected claim.
admittedInvariants :: [(Var, SpecType)] -> TargetSpec -> GhcSpecData
admittedInvariants admitted spec =
    dat
        { gsInvariants = invariants
        , gsUnsorted = gsUnsorted dat ++ Mb.catMaybes templates
        }
  where
    dat = gsData spec
    expected = S.map F.val (gsFail (gsTerm spec))
    types = HashMap.fromList admitted
    signature = admittedSignature types expected
    invariant :: (Maybe Var, LocSpecType) -> Maybe ((Maybe Var, LocSpecType), Maybe UnSortedExpr)
    invariant (Just owner, location)
        | owner `S.member` expected || owner `HashMap.member` types = do
            admittedType <- signature (owner, location)
            pure (Bare.measureTypeToInv (makeGHCLHNameLocatedFromId owner, admittedType))
    invariant candidate = Just (candidate, Nothing)
    (invariants, templates) = unzip (Mb.mapMaybe invariant (gsInvariants dat))

-- A proved callable, never its rejected checking goal, supplies a reusable
-- invariant or rewrite. The source declaration retains its own location.
admittedSignature :: HashMap.HashMap Var SpecType -> S.HashSet Var -> (Var, LocSpecType) -> Maybe (Var, LocSpecType)
admittedSignature types expected candidate@(owner, location)
  | Just ty <- HashMap.lookup owner types = Just (owner, ty <$ location)
  | owner `S.member` expected = Nothing
  | otherwise = Just candidate

-- A fixed checking interface permits separate inference. Without one, keep
-- the definition and all its consumers in the same query: its input domain
-- is constrained by those consumers. Retain a topological order when the
-- original proof dependencies are acyclic, before adding consumer coupling.
-- Core binding kinds and the independent path's source order are unchanged.
proofGroups :: TargetInfo -> [(Graph.SCC CoreBind, Maybe [CoreBind])]
proofGroups info = map ordered (Graph.stronglyConnComp vertices)
  where
    spec = giSpec info
    numbered = zip [0 :: Int ..] (giCbs (giSrc info))
    owners =
        HashMap.fromList
            [ (F.symbol owner, key)
            | (key, cb) <- numbered
            , owner <- letVars cb
            ]
    interfaces =
        S.fromList $
            map F.symbol (defaultTopVars info)
                ++ [ F.symbol owner
                   | (owner, ty) <- HashMap.toList (checkingSignatures (gsSig spec))
                   , all (not . hasHole) (F.val ty)
                   ]
    consumers =
        HashMap.fromListWith
            (++)
            [ (dependency, [key])
            | (key, _, dependencies') <- indexed
            , (symbol, dependency) <- dependencies'
            , not (symbol `S.member` interfaces)
            ]
    indexed = [(key, cb, dependencies key cb) | (key, cb) <- numbered]
    vertices =
        [ ((key, cb, dependencies'), key, dependencies' ++ HashMap.lookupDefault [] key consumers)
        | (key, cb, edges) <- indexed
        , let dependencies' = map snd edges
        ]
    ordered component = (sourceOrder component, traverse acyclic proofOrder)
      where
        proofOrder =
            Graph.stronglyConnComp
                [(cb, key, dependencies') | (key, cb, dependencies') <- Graph.flattenSCC component]
    sourceOrder (Graph.AcyclicSCC (_, cb, _)) = Graph.AcyclicSCC cb
    sourceOrder (Graph.CyclicSCC cbs) =
        Graph.CyclicSCC [cb | (_, cb, _) <- L.sortOn (\(key, _, _) -> key) cbs]
    acyclic (Graph.AcyclicSCC cb) = Just cb
    acyclic Graph.CyclicSCC{} = Nothing
    dependencies :: Int -> CoreBind -> [(F.Symbol, Int)]
    dependencies key cb =
        [ (symbol, key)
        | symbol <- map F.symbol (freeVars S.empty cb) ++ HashMap.lookupDefault [] key declarations
        , Just key <- [HashMap.lookup symbol owners]
        ]
    -- A lexical owner can occur in more than one transformed Core group.
    -- Membership is a set within each group, just like the original row filter;
    -- retaining all groups preserves duplicated case paths without duplicating
    -- a declaration merely because its owner occurs twice in one group.
    ownerGroups =
        HashMap.fromListWith
            (++)
            [(owner, [key]) | (key, cb) <- numbered, owner <- S.toList (S.fromList (letVars cb))]
    -- Distribute the ordered declaration rows once. Stable concatenation keeps
    -- every group's original symbol order and multiplicity before projection
    -- through the existing symbol-to-group map.
    declarations =
        HashMap.map (concat . reverse) $
            HashMap.fromListWith
                (++)
                [(key, [symbols]) | (owner, symbols) <- logical ++ formation, key <- HashMap.lookupDefault [] owner ownerGroups]
    -- Refinement checks are ordinary Core consumers of their free source
    -- definitions. Their predicates may already have been projected to holes
    -- in this phase's signatures, so the actual generated Core owns these
    -- dependencies. Include nested lexical owners without moving their checks
    -- out of the source environment in which they are discharged.
    formation =
        [ (refinementCheckOwner check, map F.symbol (freeVars S.empty (refinementCheckExpr check)))
        | check <- gsReftChecks (gsSig spec)
        ]
    logical =
        [ ( owner
          , foldReft
                False
                (\_ refinement symbols -> S.toList (F.syms refinement) ++ symbols)
                []
                (F.val ty)
          )
        | (owner, ty) <-
            gsTySigs (gsSig spec)
                ++ gsAsmSigs (gsSig spec)
                ++ gsRefSigs (gsSig spec)
                ++ gsInSigs (gsSig spec)
                ++ [(owner, ty) | (owner, method) <- gsMethods (gsSig spec), Just ty <- [getMethodType method]]
        ]
            ++ [ (owner, concatMap (S.toList . F.syms . F.val) metrics)
               | (owner, _, metrics) <- gsTexprs (gsSig spec)
               ]

-- Match varTemplate's asserted/internal/assumed precedence. A lower-priority
-- complete signature must not hide holes in the actual checking target.
checkingSignatures :: GhcSpecSig -> HashMap.HashMap Var LocSpecType
checkingSignatures signatures =
    HashMap.unions
        [ HashMap.fromList (gsTySigs signatures ++ [(owner, ty) | (owner, method) <- gsMethods signatures, Just ty <- [getMethodType method]])
        , HashMap.fromList (gsInSigs signatures)
        , HashMap.fromList (gsAsmSigs signatures ++ gsRefSigs signatures)
        ]

-- Constructor refinements carry lifted measure equations even when PLE is off.
-- During independent checking these are unproved source facts, not primitives.
localMeasureTypes :: TargetInfo -> HashMap.HashMap F.Symbol SpecType
localMeasureTypes info = HashMap.unions
  [ selected gsTySigs, selected gsInSigs
  , HashMap.fromList [(F.symbol owner, ofType (varType owner))
                    | owner <- S.toList local, F.symbol owner `S.member` measures] ]
  where
    spec = giSpec info
    local = S.fromList (giDefVars (giSrc info))
      `S.difference` gsIgnoreVars (gsVars spec)
    measures = S.fromList
      [ lhNameToResolvedSymbol (F.val (msName measure))
      | measure <- gsMeasures (gsData spec), msKind measure == MsLifted ]
    selected :: (GhcSpecSig -> [(Var, LocSpecType)]) -> HashMap.HashMap F.Symbol SpecType
    selected field = HashMap.fromList
      [ (F.symbol owner, F.val signature)
      | (owner, signature) <- field (gsSig spec)
      , owner `S.member` local, F.symbol owner `S.member` measures ]

-- Local and imported measures use the same input-domain projection and
-- constructor equation interpretation before meeting authored constructor types.
guardLocalMeasureEquations :: TargetInfo -> TargetInfo
guardLocalMeasureEquations info = info { giSpec = spec
  { gsData = dat { gsCtors = HashMap.toList combined } } }
  where
    spec = giSpec info
    dat = gsData spec
    facts = [(owner, ty <$ GM.locNamedThing owner) | (owner, ty) <- localMeasureEquations info]
    combined = HashMap.fromListWith combine (gsCtors dat ++ facts)
    combine :: LocSpecType -> LocSpecType -> LocSpecType
    combine left right = (Prelude.<> F.val right) <$> left

localMeasureEquations :: TargetInfo -> [(Var, SpecType)]
localMeasureEquations info =
    case [(owner, sort) | (owner, sort) <- support, fmap F.sr_sort (F.lookupSEnv (F.symbol owner) declared) /= Just sort] of
        [] -> equations
        (owner, _) : _ -> uError (ErrOther (getSrcSpan owner) (text "Constructor interpretation requires undeclared support for" <+> F.pprint (F.symbol owner)) :: UserError)
  where
    ((equations, _), support) =
        BareMeasure.makeMeasureSpec'
            interpret
            boxes
            allowTC
            (Measure.mkMSpec' definitions)
    declared = Bare.targetSpecEnv spec
    allowTC = typeclass (getConfig info)
    spec = giSpec info
    names = gsName spec
    boxes = gsConstructorBoxes names
    interpret expression =
        either Ex.throw id $
            CoreToLogic.runToLogic
                boxes
                (gsTcEmbeds names)
                (gsLogicMap (gsRefl spec))
                (dataConMap (gsADTs names))
                (getConfig info)
                (\message -> todo Nothing ("constructor interpretation: " ++ message))
                (CoreToLogic.coreToLogic expression)
    measures = localMeasureTypes info
    local = S.fromList (map F.symbol (giDefVars (giSrc info)))
    definitions =
        [ measure{msSort = Measure.measureInputType signature}
        | measure <- gsMeasures (gsData (giSpec info))
        , msKind measure == MsLifted
        , let owner = lhNameToResolvedSymbol (F.val (msName measure))
        , Just signature <-
            [if owner `S.member` local then HashMap.lookup owner measures else Just (msSort measure)]
        ]

independentResult :: SpecType -> SpecType
independentResult (RAllT a t _) = RAllT a (independentResult t) mempty
independentResult (RAllP p t) = RAllP p (independentResult t)
independentResult (RFun x i input result _) =
  RFun x i input (independentResult result) mempty
independentResult t = fmap (const (uTop (F.Reft (F.vv_, hole)))) t


updTargetInfoTermVars    :: TargetInfo -> TargetInfo
updTargetInfoTermVars i  = updInfo i  (ST.terminationVars i)
  where
    updInfo   info vs = info { giSpec = updSpec   (giSpec info) vs }
    updSpec   sp   vs = sp   { gsTerm = updSpTerm (gsTerm sp)   vs }
    updSpTerm gsT  vs = gsT  { gsNonStTerm = S.fromList vs         }

dumpCs :: CGInfo -> IO ()
dumpCs cgi = do
  putStrLn "***************************** SubCs *******************************"
  putStrLn $ render $ pprintMany (hsCs cgi)
  putStrLn "***************************** FixCs *******************************"
  putStrLn $ render $ pprintMany (fixCs cgi)
  putStrLn "***************************** WfCs ********************************"
  putStrLn $ render $ pprintMany (hsWfs cgi)

pprintMany :: (PPrint a) => [a] -> Doc
pprintMany xs = vcat [ F.pprint x $+$ text " " | x <- xs ]

e2u :: Config -> Error -> UserError
e2u cfg = fmap F.pprint . tidyError cfg

cidE2u :: Config -> (Integer, Error) -> UserError
cidE2u cfg (subcId, e) =
  let e' = attachSubcId e
   in fmap F.pprint (tidyError cfg e')
  where
    attachSubcId es@ErrSubType{}      = es { cid = Just subcId }
    attachSubcId es@ErrSubTypeModel{} = es { cid = Just subcId }
    attachSubcId es@ErrAssType{}      = es { cid = Just subcId }
    attachSubcId es = es

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi


makeFailUseErrors :: [F.Located Var] -> [CoreBind] -> [UserError]
makeFailUseErrors fbs cbs = [ mkError x bs | x <- fbs
                                          , let bs = clients (val x)
                                          , not (null bs) ]
  where
    mkError x bs = ErrFailUsed (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (pprint <$> bs)
    clients x    = map fst $ filter (elem x . snd) allClients

    allClients = concatMap go cbs

    go :: CoreBind -> [(Var,[Var])]
    go (NonRec x e) = [(x, readVars e)]
    go (Rec xes)    = [(x,cls) | x <- map fst xes] where cls = concatMap (readVars . snd) xes

makeFailErrors :: [F.Located Var] -> [Cinfo] -> [UserError]
makeFailErrors bs cis = [ mkError x | x <- bs, notElem (val x) vs ]
  where
    mkError  x = ErrFail (GM.sourcePosSrcSpan $ loc x) (pprint $ val x)
    vs         = Mb.mapMaybe ci_var cis

splitFails :: S.HashSet Var -> F.FixResult (a, Cinfo) -> (F.FixResult (a, Cinfo),  [Cinfo])
splitFails _ r@(F.Crash _ _) = (r,mempty)
splitFails _ r@(F.Safe _)    = (r,mempty)
splitFails fs (F.Unsafe s xs)  = (mkRes r, snd <$> rfails)
  where
    (rfails,r) = L.partition (Mb.maybe False (`S.member` fs) . ci_var . snd) xs
    mkRes [] = F.Safe s
    mkRes ys = F.Unsafe s ys
