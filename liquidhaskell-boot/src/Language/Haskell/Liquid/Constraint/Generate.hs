{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Generate ( ConstraintObligations (..), generateConstraints, caseEnv, consE ) where

import           Prelude                                       hiding (error)
import           GHC.Stack ( CallStack )
import           Liquid.GHC.API               as Ghc hiding ( panic
                                                            , (<+>)
                                                            , text
                                                            , vcat
                                                            )
import qualified Language.Haskell.Liquid.GHC.Resugar           as Rs
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import qualified Language.Haskell.Liquid.GHC.Misc              as GM -- ( isInternal, collectArguments, tickSrcSpan, showPpr )
import Language.Haskell.Liquid.GHC.PrimitiveContract (primitiveContract, wiredBoolean)
import Text.PrettyPrint.HughesPJ ( text )
import           Control.Monad ( foldM, forM, forM_, when, void, unless, msum, guard)
import           Control.Monad.State
import           Data.Bifunctor                                (first)
import           Data.Maybe                                    (fromMaybe, isJust)
import           Data.Either.Extra                             (eitherToMaybe)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import qualified Data.Functor.Identity
import Language.Fixpoint.Misc (errorP, safeZip )
import           Language.Fixpoint.Types.Visitor
import qualified Language.Fixpoint.Types                       as F
import Language.Fixpoint.Smt.Theories ()
import qualified Language.Fixpoint.Types.Visitor               as F
import           Language.Haskell.Liquid.Constraint.Fresh ( addKuts, freshTyType, trueTy )
import           Language.Haskell.Liquid.Constraint.Init (DefaultTypes, initEnv)
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Monad
import Language.Haskell.Liquid.Constraint.Split ( splitC, splitCheckedCWith, bsplitC, splitW )
import GHC.Core.SimpleOpt (SimpleOpts (so_eta_red), defaultSimpleOpts, simpleOptExprNoInline)
import           Language.Haskell.Liquid.Constraint.Relational (consAssmRel, consRelTop)
import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types.Literals
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types hiding (binds)
import Language.Haskell.Liquid.Types.Visitors (CBVisitable (letVars))
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Constraint ( addConstraints )
import           Language.Haskell.Liquid.Constraint.Template
import           Language.Haskell.Liquid.Constraint.Termination
import           Language.Haskell.Liquid.Constraint.RewriteCase
import qualified Language.Haskell.Liquid.Measure as Measure
import Language.Haskell.Liquid.Transforms.CoreToLogic (LogicM, NewtypeCoercion (..), castToLg, coreToLogic, newtypeCoercionDataCon, runToLogic, weakenResult)
import           Language.Haskell.Liquid.Bare.DataType (dataConMap, makeDataConChecker, makeDataConSelector)
import           Language.Haskell.Liquid.Bare.Misc (simpleSymbolVar)
import Language.Haskell.Liquid.Bare.Class (instanceDictionaryOwners)
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Core (mkVarApps)
import Language.Haskell.Liquid.UX.Config (
  Config (
    checkDerived,
    dependantCase,
    extensionality,
    nopolyinfer,
    rankNTypes,
    smtsolver,
    targetIntBits,
    targetMaxSmallTag,
    typeclass,
    warnOnTermHoles
  ),
  HasConfig (getConfig),
  adtFlag,
  totalityCheck,
  higherOrderFlag,
  patternFlag,
  warnOnTermHoles,
 )
import qualified GHC.Core.Coercion as Co
import GHC.Builtin.Names (gHC_INTERNAL_ERR)
import GHC.Core.TyCo.Rep (Coercion (CoVarCo, TransCo))
import qualified GHC.Data.Strict as Strict
import GHC.Types.Unique.Set (nonDetEltsUniqSet)
import GHC.Core.Type (getTyVar_maybe)

-- Note [Term holes]
--
-- The term-hole implementation in this module is a small, opt-in pipeline that
-- is only active when @warnOnTermHoles@ is enabled.
--
-- The thesis motivating this feature chose constraint generation as the hook for
-- hole support because this is the first phase where LiquidHaskell already knows
-- the refined types and local environment that make a warning actionable. An
-- earlier location-based approach would have been more modular, but the needed
-- query from source locations back into constraint generation was not feasible.
--
-- The implementation also uses a stable hole naming convention, recognized by
-- 'isVarHole', instead of depending on GHC surface syntax alone. This keeps the
-- matching logic local to Core while reducing the amount of desugaring detail we
-- have to reconstruct.
--
-- 1. We detect direct occurrences of a typed hole with 'detectTypedHole', which
--    peels away ticks via 'stripTicks', recovers the hole source span with
--    'lastTick', and recognizes @hole@ binders with 'isVarHole'. We need this
--    normalization-aware detection because holes can appear under GHC-introduced
--    @App@ and @Tick@ nodes, and the warning should still point at the original
--    source span.
--
-- 2. We remember hole-shaped let-bindings in 'consCB''s local @checkLetHole@
--    helper. That helper records which ANF binder names a hole by calling
--    'linkANFToHole'. This step is needed because LiquidHaskell's ANF
--    normalization can float a hole into a fresh @let@ binder, and later useful
--    constraints may mention only that ANF name instead of the original hole.
--
-- 3. We record the type and environment of each direct hole occurrence while
--    generating constraints. In checking mode, 'cconsE''s local @maybeAddHole@
--    stores the expected type with 'addHole'. In synthesis mode, 'consE''s
--    local @synthesizeWithHole@ first synthesizes the application's type and
--    then stores that synthesized type with 'addHole'. We need both sites:
--    checking gives the expected type when one is available, while synthesis
--    covers cases like applications where checking alone would only report an
--    uninformative base type for the hole.
--
-- 4. We attach ANF expressions that participate in a hole by running
--    'checkANFHoleInExpr' from 'cconsE' and from the application case of
--    'consE'. That helper walks the expression with 'collectVars', resolves any
--    binder previously linked by 'linkANFToHole' through 'isANFInHole', and
--    saves the expression/type pair with 'addHoleANF'. This is what recovers the
--    surrounding refined constraints that users actually need when the hole sits
--    inside a larger normalized expression.
--
-- 5. After constraint generation finishes, 'consAct' calls
--    'emitConsolidatedHoleWarnings'. It merges the stored hole metadata with the
--    collected ANF expressions and emits one 'ErrHole' warning per hole, using
--    the environment captured by 'addHole' so the warning reports the local
--    typing context that was in scope at the hole. Delaying emission until the
--    end is important: only then do we have the direct hole information, the ANF
--    links, and the extra constraints together in one place.
--
-- Term holes were developed during the Master's thesis
--
-- Enhancing Proof Development in LiquidHaskell: Implementation and Evaluation of Typed Holes
-- MATHEUS DE SOUSA BERNARDO
-- Chalmers University of Technology, 2025
--
-- https://odr.chalmers.se/server/api/core/bitstreams/640ee29b-b13a-44d5-9e20-200a91a11021/content


-- Note [Newtype checking]
--
-- Unlike regular data types, newtypes do not show up in core with data
-- constructors and selectors. Instead, they are represented with coercions
-- between the newtype and its representation type.
--
-- We make sure to interpret these coercions as either data constructor
-- applications or as selectors when generating constraints
-- ('castTyNewtypeWrap') and when reflecting code to the logic
-- ('Language.Haskell.Liquid.Transforms.CoreToLogic.newtypeCoercionDataCon').
--
-- Because pattern matching on newtypes is erased in core, we also need to make
-- sure that LH inserts the appropriate predicates from measures and from the
-- refinement types of the newtype's representation where there is a binding to
-- a value of a newtype. This is done with invariants
-- ('Language.Haskell.Liquid.Bare.makeNewtypeInvariants').

--------------------------------------------------------------------------------
-- | Constraint Generation: Toplevel -------------------------------------------
--------------------------------------------------------------------------------
data ConstraintObligations = ConstraintObligations
    { obligationBodies :: [CoreBind]
    , obligationMethods :: [(Var, MethodType (F.Located CheckedSpecType))]
    , obligationInterfaces :: AdmittedInterfaces
    , obligationDeclarations :: [Var]
    }

generateConstraints :: (TargetInfo -> CGInfo) -> DefaultTypes -> [(Var, SpecType)] -> TargetInfo -> ConstraintObligations -> ([(Var, SpecType)], CGInfo)
--------------------------------------------------------------------------------
generateConstraints initialize defaultTypes callables info obligations =
    {-# SCC "ConsGen" #-} runState act $ (initialize info){admittedInterfaces = obligationInterfaces obligations}
  where
    act = do
        γ <- initEnv defaultTypes callables info
        checked <- consAct γ cfg info obligations
        -- Retain the callable environment after checking, including synthesized
        -- unsigned bindings. Reuse requires the source driver's corresponding
        -- proof obligations, not merely source-position annotations. A rejected
        -- expected goal resolves to its independently checked callable instead.
        -- Generated type-representation evidence establishes only its
        -- template: its body's solved structure is no source-facing claim.
        pure
            [ (owner, ty)
            | owner <- concatMap bindersOf groups
            , let environment = if GM.isTypeRepresentationVar owner then γ else checked
            , Just ty <- [lookupREnv (F.symbol owner) (renv environment)]
            ]
    cfg = getConfig info
    groups = obligationBodies obligations

consAct :: CGEnv -> Config -> TargetInfo -> ConstraintObligations -> CG CGEnv
consAct γ cfg info obligations = do
    let sSpc = gsSig . giSpec $ info
    γ' <- foldM checkGroup γ groups
    consRefinementChecks γ' (obligationDeclarations obligations)
    requested <- gets refinementChecksByOwner
    -- An authored assumption about an imported function has no local body.
    -- Check its collected predicate in the completed module environment, using
    -- the same judgment as local declarations, without checking the assumed body.
    let localOwners = S.fromList (letVars (giCbs (giSrc info)))
        assumedOwners = S.fromList (map fst (gsAsmSigs sSpc))
    consRefinementChecks
        γ'
        [owner | owner <- M.keys requested, owner `S.member` assumedOwners, not (owner `S.member` localOwners), owner `notElem` obligationDeclarations obligations]
    visited <- gets visitedRefinementOwners
    let missingOwners = filter (not . (`S.member` visited)) (M.keys requested)
    unless (null missingOwners) $
        panic
            Nothing
            ( "Refinement formation has no checked lexical owner: "
                ++ unwords (map GM.showPpr missingOwners)
            )
    -- Relational Checking: the following only runs when the list of relational specs is not empty
    (ψ, γ'') <- foldM (consAssmRel cfg info) ([], γ') (gsAsmRel sSpc ++ gsRelation sSpc)
    mapM_ (consRelTop cfg info γ'' ψ) (gsRelation sSpc)
    -- End: Relational Checking
    classConstraints <- concat <$> mapM (consClass γ') (obligationMethods obligations)
    hcs <- gets hsCs
    fcs <- concat <$> mapM (splitC (typeclass (getConfig info))) hcs
    hws <- gets hsWfs
    fws <- concat <$> mapM splitW hws
    checkStratCtors γ sSpc
    when (warnOnTermHoles cfg) emitConsolidatedHoleWarnings
    -- Self is a constructor-field placeholder whose lexical owner is supplied
    -- by caseEnv, not a global value. Keep it in the frontend checking scope,
    -- but do not offer it as a solver constant or qualifier argument. Any
    -- residual free occurrence must fail the ordinary query scope checks.
    modify $ \st ->
        st
            { fEnv = F.deleteSEnv selfSymbol (fEnv st `mappend` feEnv (fenv γ))
            , cgLits = litEnv γ
            , cgConsts = cgConsts st `mappend` constEnv γ
            , fixCs = classConstraints ++ fcs
            , fixWfs = fws
            }
    pure γ'
  where
    groups = obligationBodies obligations
    checkGroup :: CGEnv -> CoreBind -> CG CGEnv
    checkGroup environment cb = do
        checked <- consCBTop cfg info environment cb
        consRefinementChecks checked (bindersOf cb)
        pure checked

---------------------------------

-- | Checking stratified ctors --
---------------------------------
type FExpr = F.ExprV F.Symbol
type Ctors = S.HashSet F.Symbol

checkStratCtors :: CGEnv -> GhcSpecSig -> CG ()
checkStratCtors env sSpc = do
  let ctors = S.fromList $ M.keys $ F.seBinds $ constEnv env
  let ctorRefinements = filter (isStrat . fst) $ gsTySigs sSpc
  let propOwner = lookupLogicMeasure (Ghc.mkModuleName "Language.Haskell.Liquid.ProofCombinators") "prop" (gsData $ giSpec $ cgInfo env)
  forM_ ctorRefinements $ uncurry $ checkCtor propOwner ctors
  where
    -- (Alecs): For some reason it can't see that they are the same
    -- GHC name, probably is due to some worker wrapper shenannigans
    hack = occNameString . nameOccName
    isStrat nm = hack (varName nm) `elem` map hack (gsStratCtos sSpc)

uncurryPi :: SpecType -> ([SpecType], SpecType)
uncurryPi (RFun _ _ dom cod _) = first (dom :) $ uncurryPi cod
uncurryPi rest                 = ([], rest)

getTyConName :: SpecType -> Name
getTyConName a = Ghc.tyConName $ rtc_tc $ rt_tycon a

checkCtor :: Maybe F.Symbol -> Ctors -> Var -> LocSpecType -> CG ()
checkCtor propOwner ctors name typ = do
  let loc = GM.fSrcSpan $ F.loc typ
  let (args, ret) = uncurryPi $ val typ
  -- The constuctor that we want not to appear negatively
  let tyName = getTyConName ret
  -- Its index information
  retIdx <- case getPropIndex propOwner $ ur_reft $ rt_reft ret of
    Just idx -> pure idx
    Nothing  -> uError $ ErrStratNotPropRet loc (pprint tyName) (pprint name) (F.pprint ret)
  -- For every argument of the constructor we check that all the
  -- self-refernce are refined by a "smaller" `prop` annotation
  forM_ args $ checkNg propOwner ctors loc name tyName retIdx

checkNg :: Maybe F.Symbol -> Ctors -> SrcSpan -> Var -> Name -> FExpr -> SpecType -> CG ()
checkNg propOwner ctors loc ctorName tyName retIdx = go
  where
    go :: SpecType -> CG ()
    go RVar {} = pure ()
    go RAllT { rt_ty } = go rt_ty
    go RAllP { rt_ty } = go rt_ty
    go RFun { rt_in, rt_out } = do
      go rt_in
      go rt_out
    go r@RApp { rt_tycon = RTyCon { rtc_tc }, rt_args, rt_reft } = do
      if Ghc.tyConName rtc_tc == tyName then do
          case getPropIndex propOwner $ ur_reft rt_reft of
            (Just arg) -> do
              -- We compare index information The occurrence is safe
              -- iff the index of the return type is strictly bigger
              -- than the one in negative position
              unless (isStructurallySmaller ctors arg retIdx) $ do
                uError $ ErrStratIdxNotSmall loc
                  (pprint tyName) (pprint ctorName) (F.pprint retIdx) (F.pprint arg)
            -- We don't have index information for both so we bail
            _ -> uError $ ErrStratOccProp loc (pprint tyName) (pprint ctorName) (F.pprint r)
      else do
        forM_ rt_args go
    go _ = lift $ impossible (Just loc) "checkNg unexpected type"


isStructurallySmaller :: Ctors -> FExpr -> FExpr -> Bool
isStructurallySmaller ctors l r
  -- Congruence rule
  | (F.EVar nl, argsl) <- F.splitEAppThroughECst l
  , (F.EVar nr, argsr) <- F.splitEAppThroughECst r
  , nl == nr
  , length argsl == length argsr
  , nl `elem` ctors
  = lexOrder ctors argsl argsr
  | otherwise = isSubterm ctors l r && l /= r

lexOrder :: Ctors -> [F.ExprV F.Symbol] -> [F.ExprV F.Symbol] -> Bool
lexOrder _     []     []            = False
lexOrder ctors (l:ls) (r:rs)
  | isStructurallySmaller ctors l r = True
  | l == r                          = lexOrder ctors ls rs
  | otherwise                       = False
lexOrder _ _ _ = errorP "" "lexOrder: different length lists"

isSubterm :: Ctors -> FExpr -> FExpr -> Bool
isSubterm ctors l r | l == r
                   = True
                  -- Congruence rule
                  | (F.EVar nm, args) <- F.splitEAppThroughECst r
                  , nm `elem` ctors
                  = any (isSubterm ctors l) args
                  | otherwise
                  = False

-- | Emit one warning per recorded term hole after constraint generation has
--   collected both the hole metadata and any ANF expressions linked to it.
--
-- See Note [Term holes]
emitConsolidatedHoleWarnings :: CG ()
emitConsolidatedHoleWarnings = do
  holes     <- gets hsHoles
  holeExprs <- gets hsHolesExprs

  let mergedHoles
                  = [(h
                    , holeInfo
                    , M.findWithDefault [] (h, srcSpan) holeExprs
                    )
                    | ((h, srcSpan), holeInfo) <- M.toList holes
                    ]

  forM_ mergedHoles $ \(h, holeInfo, anfs) -> do
    let γ        = snd . info $ holeInfo
    let anfs'    = map (\(v, x, t) -> (F.symbol v, x, t)) anfs
    addWarning $ ErrHole (hloc holeInfo) "hole found" (reLocal $ renv γ) (F.symbol h) (htype holeInfo) anfs'


--------------------------------------------------------------------------------
-- | Ensure that the instance type is a subtype of the class type --------------

--------------------------------------------------------------------------------

consClass :: CGEnv -> (Var, MethodType (F.Located CheckedSpecType)) -> CG [FixSubC]
consClass γ (x, mt)
    | Just ti <- tyInstance mt =
        do
            (ti', _) <- refreshArgsSubWith substCheckedType F.subst (val ti)
            (tc, _) <- refreshArgsSubWith substCheckedType F.subst $ maybe (logicalSpecType $ ofType $ varType x) val (tyClass mt)
            constraints <- splitCheckedCWith nativeRefinementLeaf (typeclass (getConfig γ)) (SubC (γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc ti))) ti' tc)
            let endpoints = fmap (fmap ordinarySpecType) mt{tyInstance = Just (F.loc ti `F.atLoc` ti'), tyClass = Just (maybe (F.loc ti) F.loc (tyClass mt) `F.atLoc` tc)}
            modify $ \state -> state{interfaceEndpoints = (x, endpoints) : interfaceEndpoints state}
            pure constraints
-- Without a refined class declaration, the public interface is Haskell's.
consClass _ _ =
    return []

-- Both concrete predicates are opened in the actual oriented split judgment.
-- In particular, no original query argument domain is replayed as a premise.
nativeRefinementLeaf :: [RPVar] -> CGEnv -> CheckedSpecType -> CheckedSpecType -> CG [FixSubC]
nativeRefinementLeaf predicates environment left right
    | Just leftRefinement <- stripRTypeBase left
    , Just rightRefinement <- stripRTypeBase right
    , not (null $ checkedPredicates leftRefinement ++ checkedPredicates rightRefinement) = do
        let root = F.reftBind $ ur_reft $ checkedOrdinary leftRefinement
            carrier = mapRBase (const mempty) (ordinarySpecType left)
            rightAtRoot = renameCheckedRoot rightRefinement root
        scoped <- environment += ("native refinement value", root, carrier)
        case alignNativeOwners scoped (checkedPredicates leftRefinement ++ checkedPredicates rightAtRoot) of
            Nothing -> ordinary
            Just owners
                | all (isJust . openNativeSignature predicates . predicateSignature) (checkedPredicates leftRefinement ++ checkedPredicates rightAtRoot) -> do
                    opened <- renameNativeEnvironment owners scoped
                    (leftEnvironment, lhsBody, lhsMeaning) <- openNativeRefinement predicates opened owners leftRefinement
                    -- A relational goal must be concrete: nested RHS KVars
                    -- are not Horn producers and cannot establish this cut.
                    unless (F.isConc lhsMeaning) $
                        panic (Just $ getLocation environment) "Native source interpretation contains an inferred predicate"
                    inferred <- freshTyType (typeclass $ getConfig leftEnvironment) LetE lhsBody (exprType lhsBody)
                    addW $ WfC leftEnvironment inferred
                    let booleanRoot = F.vv Nothing
                        -- One checking pass proves both native result facts
                        -- and their precise interpretation. The readback alone
                        -- need not expose a checked source result contract.
                        witnessed = inferred `strengthen` uTop (F.Reft (booleanRoot, F.PIff (F.EVar booleanRoot) lhsMeaning))
                    cconsE leftEnvironment lhsBody witnessed
                    witness <- freshNativeBool
                    witnessedEnvironment <- leftEnvironment += ("checked native refinement", F.symbol witness, witnessed)
                    trueEnvironment <- caseEnv witnessedEnvironment witness [DataAlt falseDataCon, DataAlt trueDataCon] (DataAlt trueDataCon) [] Nothing
                    producerRoot <- fresh
                    let action = F.mkSubst [(owner, F.EVar $ F.symbol actual) | (owner, actual) <- owners]
                        nativeRoot = maybe root F.symbol (lookup root owners)
                        membership refinement = renameReftRoot (F.subst action $ checkedLogical refinement) nativeRoot
                        leftMembership = shiftVV (carrier `strengthen` membership leftRefinement) producerRoot
                        rightMembership = carrier `strengthen` membership rightAtRoot
                        pinnedLeft = leftMembership `strengthen` uTop (F.Reft (producerRoot, F.PAtom F.Eq (F.EVar producerRoot) (F.EVar nativeRoot)))
                    -- Keep the oriented membership conclusion on the Horn
                    -- RHS. Boxing it as an input Bool would lose its producer.
                    constraints <- bsplitC trueEnvironment pinnedLeft rightMembership
                    let resident = fromMaybe (panic (Just $ getLocation environment) "Native refinement lost its value owner") (trueEnvironment ?= nativeRoot)
                    cutEnvironment <- trueEnvironment += ("checked native membership", nativeRoot, resident `strengthen` membership rightAtRoot)
                    (rightEnvironment, rhsBody, _) <- openNativeRefinement predicates cutEnvironment owners rightAtRoot{checkedLogical = mempty}
                    let target = ofType boolTy `strengthen` uTop (F.Reft (booleanRoot, F.EVar booleanRoot))
                    cconsE rightEnvironment rhsBody target
                    return constraints
            _ -> ordinary
    | otherwise = ordinary
  where
    ordinary = bsplitC environment (ordinarySpecType left) (ordinarySpecType right)

-- A logical substitution may have no native application. Only exact source
-- variable owners, with their actual nominal Gamma carriers, admit opening.
alignNativeOwners :: CGEnv -> [CheckedPredicate] -> Maybe [(F.Symbol, Id)]
alignNativeOwners environment = foldM addPredicate []
  where
    addPredicate owners predicate = foldM (addFormal predicate) owners (queryValueOwners $ predicateTelescope predicate)
    addFormal predicate owners (_, formal)
        | isCoVar formal = Nothing
        | primitiveFormal predicate formal = Just owners
        | Just (F.EVar source) <- lookup formal (predicateDefinitions predicate)
        , Just actual <- environment ?= source
        , let nominal = instantiateNativeType predicate (varType formal)
        , nominal `eqType` specTypeToQueryType actual =
            case lookup source owners of
                Just existing | varType existing `eqType` nominal -> Just owners
                Just _ -> Nothing
                Nothing | isJust (environment ?= F.symbol formal) && F.symbol formal /= source -> Nothing
                Nothing -> Just (owners ++ [(source, setVarType formal nominal)])
        | otherwise = Nothing

primitiveFormal :: CheckedPredicate -> Id -> Bool
primitiveFormal predicate formal = formal `elem` predicateLogicalParameters predicate

instantiateNativeType :: CheckedPredicate -> Type -> Type
instantiateNativeType predicate ty = substTyWith native source ty
  where
    correspondence = [(actual, mkTyVarTy owner) | (owner, image) <- queryTypeOwners (predicateTelescope predicate), Just actual <- [getTyVar_maybe image]]
    (native, source) = unzip correspondence

-- Rebuild the SAME active Horn context under one simultaneous owner action;
-- retaining old bindings plus aliases would not be native alpha conversion.
renameNativeEnvironment :: [(F.Symbol, Id)] -> CGEnv -> CG CGEnv
renameNativeEnvironment owners environment = do
    bindings <- gets binds
    renamed <- forM (F.elemsIBindEnv $ feBinds $ fenv environment) $ \key -> do
        let (owner, refinement, information) = F.lookupBindEnv key bindings
            owner' = rename owner
            refinement' = F.subst action refinement
        if owner' == owner && refinement' == refinement
            then return ((owner, F.sr_sort refinement), key)
            else state $ \current ->
                let (freshKey, updated) = F.insertBindEnv owner' refinement' information (binds current)
                 in (((owner', F.sr_sort refinement'), freshKey), current{binds = updated})
    let renamedFixpoint = insertsFEnv (initFEnv [(rename owner, sort) | (owner, sort) <- F.toListSEnv $ feEnv $ fenv environment]) renamed
    return
        environment
            { renv = renameTypes (renv environment)
            , grtys = renameTypes (grtys environment)
            , assms = renameTypes (assms environment)
            , intys = renameTypes (intys environment)
            , fenv = renamedFixpoint
            , denv = renameDictionaries (denv environment)
            , lcb = M.fromList [(rename owner, renameCore expression) | (owner, expression) <- M.toList $ lcb environment]
            , forallcb = M.fromList [(renameId owner, F.subst action expression) | (owner, expression) <- M.toList $ forallcb environment]
            , lcs = case lcs environment of LC contexts -> LC [[(rename owner, F.subst action ty) | (owner, ty) <- context] | context <- contexts]
            }
  where
    action = F.mkSubst [(owner, F.EVar $ F.symbol actual) | (owner, actual) <- owners]
    rename owner = maybe owner F.symbol (lookup owner owners)
    renameTypes (REnv globals locals) = REnv (renameMap globals) (renameMap locals)
    renameMap types = M.fromList [(rename owner, F.subst action ty) | (owner, ty) <- M.toList types]
    renameId owner = fromMaybe owner (lookup (F.symbol owner) owners)
    renameDictionaries (DEnv dictionaries) = DEnv $ M.fromList [(renameId owner, M.map (fmap $ F.subst action) fields) | (owner, fields) <- M.toList dictionaries]
    renameCore expression = foldr (\owner -> GM.substCoreVar owner (Var $ renameId owner)) expression [owner | owner <- nonDetEltsUniqSet $ exprFreeVars expression, isId owner]

-- Abstract applications retain their owned representation through query
-- composition. Only rigid owners introduced by this split judgment are lowered
-- here; a same-spelled source term is never an abstract predicate owner.
openNativeSignature :: [RPVar] -> SpecType -> Maybe SpecType
openNativeSignature predicates signature =
    let opened = foldl open signature predicates
     in if closedTelescope opened then Just opened else Nothing
  where
    open ty predicate = mapScopedPredicateWith remove predicate (const $ replacePredsWithRefs (uPVar predicate, pVartoRConc predicate)) ty
      where
        remove binder
            | pname binder == pname predicate = Nothing
            | otherwise = Just (binder, pname binder)
    closedTelescope (RAllT _ rest _) = closedTelescope rest
    closedTelescope RAllP{} = False
    closedTelescope (RFun _ _ _ rest _) = closedTelescope rest
    closedTelescope _ = True

openNativeRefinement :: [RPVar] -> CGEnv -> [(F.Symbol, Id)] -> CheckedRefinement -> CG (CGEnv, CoreExpr, F.Expr)
openNativeRefinement predicates environment owners refinement = do
    (opened, bodies) <- foldM open (environment, []) (checkedPredicates refinement)
    let logical = checkedLogical refinement
        F.Reft (root, concrete) = ur_reft logical
        Pr applications = ur_pred logical
        remainder = F.pAnd (concrete : [pVartoRConc application (root, pargs application) | application <- applications])
        action = F.mkSubst [(owner, F.EVar $ F.symbol actual) | (owner, actual) <- owners]
    (withRemainder, remainderBody, membershipMeaning) <- logicalBoolean opened (F.subst action remainder)
    -- Membership supplies the path on which the authored source guards are
    -- admitted. Demand each whole guard only there, in its original order;
    -- no original query argument domain is installed as an assumption.
    sourceBody <- foldM (\result source -> nativeIf source result (Var $ dataConWorkId falseDataCon)) (Var $ dataConWorkId trueDataCon) (reverse bodies)
    body <- nativeIf remainderBody sourceBody (Var $ dataConWorkId falseDataCon)
    let meaning = F.pAnd (membershipMeaning : [F.subst action $ predicateReadback source | source <- checkedPredicates refinement])
    return (withRemainder, body, meaning)
  where
    open (scope, bodies) predicate = do
        let signature = fromMaybe (panic (Just $ getLocation environment) "Native opening lost its owned predicate scope") (openNativeSignature predicates $ predicateSignature predicate)
            openedBody = simpleOptExprNoInline defaultSimpleOpts{so_eta_red = False} $ mkApps (predicateCore predicate) (arguments predicate signature)
            primitiveDomains = [(formal, F.subst (queryOwnerAction predicate) domain) | (owner, domain) <- domains signature, Just formal <- [lookup owner $ queryValueOwners $ predicateTelescope predicate], primitiveFormal predicate formal]
        scope' <- foldM (\current (formal, domain) -> if primitiveFormal predicate formal then current += ("native logical primitive", F.symbol formal, domain) else return current) scope primitiveDomains
        return (scope', bodies ++ [openedBody])
    domains (RAllT _ rest _) = domains rest
    domains (RAllP _ rest) = domains rest
    domains (RFun owner _ domain rest _) = (owner, domain) : domains rest
    domains _ = []
    -- Generated contracts share the complete query telescope. Open their
    -- dependent value coordinates by the SAME action as the Core arguments.
    queryOwnerAction predicate = F.mkSubst [(owner, F.EVar $ F.symbol actual) | (owner, formal) <- queryValueOwners $ predicateTelescope predicate, Just actual <- [argumentOwner predicate formal]]
    argumentOwner predicate formal
        | primitiveFormal predicate formal = Just formal
        | Just (F.EVar source) <- lookup formal (predicateDefinitions predicate) = lookup source owners
        | otherwise = Nothing
    arguments predicate (RAllT variable rest _)
        | RTV source <- ty_var_value variable = Type (mkTyVarTy source) : arguments predicate rest
    arguments predicate (RAllP _ rest) = arguments predicate rest
    arguments predicate (RFun owner _ _ rest _) = case lookup owner (queryValueOwners $ predicateTelescope predicate) of
        Just formal
            | primitiveFormal predicate formal -> Var (setVarType formal $ instantiateNativeType predicate $ varType formal) : arguments predicate rest
            | Just (F.EVar source) <- lookup formal (predicateDefinitions predicate)
            , Just actual <- lookup source owners ->
                Var actual : arguments predicate rest
        _ -> panic (Just $ getLocation environment) "Native opening lost a validated source owner"
    arguments _ _ = []

logicalBoolean :: CGEnv -> F.Expr -> CG (CGEnv, CoreExpr, F.Expr)
logicalBoolean environment F.PTrue = return (environment, Var $ dataConWorkId trueDataCon, F.PTrue)
logicalBoolean environment F.PFalse = return (environment, Var $ dataConWorkId falseDataCon, F.PFalse)
logicalBoolean environment meaning = do
    identifier <- freshNativeBool
    let root = F.vv Nothing
        carrier = ofType boolTy `strengthen` uTop (F.Reft (root, F.PIff (F.EVar root) meaning))
    extended <- environment += ("native logical Boolean", F.symbol identifier, carrier)
    return (extended, Var identifier, F.EVar $ F.symbol identifier)

freshNativeBool :: CG Id
freshNativeBool = do
    unique <- fresh
    return $ mkLocalVar VanillaId (mkInternalName (mkUnique 'L' $ fromInteger unique) (mkVarOcc "lh_native_bool") noSrcSpan) ManyTy boolTy vanillaIdInfo

nativeIf :: CoreExpr -> CoreExpr -> CoreExpr -> CG CoreExpr
-- Bool's identity case preserves the source expression itself, including its
-- demand structure, instead of asking inference to summarize another Case.
nativeIf condition (Var yes) (Var no)
    | yes == dataConWorkId trueDataCon
    , no == dataConWorkId falseDataCon =
        return condition
nativeIf condition yes no = do
    binder <- freshNativeBool
    return $ Case condition binder boolTy [Alt (DataAlt falseDataCon) [] no, Alt (DataAlt trueDataCon) [] yes]

--------------------------------------------------------------------------------
consCBLet :: CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBLet γ cb = do
    oldtcheck <- gets tcheck
    isStr <- doTermCheck (getConfig γ) cb
    -- TODO: yuck.
    modify $ \s -> s{tcheck = oldtcheck && isStr}
    γ' <- consCB (mkTCheck oldtcheck isStr) γ cb
    modify $ \s -> s{tcheck = oldtcheck}
    consRefinementChecks γ' (bindersOf cb)
    -- The original binding and its declared contract have just been checked in
    -- their original scope. Remember only a finite constructor introduction:
    -- its recursive field view is synthesized at each actual use, not before
    -- the enclosing function's value arguments have entered the environment.
    return $ case cb of
        NonRec owner rhs
            | Just _ <- dictionaryConstructorAt γ rhs ->
                γ'{lcb = M.insert (F.symbol owner) rhs (lcb γ')}
        _ -> γ'

-- Formation is an ordinary Core typing judgment in the owner's lexical
-- environment. Check after the group: its independently inferred contracts
-- are shared with this query, without the group's temporary decrease types.
consRefinementChecks :: CGEnv -> [Var] -> CG ()
consRefinementChecks γ owners = forM_ owners $ \owner -> do
    requested <- gets refinementChecksByOwner
    modify $ \s -> s{visitedRefinementOwners = S.insert owner (visitedRefinementOwners s)}
    -- Case expansion can duplicate a binding. Check every occurrence's actual
    -- path; the visited set only detects obligations with no owner at all.
    forM_ (M.findWithDefault [] owner requested) $ \check -> do
        let expression = refinementCheckExpr check
            location = GM.fSrcSpan (F.loc (refinementCheckPredicate check))
            freeIds = filter isId (nonDetEltsUniqSet (exprFreeVars expression))
            sourceIds = S.fromList (giDefVars (giSrc (cgInfo γ)))
        -- A predicate can mention a source definition before its Core group.
        -- Use the very same independently projected checking template/KVars
        -- that its body must establish. Never fall back to an erased arrow.
        queryEnv <- foldM (forwardTemplate location sourceIds) γ freeIds
        let
            missing =
                [ identifier
                | identifier <- freeIds
                , not (isExternalName (getName identifier))
                , not (GM.isDataConId identifier)
                , Nothing <- [queryEnv ?= F.symbol identifier]
                ]
        unless (null missing) $
            panic
                (Just location)
                ( "Refinement formation lost lexical captures: "
                    ++ unwords (map GM.showPpr missing)
                )
        tycons <- gets tyConInfo
        target <- refreshArgs $ addTyConInfo (emb γ) tycons (predicateSignature (F.val (refinementCheckPredicate check)))
        -- Metadata belongs to this declaration, not the last checked member
        -- of its group. Bodyless external owners use the ordinary default tag.
        let ownedEnv = queryEnv{cgVar = Just owner, tgKey = Nothing} `setBind` owner
        cconsE (ownedEnv `setLocation` Sp.Span location) expression target
  where
    forwardTemplate location sourceIds environment identifier
        | identifier `S.member` sourceIds
        , Nothing <- environment ?= F.symbol identifier =
            case lookupREnv (F.symbol identifier) (grtys environment) of
                Just declared -> do
                    callable <- refreshArgs declared
                    environment += ("refinement checking template", F.symbol identifier, callable)
                Nothing ->
                    panic
                        (Just location)
                        ("Refinement formation has no shared source checking template: " ++ GM.showPpr identifier)
        | otherwise = pure environment

--------------------------------------------------------------------------------
-- | Constraint Generation: Corebind -------------------------------------------
--------------------------------------------------------------------------------
consCBTop :: Config -> TargetInfo -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
consCBTop cfg info cgenv cb
  | all trustVar xs
  = foldM addB cgenv xs
    where
       xs   = bindersOf cb
       tt   = trueTy (typeclass cfg) . varType
       addB γ x = tt x >>= (\t -> γ += ("derived", F.symbol x, t))
       trustVar x = not (checkDerived cfg) && derivedVar (giSrc info) x

consCBTop _ info γ cb
  = do oldtcheck <- gets tcheck
       -- lazyVars  <- specLazy <$> get
       isStr     <- doTermCheck (getConfig γ) cb
       modify $ \s -> s { tcheck = oldtcheck && isStr}
       -- Current claims are induction candidates, not ambient invariants.
       -- removeInvariant places them in rinvs; makeRecInvariants may expose
       -- them only for smaller arguments. restoreInvariant publishes them
       -- to following groups after this group's constraints are generated.
       let pending = mkRTyConInv
             [ candidate | candidate@(Just owner, _) <- gsInvariants (gsData (giSpec info))
                         , owner `elem` bindersOf cb ]
           (γ', i) = removeInvariant
             (γ { invs = M.unionWith (++) (invs γ) pending }) cb
       γ'' <- consCB (mkTCheck oldtcheck isStr) (γ'{cgVar = topBind cb}) cb
       modify $ \s -> s { tcheck = oldtcheck}
       return $ restoreInvariant γ'' i                    --- DIFF
    where
      topBind (NonRec v _)  = Just v
      topBind (Rec [(v,_)]) = Just v
      topBind _             = Nothing

--------------------------------------------------------------------------------
consCB :: TCheck -> CGEnv -> CoreBind -> CG CGEnv
--------------------------------------------------------------------------------
-- do termination checking
consCB TerminationCheck γ (Rec xes)
  = do modify $ \i -> i { recCount = recCount i + length xes }
       consCBSourceTys consBind γ xes

-- don't do termination checking, but some strata checks?
consCB StrataCheck γ (Rec xes)
  = do authorized <- structuralTerminationAuthorized (getConfig γ) (Rec xes)
       xets     <- forM xes $ \(x, e) -> (x, e,) <$> varTemplate γ (x, Just e)
       modify     $ \i -> i { recCount = recCount i + length xes }
       let xts    = [(x, to) | (x, _, to) <- xets]
       γ'        <- foldM (extend authorized) (γ `setRecs` (fst <$> xts)) xts
       checked <- mapM (consBind True γ') xets
       foldM (extenderAfterBodyWith id) (γ `setRecs` (fst <$> xts))
         [(owner, original, actual) | ((owner, original), actual) <- zip xts checked]
  where
    extend True env (owner, Asserted target) = induction env owner target
    extend True env (owner, Internal target) = induction env owner target
    extend _ env binding = extenderWith recursiveHypothesis env binding
    induction env owner target = do
      callable <- recursiveCallable env owner target
      env += ("structural induction", F.symbol owner, recursiveHypothesis callable)

-- don't do termination checking, and don't do any strata checks either?
consCB NoCheck γ (Rec xes)
  = do xets   <- forM xes $ \(x, e) -> fmap (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM (extenderWith recursiveHypothesis) (γ `setRecs` (fst <$> xts)) xts
       checked <- mapM (consBind True γ') xets
       foldM (extenderAfterBodyWith id) (γ `setRecs` (fst <$> xts))
         [(owner, original, actual) | ((owner, original), actual) <- zip xts checked]

consCB _ γ (NonRec x def)
  | Just (w, τ) <- grepDictionary def
  , Just d      <- dlookup (denv γ) w
  = do st       <- mapM (trueTy (typeclass (getConfig γ))) τ
       mapM_ addW (WfC γ <$> st)
       let xts   = dmap (fmap (f st)) d
       γ'       <- consCBNonRec γ x def
       return $ γ' { denv = dinsert (denv γ') x xts }
   where
    f [t']    (RAllT α te _) = subsTyVarMeetWith (emb γ) (ty_var_value α, t') te
    f (t':ts) (RAllT α te _) = f ts $ subsTyVarMeetWith (emb γ) (ty_var_value α, t') te
    f _ _ = impossible Nothing "consCB on Dictionary: this should not happen"

consCB _ γ (NonRec x e) = consCBNonRec γ x e

consCBNonRec :: CGEnv -> Var -> CoreExpr -> CG CGEnv
consCBNonRec γ x e
  = do to  <- varTemplate γ (x, Nothing)
       when (warnOnTermHoles (getConfig γ)) checkLetHole
       to' <- consBind False γ (x, e, to) >>= addPostTemplate γ
       extenderAfterBodyWith (makeSingleton γ (simplify e)) γ (x, to, to')
  where
    -- See Note [Term holes]
    checkLetHole =
      do
        let isItHole = detectTypedHole e
        case isItHole of
          Just (srcSpan, var) -> do
            linkANFToHole x (var, RealSrcSpan srcSpan Strict.Nothing)
          _ -> return ()
grepDictionary :: CoreExpr -> Maybe (Var, [Type])
grepDictionary = go []
  where
    go ts (App (Var w) (Type t)) = Just (w, reverse (t:ts))
    go ts (App e (Type t))       = go (t:ts) e
    go ts (App e (Var _))        = go ts e
    go ts (Let _ e)              = go ts e
    go _ _                       = Nothing

--------------------------------------------------------------------------------
consBind :: Bool -> CGEnv -> (Var, CoreExpr, Template SpecType) -> CG (Template SpecType)
--------------------------------------------------------------------------------
consBind _ _ (x, _, Assumed t)
  | RecSelId {} <- idDetails x -- don't check record selectors with assumed specs
  = return $ F.notracepp ("TYPE FOR SELECTOR " ++ show x) $ Assumed t

consBind isRec' γ (x, e, Asserted spect) =
    do
        let γ' = γ `setBind` x
            (_, πs, _) = bkUniv spect
        cgenv <- foldM addPToEnv γ' πs
        cconsE cgenv e (weakenResult (typeclass (getConfig γ)) x spect)
        when (F.symbol x `elemHEnv` holes γ) $ do
            -- Hole formals belong to the shared checking template. Body and
            -- formation-call refreshings are occurrences substituting those
            -- formals, not new owners of the KVar's well-formedness scope.
            -- Keep this actual lexical environment for captured variables.
            case lookupREnv (F.symbol x) (grtys cgenv) of
                Just declared -> addW $ WfC cgenv $ fmap killSubst declared
                Nothing ->
                    panic
                        (Just (getSrcSpan x))
                        ("Missing shared hole checking template: " ++ GM.showPpr x)
        addIdA x (defAnn isRec' spect)
        return $ Asserted spect

consBind isRec' γ (x, e, Internal spect)
  = do let γ'       = γ `setBind` x
           (_,πs,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs
       let γπ' = γπ {cerr = Just $ ErrHMeas (getLocation γπ) (pprint x) (text explanation)}
       cconsE γπ' e spect
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec' spect)
       return $ Internal spect
  where
    explanation = "Cannot give singleton type to the function definition."

consBind isRec' γ (x, e, Assumed spect)
  = do let γ' = γ `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e =<< true (typeclass (getConfig γ)) spect
       addIdA x (defAnn isRec' spect)
       return $ Asserted spect
    where πs   = ty_preds $ toRTypeRep spect

consBind isRec' γ (x, e, Unknown)
  = do t'    <- consE (γ `setBind` x) e
       t     <- topSpecType x t'
       addIdA x (defAnn isRec' t)
       when (GM.isExternalId x) (addKuts x t)
       return $ Asserted t

killSubst :: RReft -> RReft
killSubst = mapReftField killSubstReft

killSubstReft :: F.Reft -> F.Reft
killSubstReft = trans ks
  where
    ks (F.PKVar k _ _) = F.PKVar k mempty mempty
    ks p                = p

-- | Add a type variable → sort mapping to every PKVar in a SpecType.
-- Used during type application to record how type variables are instantiated,
-- so the solver can apply the correct sort substitution to qualifier solutions.
addTyVarSubToKVars :: F.Symbol -> F.Sort -> SpecType -> SpecType
addTyVarSubToKVars sym sort = mapReft (mapReftField (trans addSub))
  where
    addSub (F.PKVar k tsu su) =
      let tsu' = M.map (F.applyCoercion sym sort) tsu
       in F.PKVar k (M.insert sym sort tsu') su
    addSub e                  = e

defAnn :: Bool -> t -> Annot t
defAnn True  = AnnRDf
defAnn False = AnnDef

-- | Detect a direct typed-hole occurrence in Core and recover the source span
--   that GHC attached to it, if present. The helper deliberately matches the
--   stable @.hole@ naming convention after stripping wrappers introduced by
--   desugaring and normalization.
--
-- See Note [Term holes]
detectTypedHole :: CoreExpr -> Maybe (RealSrcSpan, Var)
detectTypedHole e =
  case stripTicks e of
    Var x | isVarHole x ->
      case lastTick e of
        Just (SourceNote src _) -> Just (src, x)
        _                       -> Nothing
    _ -> Nothing

-- | Remove the outer application and tick wrappers that GHC places around a
--   hole so 'detectTypedHole' can inspect the underlying binder.
stripTicks :: CoreExpr -> CoreExpr
stripTicks (App (Tick _ e) _) = stripTicks e
stripTicks (Tick _ e)         = stripTicks e
stripTicks e          = e

-- | Traverse an expression and keep the innermost tick, which is the source
--   note used to report the hole location.
lastTick :: Expr b -> Maybe CoreTickish
lastTick (Tick t e) =
  case lastTick e of
    Just t' -> Just t'
    Nothing -> Just t
lastTick (App e a) =
  case lastTick a of
    Just ta -> Just ta
    Nothing -> lastTick e
lastTick _ = Nothing

-- | Check whether a Core binder name follows GHC's @.hole@ naming scheme for
--   typed holes.
isVarHole :: Var -> Bool
isVarHole x = isHoleStr (F.symbolString (F.symbol x))
  where
    isHoleStr s =
      case break (== '.') s of
        (_, '.':rest) -> rest == "hole"
        _             -> False

--------------------------------------------------------------------------------
-- | Bidirectional Constraint Generation: CHECKING -----------------------------
--------------------------------------------------------------------------------
cconsE :: CGEnv -> CoreExpr -> SpecType -> CG ()
--------------------------------------------------------------------------------
cconsE g e t = do
  checkANFHoleInExpr e t
  cconsE' g e t

--------------------------------------------------------------------------------
cconsE' :: CGEnv -> CoreExpr -> SpecType -> CG ()
--------------------------------------------------------------------------------
cconsE' γ e t
  | Just (Rs.PatSelfBind _x e') <- Rs.lift e
  = cconsE' γ e' t

  | Just (Rs.PatSelfRecBind x e') <- Rs.lift e
  = let γ' = γ { grtys = insertREnv (F.symbol x) t (grtys γ)}
    in void $ consCBLet γ' (Rec [(x, e')])

cconsE' γ e@(Let b@(NonRec x _) ee) t
  = do sp <- gets specLVars
       if x `S.member` sp
         then cconsLazyLet γ e t
         else do γ' <- consCBLet γ b
                 cconsE γ' ee t

cconsE' γ e (RAllP p t) =
    do
        (γπ, t') <- openPredicate γ p t
        let (css, t'') = splitConstraints (typeclass (getConfig γ)) t'
        cconsE (L.foldl' addConstraints γπ css) e t''

cconsE' γ (Let b e) t
  = do γ' <- consCBLet γ b
       cconsE γ' e t

cconsE' γ (Case e x _ cases) t
  = do γ' <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase γ' x t nonDefAlts
    where
       nonDefAlts = [a | Alt a _ _ <- cases, a /= DEFAULT]
       _msg = "cconsE' #nonDefAlts = " ++ show (length nonDefAlts)

cconsE' γ (Lam α e) (RAllT α' t r) | isTyVar α
  = do γ' <- updateEnvironment γ α
       addForAllConstraint γ' α e (RAllT α' t r)
       cconsE γ' e $ subsTyVarMeet' (ty_var_value α', rVar α) t

cconsE' γ (Lam x e) (RFun y i ty t r)
  | not (isTyVar x)
  = do γ' <- γ += ("cconsE", x', ty)
       cconsE γ' e t'
       addFunctionConstraint γ x e (RFun x' i ty t' r')
       addIdA x (AnnDef ty)
  where
    x'  = F.symbol x
    t'  = t `F.subst1` (y, F.EVar x')
    r'  = r `F.subst1` (y, F.EVar x')

cconsE' γ (Tick tt e) t
  = cconsE (γ `setLocation` Sp.Tick tt) e t

cconsE' γ e@(Cast e' c) t
  = do t' <- castTy γ (exprType e) e' c
       addC (SubC γ (F.notracepp ("Casted Type for " ++ GM.showPpr e ++ "\n init type " ++ showpp t) t') t) ("cconsE Cast: " ++ GM.showPpr e)

cconsE' γ e t
  = do
       when (warnOnTermHoles (getConfig γ))  maybeAddHole
       te  <- consE γ e
       cconsType γ e te t
  where
    -- See Note [Term holes]
    -- Record the expected type of a direct hole encountered in checking mode.
    maybeAddHole = do
      let isItHole = detectTypedHole e
      case isItHole of
        Just (srcSpan, x) -> do
          addHole (RealSrcSpan srcSpan Strict.Nothing) x t γ
        _ -> return ()

cconsType :: CGEnv -> CoreExpr -> SpecType -> SpecType -> CG ()
cconsType γ e te t = do
  te' <- instantiatePreds γ te >>= addPost γ
  addC (SubC γ te' t) ("cconsE: " ++ "\n t = " ++ showpp t ++ "\n te = " ++ showpp te ++ GM.showPpr e)

lambdaSingleton :: CGEnv -> F.TCEmb TyCon -> Var -> CoreExpr -> CG UReft
lambdaSingleton γ tce x e
  | higherOrderFlag γ
  = do expr <- logicExpr γ (F.ELam (F.symbol x, sx) <$> coreToLogic e)
       return $ case expr of
         Just e' -> uTop $ F.exprReft e'
         _       -> mempty
  where
    sx = typeSort tce $ Ghc.expandTypeSynonyms $ varType x
lambdaSingleton _ _ _ _
  = return mempty

addForAllConstraint :: CGEnv -> Var -> CoreExpr -> SpecType -> CG ()
addForAllConstraint γ _ _ (RAllT rtv rt rr)
  | isTauto rr
  = return ()
  | otherwise
  = do t'       <- true (typeclass (getConfig γ)) rt
       let truet = RAllT rtv $ unRAllP t'
       addC (SubC γ (truet mempty) $ truet rr) "forall constraint true"
  where unRAllP (RAllT a t r) = RAllT a (unRAllP t) r
        unRAllP (RAllP _ t)   = unRAllP t
        unRAllP t             = t
addForAllConstraint γ _ _ _
  = impossible (Just $ getLocation γ) "addFunctionConstraint: called on non function argument"


addFunctionConstraint :: CGEnv -> Var -> CoreExpr -> SpecType -> CG ()
addFunctionConstraint γ x e (RFun y i ty t r)
  = do ty'      <- true (typeclass (getConfig γ)) ty
       t'       <- true (typeclass (getConfig γ)) t
       let truet = RFun y i ty' t'
       tce <- gets tyConEmbed
       ref <- lambdaSingleton γ tce x e
       addC (SubC γ (truet ref) $ truet r) "function constraint singleton"
addFunctionConstraint γ _ _ _
  = impossible (Just $ getLocation γ) "addFunctionConstraint: called on non function argument"

splitConstraints ::
    (TyConable c) =>
    Bool -> RType c tv r -> ([[(F.Symbol, RType c tv r)]], RType c tv r)
splitConstraints allowTC (RRTy cs _ OCons t) =
    let (css, t') = splitConstraints allowTC t in (cs : css, t')
splitConstraints allowTC (RFun x i tx@(RApp c _ _ _) t r)
    | isErasable c =
        let (css, t') = splitConstraints allowTC t in (css, RFun x i tx t' r)
  where
    isErasable = isEmbeddedDict
splitConstraints _ t =
    ([], t)

-------------------------------------------------------------------
-- | @instantiatePreds@ peels away the universally quantified @PVars@
--   of a @RType@, generates fresh @Ref@ for them and substitutes them
--   in the body.
-------------------------------------------------------------------
instantiatePreds :: CGEnv
                 -> SpecType
                 -> CG SpecType
instantiatePreds γ (RAllP π t)
  = do r <- freshPredRef γ π
       instantiatePreds γ $ replacePreds "consE" t [(π, r)]

instantiatePreds _ t0
  = return t0


-------------------------------------------------------------------
cconsLazyLet :: CGEnv
             -> CoreExpr
             -> SpecType
             -> CG ()
cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- trueTy (typeclass (getConfig γ)) (varType x)
       γ' <- (γ, "Let NonRec") +++= (F.symbol x, ex, tx)
       cconsE γ' e t
cconsLazyLet _ _ _
  = panic Nothing "Constraint.Generate.cconsLazyLet called on invalid inputs"


---------------------------------------------------------
-- | Bidirectional Constraint Generation: SYNTHESIS ----------------------------
--------------------------------------------------------------------------------
consE :: CGEnv -> CoreExpr -> CG SpecType
--------------------------------------------------------------------------------
consE γ e
  | Just result <- primitiveContract (targetMaxSmallTag (getConfig γ)) (emb γ) (gsADTs $ gsName $ giSpec $ cgInfo γ) e =
      either (panic (Just $ getLocation γ)) refreshVV result
consE γ e
  | patternFlag γ
  , Just p <- Rs.lift e
  = consPattern γ (F.notracepp "CONSE-PATTERN: " p) (exprType e)

-- NV CHECK 3 (unVar and does this hack even needed?)
-- NV (below) is a hack to type polymorphic axiomatized functions
-- no need to check this code with flag, the axioms environment with
-- is empty if there is no axiomatization.

-- [NOTE: PLE-OPT] We *disable* refined instantiation for
-- reflected functions inside proofs.

-- If datacon definitions have references to self for fancy termination,
-- ignore them at the construction.
consE γ (Var x) | GM.isDataConId x =
    do
        t0 <- varRefType γ x
        -- NV: The check is expected to fail most times, so
        --     it is cheaper than direclty fmap ignoreSelf.
        let hasSelf = selfSymbol `S.member` F.syms t0
        let t =
                if hasSelf
                    then mapReft (mapReftField ignoreSelf) t0
                    else t0
        addLocA (Just x) (getLocation γ) (varAnn γ x t)
        return (scopedConstructorIntroduction γ (Var x) t)

-- Re-infer a known constructor at the actual use scope, where the current
-- recursive call's argument binders and decreased field types are available.
-- This is ordinary constructor typing, not a field-body expansion.
consE γ (Var x)
    | Just (constructor, recursive) <- recursiveDictionary γ (Var x)
    , recursiveDictionaryInScope γ recursive =
        consE γ constructor

consE γ (Var x)
  = do -- GHC's undefined has no ordinary argument on which to place an
       -- impossible domain, and a false RESULT would make every context that
       -- merely binds it vacuous. Under totality its use is an obligation that
       -- the context is unreachable.
       when (totalityCheck γ && isUndefinedPrimitive x) $
         addC (SubC γ (ofType boolTy) (ofType boolTy `strengthen` uTop F.falseReft)) "strict totality: undefined"
       t <- varRefType γ x
       addLocA (Just x) (getLocation γ) (varAnn γ x t)
       return t

consE _ (Lit c)
  = refreshVV $ uRType $ literalFRefType c

consE γ e@App{}
  | Just l <- boxedLiteralExpr γ e
  = refreshVV $ strengthenMeet (ofType $ exprType e) (uTop $ F.exprReft l)

consE γ e'@(App _ _) =
    do
        t <- if warnOnTermHoles (getConfig γ) then synthesizeWithHole else consEApp γ e'
        -- Keep the original call's argument/domain constraints before exposing
        -- an exact dictionary constructor under the current recursive field types.
        actual <- case recursiveDictionary γ e' of
            Just (constructor, recursive)
                | recursiveDictionaryInScope γ recursive ->
                    consE γ constructor
            _ -> return t
        selected <- refineDictionarySelection γ e' actual
        checkANFHoleInExpr e' selected
        return selected
  where
    -- See Note [Term holes]
    -- Record the synthesized type of a direct hole encountered in synthesis
    -- mode before the caller consumes it.
    synthesizeWithHole = do
      let isItHole = detectTypedHole e'
      t <- consEApp γ e'
      _ <- case isItHole of
        Just (srcSpan, x) -> do
          addHole (RealSrcSpan srcSpan Strict.Nothing) x t γ
        _ -> return ()
      return t
consE γ (Lam α e) | isTyVar α
  = do γ' <- updateEnvironment γ α
       t' <- consE γ' e
       return $ RAllT (makeRTVar $ rTyVar α) t' mempty

consE γ  e@(Lam x e1)
  = do tx      <- freshTyType (typeclass (getConfig γ)) LamE (Var x) τx
       γ'      <- γ += ("consE", F.symbol x, tx)
       t1      <- consE γ' e1
       addIdA x $ AnnDef tx
       addW     $ WfC γ tx
       tce     <- gets tyConEmbed
       lamSing <- lambdaSingleton γ tce x e1
       return   $ RFun (F.symbol x) (mkRFInfo $ getConfig γ) tx t1 lamSing
    where
      FunTy { ft_arg = τx } = exprType e

consE γ e@(Let _ _)
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ cs)
  = cconsFreshE (caseKVKind cs) γ e

consE γ (Tick tt e)
  = do t <- consE (setLocation γ (Sp.Tick tt)) e
       addLocA Nothing (GM.tickSrcSpan tt) (AnnUse t)
       return t

consE γ e@(Cast e' c)
  = castTy γ (exprType e) e' c

consE γ (Coercion (CoVarCo variable)) =
    γ ??= variable
consE γ (Coercion (SymCo co)) = do
    RApp c [k1, k2, source, target] ps r <- consE γ (Coercion co)
    return $ RApp c [k2, k1, target, source] ps r
consE γ (Coercion (TransCo firstCo secondCo)) = do
    RApp c [k1, _, source, middle1] ps r <- consE γ (Coercion firstCo)
    RApp _ [_, k2, middle2, target] _ _ <- consE γ (Coercion secondCo)
    addC (SubC γ middle1 middle2) "coercion composition"
    addC (SubC γ middle2 middle1) "coercion composition"
    return $ RApp c [k1, k2, source, target] ps r

-- Reflexive primitive evidence relates one refined endpoint to itself.
consE γ e@(Coercion co)
  | Just (τ, role) <- Co.isReflCo_maybe co
  , role /= Co.Phantom =
      do
        RApp c [k1, k2, _, _] ps r <- trueTy allowTC $ exprType e
        t <- freshTyType allowTC TypeInstE e τ
        addW $ WfC γ t
        return $ RApp c [k1, k2, t, t] ps r
 where
  allowTC = typeclass (getConfig γ)

-- Evidence transports the whole endpoint in both directions. The fresh
-- endpoint predicates cannot depend on either independently scoped witness.
consE γ e@(Coercion co)
  | Co.coercionRole co /= Co.Phantom
  , Just (dc, direction) <- newtypeCoercionDataCon co = do
      RApp c [k1, k2, _, _] ps r <- trueTy allowTC $ exprType e
      let Pair source target = coercionKind co
      s <- freshTyType allowTC TypeInstE e source
      t <- freshTyType allowTC TypeInstE e target
      addW $ WfC γ s
      addW $ WfC γ t
      checkNewtypeCoercion γ co dc direction s t
      let inverse = case direction of
            WrapCoercion -> UnwrapCoercion
            UnwrapCoercion -> WrapCoercion
      checkNewtypeCoercion γ (Co.mkSymCo co) dc inverse t s
      return $ RApp c [k1, k2, s, t] ps r
 where
  allowTC = typeclass (getConfig γ)

consE γ e@(Coercion _)
   = trueTy (typeclass (getConfig γ)) $ exprType e

consE _ e@(Type t)
  = panic Nothing $ "consE cannot handle type " ++ GM.showPpr (e, t)

-- | Attach the current expression and inferred type to any ANF binders that
--   were previously recognized as naming a term hole. This compensates for ANF
--   normalization, which often moves the informative constraints from the hole
--   occurrence onto the fresh binder that stands for it.
--
-- See Note [Term holes]
checkANFHoleInExpr :: CoreExpr -> SpecType -> CG ()
checkANFHoleInExpr e t = do
  let vars = collectVars e
  forM_ vars $ \var -> do
    isANF <- isANFInHole var
    case isANF of
      Just uniqueVar -> addHoleANF uniqueVar var e t
      _ -> return ()
-- | Collect every variable mentioned in a Core expression so
--   'checkANFHoleInExpr' can look for ANF binders linked to a hole.
collectVars :: CoreExpr -> [Var]
collectVars (Var x) = [x]
collectVars (App e1 e2) = collectVars e1 ++ collectVars e2
collectVars (Lam x e) = x : collectVars e
collectVars (Let (NonRec x e1) e2) = x : collectVars e1 ++ collectVars e2
collectVars (Let (Rec xes) e) =
  let (xs, es) = unzip xes
  in xs ++ concatMap collectVars es ++ collectVars e
collectVars (Case e x _ alts) =
  x : collectVars e ++ concatMap collectAltVars alts
  where collectAltVars (Alt _ xs e') = xs ++ collectVars e'
collectVars _ = []

consEApp :: CGEnv -> CoreExpr -> CG SpecType
consEApp = consEAppUsing consE

-- The function's source judgment can differ at an admitted subsumption site.
-- Its arguments still use the ordinary environment and argument checker.
consEAppUsing :: (CGEnv -> CoreExpr -> CG SpecType) -> CGEnv -> CoreExpr -> CG SpecType
consEAppUsing synthesize γ e'@(App e a@(Type τ)) =
    do
        RAllT α te _ <- checkAll ("Non-all TyApp with expr", e) γ <$> synthesize γ e
        -- Runtime dictionaries are checked arguments. Their constructor-field
        -- variance, not a class-name whitelist, constrains instantiation.
        t <-
            if not (nopolyinfer (getConfig γ)) && isPos α
                then freshTyType (typeclass (getConfig γ)) TypeInstE e τ
                else trueTy (typeclass (getConfig γ)) τ
        addW $ WfC γ t
        t' <- refreshVV t
        tt0 <- instantiatePreds γ (subsTyVarMeetWith (emb γ) (ty_var_value α, t') te)
        let tyVarSym = F.symbol (ty_var_value α)
            tyVarSort = typeSort (emb γ) (Ghc.expandTypeSynonyms τ)
            tt0' = addTyVarSubToKVars tyVarSym tyVarSort tt0
            tt = scopedConstructorIntroduction γ e' (makeSingleton γ (simplify e') tt0')
        return $ case rTVarToBind α of
            Just (x, _) -> maybe (checkUnbound γ e' x tt a) (F.subst1 tt . (x,)) (argType τ)
            Nothing -> tt
  where
    isPos α = not (extensionality (getConfig γ)) || rtv_is_pol (ty_var_info α)
consEAppUsing synthesize γ e'@(App e a) | Just aDict <- getExprDict γ a =
    case getExprFun e a >>= dhasinfo (dlookup (denv γ) aDict) of
        Just riSig | recursiveFields aDict -> do
            actual <- ordinaryApplication
            -- Keep the named instance contract as well as the current recursive
            -- field bound. Returning the latter also checks partial/value uses.
            addC (SubC γ (fromRISig riSig) actual) "recursive dictionary selector contract"
            return actual
        Just riSig -> do
            actual <- ordinaryApplication
            addC (SubC γ (fromRISig riSig) actual) "dictionary selector contract"
            return $ fromRISig riSig
        _ -> ordinaryApplication
  where
    recursiveFields aDict =
        isJust (recursiveDictionary γ a)
            || maybe False (isJust . recursiveDictionary γ) (M.lookup (F.symbol aDict) (lcb γ))
    ordinaryApplication = snd <$> consEAppWith synthesize γ e' e (argExpr γ a) (\γ' -> sourceArgument γ' e' a)
consEAppUsing synthesize γ e'@(App e a) =
    do
        (γ', t) <- consEAppWith synthesize γ e' e (argExpr γ $ simplify a) (\γ' -> sourceArgument γ' e' a)
        return $ scopedConstructorIntroduction γ' e' (makeSingleton γ' (simplify e') t)
consEAppUsing _ _ _ = panic Nothing "Constraint.Generate.consEApp called on invalid inputs"

-- Subsumption changes this source value's view, not the surrounding callable
-- environment. Every actual argument and every residual expected refinement
-- is checked by the ordinary application and subtyping judgments.
sourceArgument :: CGEnv -> CoreExpr -> CoreExpr -> SpecType -> CG ()
sourceArgument γ site = sourceArgumentAt γ (constructorField site)
  where
    constructorField expression = case collectArgs expression of
        (Var headOwner, arguments)
            | Just constructor <- sourceConstructor headOwner
            , null (Ghc.dataConExTyCoVars constructor)
            , Ghc.dataConWrapperType constructor `eqType` varType headOwner
            , let (_, fields) = span isTypeArg arguments
            , not (null fields) ->
                Just (constructor, length fields - 1)
        _ -> Nothing
    sourceConstructor owner = case idDetails owner of
        DataConWorkId constructor -> Just constructor
        DataConWrapId constructor -> Just constructor
        _ -> Nothing

sourceArgumentAt :: CGEnv -> Maybe (Ghc.DataCon, Int) -> CoreExpr -> SpecType -> CG ()
sourceArgumentAt γ origin argument expected = do
    AdmittedInterfaces interfaces <- gets admittedInterfaces
    case origin >>= \(constructor, index) -> admittedField interfaces constructor index of
        Just (owner, interface) -> do
            actual <- synthesizeInterface owner interface γ argument
            cconsType γ argument actual expected
        Nothing -> cconsE γ argument expected
  where
    admittedField interfaces constructor index = do
        dictionary <- cgVar γ
        guard (isDFunId dictionary)
        let (_, _, cls, _) = Ghc.tcSplitDFunTy (varType dictionary)
        guard (constructor == Ghc.classDataCon cls)
        selector <- atIndex (Ghc.classAllSelIds cls) index
        let program = giCbs (giSrc (cgInfo γ))
        owner <- lookup selector =<< instanceDictionaryOwners program dictionary
        body <- lookup dictionary (flattenBinds program)
        let (parameters, _) = collectBinders body
        guard (argument `eqCoreExpr` mkVarApps (Var owner) parameters)
        case [val ty | (actualOwner, method@MT{}) <- interfaces, actualOwner == owner, methodOrigin method == Just (dictionary, selector), Just ty <- [tyClass method]] of
            [ty] | toType False ty `eqType` varType owner -> Just (owner, ty)
            _ -> Nothing
    atIndex values index = case drop index values of
        value : _ -> Just value
        [] -> Nothing

synthesizeInterface :: Var -> SpecType -> CGEnv -> CoreExpr -> CG SpecType
synthesizeInterface owner interface γ expression = case expression of
    Var actual | actual == owner -> varRefType' γ owner <$> refreshVV interface
    App{} -> consEAppUsing (synthesizeInterface owner interface) γ expression
    Tick tick body -> synthesizeInterface owner interface (γ `setLocation` Sp.Tick tick) body
    _ -> consE γ expression

-- The actual constructor application has already passed ordinary argument
-- checking. Its native prefix supplies the entire instantiated source telescope;
-- no requested result refinement participates in equation selection.
scopedConstructorIntroduction :: CGEnv -> CoreExpr -> SpecType -> SpecType
scopedConstructorIntroduction γ expression inferred = case collectArgs expression of
    (Var owner, arguments)
        | Just dc <- constructor owner
        , let (types, fields) = span isTypeArg arguments
        , all valueArgument fields
        , let actual = exprType (foldl App (Var owner) types)
        , let (variables, body) = splitForAllTyCoVars actual
        , null variables
        , let (expected, result) = splitFunTys body
        , length expected == length fields
        , and (zipWith (\field ty -> exprType field `eqType` irrelevantMult ty) fields expected)
        , result `eqType` exprType expression
        , Just values <- traverse (argExpr γ) fields ->
            inferred `strengthen` uTop (scopedConstructorFacts γ dc actual values)
    _ -> inferred
  where
    constructor owner = case idDetails owner of
        DataConWorkId dc -> Just dc
        DataConWrapId dc -> Just dc
        _ -> Nothing
    valueArgument Type{} = False
    valueArgument Coercion{} = False
    valueArgument _ = True

-- Only source/worker-identical constructors are handled here. Boxed, unpacked,
-- GADT evidence and newtype transport retain their existing judgments. The
-- stage's original measure inventory also owns source availability/admission.
scopedConstructorFacts :: CGEnv -> Ghc.DataCon -> Type -> [F.Expr] -> F.Reft
scopedConstructorFacts γ dc actual fields
    | Ghc.dataConWrapperType dc `eqType` varType (dataConWorkId dc) =
        mconcat
            [ F.subst (F.mkSubst (zip (map fst equationFields) fields)) (rTypeReft receiver)
            | declaration <- gsMeasures (gsData (giSpec (cgInfo γ)))
            , msKind declaration == MsMeasure
            , original <- msEqns declaration
            , ctor original == dc
            , let definition@(Def _ _ _ equationFields _) = mapDefTy (fmap toReft) original
            , length equationFields == length fields
            , Measure.deferredConstructorEquation (msSort declaration) original
            , Just receiver <- [Measure.instantiateConstructorEquation (msSort declaration) actual definition]
            ]
    | otherwise = mempty

-- Ordinary applications and synthesized coercion endpoints use the same
-- argument judgment, differing only in how the actual argument is checked.
consEAppWith :: (CGEnv -> CoreExpr -> CG SpecType) -> CGEnv -> CoreExpr -> CoreExpr -> Maybe F.Expr -> (CGEnv -> SpecType -> CG ()) -> CG (CGEnv, SpecType)
consEAppWith synthesize γ site function actual checkArgument = do
    ([], πs, te) <- bkUniv <$> synthesize γ function
    te1 <- instantiatePreds γ $ foldr RAllP te πs
    (γ', te2) <- dropExists γ te1
    te3 <- dropConstraints γ te2
    updateLocA (exprLoc function) te3
    let RFun x _ tx t _ = checkFun ("Non-fun App with caller ", site) γ te3
    checkArgument γ' tx
    result <- addPost γ' $ maybe (checkUnbound γ' site x t actual) (F.subst1 t . (x,)) actual
    return (γ', result)

-- A checked constructor equality identifies its stored field, but does not
-- replace the selector's source contract. Infer extra result facts under that
-- contract's unchanged input telescope, including inputs of returned functions.
refineDictionarySelection :: CGEnv -> CoreExpr -> SpecType -> CG SpecType
refineDictionarySelection γ expression source
  | Just field <- selectedDictionaryField γ expression = do
      refinement <- refresh (typeclass (getConfig γ)) (mempty :: RReft)
      let onlyNew r
            | F.reftPred (ur_reft r) == F.reftPred (ur_reft refinement) = r
            | otherwise = mempty
      case resultTemplate refinement source of
        Just (goal, candidate) -> do
          instantiated <- instantiatePreds γ field
          addW (WfC γ (mapReft onlyNew goal))
          addC (SubC γ instantiated goal) "checked dictionary field projection"
          return candidate
        Nothing -> return source
  | otherwise = return source
 where
  resultTemplate extra (RAllT variable body refinement) = do
    (goal, candidate) <- resultTemplate extra body
    return (RAllT variable goal mempty, RAllT variable candidate refinement)
  resultTemplate extra (RFun binder info input result refinement) = do
    (goal, candidate) <- resultTemplate extra result
    return (RFun binder info input goal mempty, RFun binder info input candidate refinement)
  resultTemplate extra (REx binder domain body) = do
    (goal, candidate) <- resultTemplate extra body
    return (REx binder domain goal, REx binder domain candidate)
  resultTemplate extra result
    | Just _ <- stripRTypeBase result =
        Just (strengthenTop (topRTypeBase result) extra, strengthenTop result extra)
    -- Supplemental inference needs an exposed result refinement under the
    -- ordinary SubC telescope. Leave delayed predicates/obligations to their
    -- existing application rules, without dropping or checking them early.
    | otherwise = Nothing

selectedDictionaryField :: CGEnv -> CoreExpr -> Maybe SpecType
selectedDictionaryField γ (App function dictionary) = do
  selector <- getExprFun function dictionary
  cls <- isClassOpId_maybe selector
  (_, arguments) <- getClassPredTys_maybe (exprType dictionary)
  -- A collapsed embedding does not make logical equality identify a stored
  -- source field. This elimination uses the actual nominal class carrier.
  guard $
    typeSort (emb γ) (exprType dictionary)
      == F.fApp
        (F.FTC (F.symbolFTycon (F.dummyLoc (F.symbol (classTyCon cls)))))
        (typeSort (emb γ) <$> arguments)
  index <- L.elemIndex selector (classAllSelIds cls)
  expression <- argExpr γ dictionary
  fields <- constructorFields cls S.empty expression
  let field = fields !! index
  case trec γ >>= M.lookup field of
    Just recursive -> do
      guard (recursiveDictionaryInScope γ [recursive])
      return recursive
    Nothing -> γ ?= field
 where
  constructorFields cls seen expression
    | (F.EVar constructor, fields) <- F.splitEApp expression
    , constructor == F.symbol (dataConWorkId (classDataCon cls))
    , length fields == length (classAllSelIds cls) =
        traverse fieldSymbol fields
    | F.EVar owner <- expression
    , not (owner `S.member` seen) = do
        ty <- γ ?= owner
        let F.Reft (value, predicate) = rTypeReft ty
        msum
          [ constructorFields cls (S.insert owner seen) image
          | conjunct <- F.conjuncts predicate
          , Just image <- [F.isSingletonExpr value conjunct]
          ]
    | otherwise = Nothing
  fieldSymbol (F.EVar owner) = Just owner
  fieldSymbol _ = Nothing
selectedDictionaryField _ _ = Nothing

-- The defining binder, not its spelling or re-exporting module: a user's own
-- total binding named undefined remains an ordinary value.
isUndefinedPrimitive :: Var -> Bool
isUndefinedPrimitive x =
  nameModule_maybe name == Just gHC_INTERNAL_ERR
    && occNameString (nameOccName name) == "undefined"
  where
    name = varName x

caseKVKind ::[Alt Var] -> KVKind
caseKVKind [Alt (DataAlt _) _ (Var _)] = ProjectE
caseKVKind cs                          = CaseE (length cs)

updateEnvironment :: CGEnv  -> TyVar -> CG CGEnv
updateEnvironment γ a
  | isValKind (tyVarKind a)
  = γ += ("varType", F.symbol $ varName a, kindToRType $ tyVarKind a)
  | otherwise
  = return γ

-- A cached instance signature replaces only the selector's owning dictionary.
-- Later dictionaries belong to the complete method arrow and are checked by
-- ordinary application, even when type arguments occur between dictionaries.
getExprFun :: CoreExpr -> CoreExpr -> Maybe Var
getExprFun _ Type {} = Nothing
getExprFun _ Coercion {} = Nothing
getExprFun function dictionary
  | (Var selector, arguments, _) <- collectArgsTicks (const True) function
  , all isTypeArg arguments
  , Just owner <- isClassOpId_maybe selector
  , Just (actual, _) <- getClassPredTys_maybe (exprType dictionary)
  , owner == actual =
      Just selector
  | otherwise = Nothing

-- | `exprDict e` returns the dictionary `Var` inside the expression `e`
getExprDict :: CGEnv -> CoreExpr -> Maybe Var
getExprDict γ           =  go
  where
    go (Var x)          = case dlookup (denv γ) x of {Just _ -> Just x; Nothing -> Nothing}
    go (Tick _ e)       = go e
    go (App a (Type _)) = go a
    go (Let _ e)        = go e
    go _                = Nothing

--------------------------------------------------------------------------------
-- | Type Synthesis for Special @Pattern@s -------------------------------------
--------------------------------------------------------------------------------
consPattern :: CGEnv -> Rs.Pattern -> Type -> CG SpecType

{- [NOTE] special type rule for monadic-bind application

    G |- e1 ~> m tx     G, x:tx |- e2 ~> m t
    -----------------------------------------
          G |- (e1 >>= \x -> e2) ~> m t
 -}

consPattern γ (Rs.PatBind e1 x e2 _ _ _ _ _) _ = do
  tx <- checkMonad (msg, e1) γ <$> consE γ e1
  γ' <- γ += ("consPattern", F.symbol x, tx)
  addIdA x (AnnDef tx)
  consE γ' e2
  where
    msg = "This expression has a refined monadic type; run with --no-pattern-inline: "

{- [NOTE] special type rule for monadic-return

           G |- e ~> et
    ------------------------
      G |- return e ~ m et
 -}
consPattern γ (Rs.PatReturn e m _ _ _) t = do
  et    <- F.notracepp "Cons-Pattern-Ret" <$> consE γ e
  mt    <- trueTy (typeclass (getConfig γ))  m
  tt    <- trueTy (typeclass (getConfig γ))  t
  return (mkRAppTy mt et tt) -- /// {-    $ RAppTy mt et mempty -}

-- Projection demands its scrutinee just like every other case expression.
-- The ordinary case judgment checks that demand before exposing field types.
consPattern γ p@Rs.PatProject{} _ =
  cconsFreshE ProjectE γ (Rs.lower p)

consPattern γ (Rs.PatSelfBind _ e) _ =
  consE γ e

consPattern γ p@Rs.PatSelfRecBind{} _ =
  cconsFreshE LetE γ (Rs.lower p)

mkRAppTy :: SpecType -> SpecType -> SpecType -> SpecType
mkRAppTy mt et RAppTy{}          = RAppTy mt et mempty
mkRAppTy _  et (RApp c [_] [] _) = RApp c [et] [] mempty
mkRAppTy _  _  _                 = panic Nothing "Unexpected return-pattern"

checkMonad :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkMonad x g = go . unRRTy
 where
   go (RApp _ ts [] _)
     | not (null ts) = last ts
   go (RAppTy _ t _) = t
   go t              = checkErr x g t

unRRTy :: SpecType -> SpecType
unRRTy (RRTy _ _ _ t) = unRRTy t
unRRTy t              = t

--------------------------------------------------------------------------------
castTy :: CGEnv -> Type -> CoreExpr -> Coercion -> CG SpecType
--------------------------------------------------------------------------------
castTy γ t e co
    | Just (dc, direction) <- newtypeCoercionDataCon co =
        do
            checked <- case direction of
                UnwrapCoercion -> do
                    input <- consE γ e >>= instantiatePreds γ >>= addPost γ
                    castTyNewtypeUnwrap γ t input (argExpr γ e) dc
                WrapCoercion -> castTyNewtypeWrap γ t e (argExpr γ e) (\γ' -> sourceArgumentAt γ' (Just (dc, 0)) e) dc
            -- Use the same interpretation as reflection, after structural checking.
            -- No expected refinement participates in interpreting the actual cast.
            meaning <- lamExpr γ (Cast e co)
            pure (checked `strengthen` maybe mempty (uTop . F.uexprReft) meaning)
castTy γ _ e co = do
    RApp _ [_, _, source, target] _ _ <- consE γ (Coercion co)
    cconsE γ e source
    meaning <- lamExpr γ (Cast e co)
    pure (target `strengthen` maybe mempty (uTop . F.uexprReft) meaning)

-- | A @newtype@ /wrap/ cast @e |> Sym (Rep ~ NT)@ is, logically, the newtype
-- constructor applied to @e@. We type the equivalent constructor application
-- @MkNT \@ts e@, which reuses the datacon's refined type carrying the
-- measure/selector refinements. This makes measures over a @newtype@ reduce
-- just like their @data@ counterparts.
--
-- See note [Newtype checking]
castTyNewtypeWrap :: CGEnv -> Type -> CoreExpr -> Maybe F.Expr -> (CGEnv -> SpecType -> CG ()) -> Ghc.DataCon -> CG SpecType
castTyNewtypeWrap γ τ site actual checkArgument dc
    | Just (_, tyArgs) <- Ghc.splitTyConApp_maybe τ =
        do
            -- The declared field obligation precedes constructor application and is
            -- instantiated independently from its argument obligation.
            mtc <- lookupNewType (Ghc.dataConTyCon dc)
            forM_ mtc $ checkArgument γ
            let constructor = foldl App (Var (Ghc.dataConWorkId dc)) (map Type tyArgs)
            snd <$> consEAppWith consE γ site constructor actual checkArgument
    | otherwise =
        panic (Just (getLocation γ)) "Newtype wrap requires its target datatype application"

-- A newtype projection eliminates its one constructor. Instantiate that
-- constructor exactly as caseEnv does, then transfer its declared equations
-- to the actual input and projected field. No requested goal is an input.
castTyNewtypeUnwrap :: CGEnv -> Type -> SpecType -> Maybe F.Expr -> Ghc.DataCon -> CG SpecType
castTyNewtypeUnwrap γ τ input actual dc = do
    case input of
        RApp _ ts rs _ -> do
            td <- γ ??= Ghc.dataConWorkId dc
            let ti = defaultPvs (instantiatePvs (instantiateTys γ td ts) (reverse rs))
                RFun _ _ field _ _ = checkFun ("Newtype constructor", dc) γ ti
                represented = ofType τ :: SpecType
            unless (toType False field `Ghc.eqType` toType False represented) $
                panic (Just (getLocation γ)) "Newtype field disagrees with its actual Core coercion"
            case actual of
                Nothing -> pure field
                Just value -> do
                    fieldValue <- fresh
                    adts <- gets cgADTs
                    let dm = dataConMap adts
                    let F.Reft (whole, predicate) = dataConMsReft ti [fieldValue]
                        measureFacts = F.Reft (fieldValue, F.subst1 predicate (whole, value))
                        selector = F.EApp (F.EVar (makeDataConSelector (Just dm) dc 1)) value
                        selectorFact
                            | logicSymbolsInScope γ adts selector =
                                F.uexprReft selector
                            | otherwise = mempty
                    pure (field `strengthen` uTop (measureFacts `meet` selectorFact))
        _ -> panic (Just (getLocation γ)) "Newtype projection requires its source datatype application"

checkNewtypeCoercion :: CGEnv -> Coercion -> Ghc.DataCon -> NewtypeCoercion -> SpecType -> SpecType -> CG ()
checkNewtypeCoercion γ co dc direction source target = do
    x <- fresh
    γ' <- γ += ("newtype coercion", x, source)
    let actual = F.EVar x :: F.Expr
        selfify = if higherOrderFlag γ then strengthenMeet else strengthenTop
        input = selfify source (uTop $ F.uexprReft actual)
        site = Coercion co
        Pair _ τ = coercionKind co
    checked <- case direction of
        WrapCoercion -> castTyNewtypeWrap γ' τ site (Just actual) (\env -> cconsType env site input) dc
        UnwrapCoercion -> do
            prepared <- instantiatePreds γ' input >>= addPost γ'
            castTyNewtypeUnwrap γ' τ prepared (Just actual) dc
    meaning <- logicExpr γ' (castToLg co actual)
    addC (SubC γ' (checked `strengthen` maybe mempty (uTop . F.uexprReft) meaning) target) "newtype coercion endpoint"

--------------------------------------------------------------------------------

-- | @consFreshE@ is used to *synthesize* types with a **fresh template**.
--   e.g. at joins, recursive binders, polymorphic instantiations etc. It is
--   the "portal" that connects `consE` (synthesis) and `cconsE` (checking)
--------------------------------------------------------------------------------
cconsFreshE :: KVKind -> CGEnv -> CoreExpr -> CG SpecType
cconsFreshE kvkind γ e = do
  t   <- freshTyType (typeclass (getConfig γ)) kvkind e $ exprType e
  addW $ WfC γ t
  cconsE γ e t
  return t
--------------------------------------------------------------------------------

checkUnbound :: (PPrint a, Show a2, F.Subable a, F.Variable a ~ F.Symbol)
             => CGEnv -> CoreExpr -> F.Symbol -> a -> a2 -> a
checkUnbound γ e x t a
  | not (x `S.member` F.syms t) = t
  | otherwise            = panic (Just $ getLocation γ) msg
  where
    msg = unlines [ "checkUnbound: " ++ show x ++ " is elem of syms of " ++ showpp t
                  , "In"
                  , GM.showPpr e
                  , "Arg = "
                  , show a
                  ]

dropExists :: CGEnv -> SpecType -> CG (CGEnv, SpecType)
dropExists γ (REx x tx t) =         (, t) <$> γ += ("dropExists", x, tx)
dropExists γ t            = return (γ, t)

dropConstraints :: CGEnv -> SpecType -> CG SpecType
dropConstraints cgenv (RFun x i tx@(RApp c _ _ _) t r) | isErasable c
  = flip (RFun x i tx) r <$> dropConstraints cgenv t
  where
    isErasable = isEmbeddedDict
dropConstraints cgenv (RRTy cts _ OCons rt)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) cgenv xts
       addC (SubC γ' t1 t2)  "dropConstraints"
       dropConstraints cgenv rt
  where
    (xts, t1, t2) = envToSub cts

dropConstraints _ t = return t

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> CoreAlt -> CG ()
-------------------------------------------------------------------------------------
cconsCase γ x t acs (Alt ac ys ce)
  = do cγ <- caseEnv γ x acs ac ys mempty
       cconsE cγ ce t

{-

case x :: List b of
  Emp -> e

  Emp :: tdc          forall a. {v: List a | cons v === 0}
  x   :: xt           List b
  ys  == binders      []

-}
-------------------------------------------------------------------------------------
caseEnv :: CGEnv -> Var -> [AltCon] -> AltCon -> [Var] -> Maybe [Int] -> CG CGEnv
-------------------------------------------------------------------------------------
caseEnv γ x _ (DataAlt c) ys pIs = do
    let (x' : ys') = F.symbol <$> (x : ys)
    xt0 <- checkTyCon ("checkTycon cconsCase", x) γ <$> γ ??= x
    let rt = shiftVV xt0 x'
    tdc <- γ ??= dataConWorkId c >>= refreshVV
    let (rtd, yts', _) = unfoldR γ tdc rt ys
    yts <- projectTypes (typeclass (getConfig γ)) pIs yts'
    let ys'' = F.symbol <$> filter (\v -> isId v && not (GM.isEmbeddedDictVar v)) ys
    let r1 = dataConReft c ys''
    let actual = toType False (mkArrow [] [] [(F.symbol y, mkRFInfo (getConfig γ), ofType (varType y), mempty) | y <- ys, isId y] (ofType (varType x) :: SpecType))
    let scoped = scopedConstructorFacts γ c actual (F.EVar <$> ys'')
    let r2 = dataConMsReft rtd ys'' `meet` scoped
    let xt = (xt0 `meet` rtd) `strengthen` uTop (r1 `meet` r2)
    let cbs =
            safeZip
                "cconsCase"
                (x' : ys')
                ( map
                    (`F.subst1` (selfSymbol, F.EVar x'))
                    (xt0 : yts)
                )
    cγ' <- addBinders γ x' cbs
    when allowDC $
        addRewritesForNextBinding $
            getCaseRewrites γ $
                xt0 `meet` rtd
    addBinders cγ' x' [(x', substSelf <$> xt)]
  where
    allowDC = dependantCase (getConfig γ)
caseEnv γ x acs a _ _ = do
    let x' = F.symbol x
    xt' <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x)
    addBinders γ x' [(x', xt')]

------------------------------------------------------
-- SELF special substitutions
------------------------------------------------------

substSelf :: UReft -> UReft
substSelf (MkUReft r p) = MkUReft (substSelfReft r) p

substSelfReft :: F.Reft -> F.Reft
substSelfReft (F.Reft (v, e)) = F.Reft (v, F.subst1 e (selfSymbol, F.EVar v))

ignoreSelf :: F.Reft -> F.Reft
ignoreSelf = F.mapExpr (\r -> if selfSymbol `S.member` F.syms r then F.PTrue else r)

--------------------------------------------------------------------------------
-- | `projectTypes` masks (i.e. true's out) all types EXCEPT those
--   at given indices; it is used to simplify the environment used
--   when projecting out fields of single-ctor datatypes.
--------------------------------------------------------------------------------
projectTypes :: Bool -> Maybe [Int] -> [SpecType] -> CG [SpecType]
projectTypes _        Nothing    ts = return ts
projectTypes allowTC (Just ints) ts = mapM (projT ints) (zip [0..] ts)
  where
    projT is (j, t)
      | j `elem` is = return t
      | otherwise   = true allowTC t

altReft :: CGEnv -> [AltCon] -> AltCon -> F.Reft
altReft _ _   (LitAlt l) = literalFReft l
altReft γ acs DEFAULT    = mconcat ([notLiteralReft l | LitAlt l <- acs] ++ [notDataConReft d | DataAlt d <- acs])
  where
    notLiteralReft   = maybe mempty F.notExprReft . snd . literalConst (emb γ)
    notDataConReft d = F.Reft (F.vv_, F.PNot (F.EApp (F.EVar $ makeDataConChecker d) (F.EVar F.vv_)))
altReft _ _ _            = panic Nothing "Constraint : altReft"

unfoldR :: CGEnv -> SpecType -> SpecType -> [Var] -> (SpecType, [SpecType], SpecType)
unfoldR γ td (RApp _ ts rs _) ys = (t3, tvys ++ yts, ignoreOblig rt)
  where
        tbody                = instantiatePvs (instantiateTys γ td ts) (reverse rs)
        ((ys0,_,yts',_), rt) = safeBkArrow (F.notracepp msg $ defaultPvs $ instantiateTys γ tbody tvs')
        msg                  = "INST-TY: " ++ F.showpp (td, ts, tbody, ys, tvs')
        yts''                = zipWith F.subst sus (yts'++[rt])
        (t3,yts)             = (last yts'', init yts'')
        sus                  = F.mkSubst <$> L.inits [(x, F.EVar y) | (x, y) <- zip ys0 ys']
        (αs, ys')            = fmap F.symbol <$> L.partition isTyVar ys
        tvs' :: [SpecType]
        tvs'                 = rVar <$> αs
        tvys                 = ofType . varType <$> αs

unfoldR _ _  _                _  = panic Nothing "Constraint.hs : unfoldR"

instantiateTys :: CGEnv -> SpecType -> [SpecType] -> SpecType
instantiateTys γ = L.foldl' go
  where
    go (RAllT α tbody _) t = subsTyVarMeetWith (emb γ) (ty_var_value α, t) tbody
    go _ _                 = panic Nothing "Constraint.instantiateTy"

instantiatePvs :: SpecType -> [SpecProp] -> SpecType
instantiatePvs           = L.foldl' go
  where
    go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
    go t               _ = errorP "" ("Constraint.instantiatePvs: t = " ++ showpp t)

-- | @defaultPvs@ instantiates any leftover abstract-refinement binders (i.e.
--   'RAllP') with a trivial (i.e. @True@) predicate. This is needed when the
--   scrutinee's type carries fewer abstract-refinement arguments than the data
--   constructor expects. That happens, for example, when the scrutinee's type
--   is derived directly from a GHC 'Type' (as for @ignore@d bindings), since
--   @ofType@ produces an 'RApp' with an empty list of predicate arguments,
--   while the constructor's type (e.g. the dependent-pair encoding of tuples)
--   still quantifies over the abstract refinement.
--
--   See IgnoreTupleAbsRef for an example that used to crash without this
--   function.
defaultPvs :: SpecType -> SpecType
defaultPvs (RAllP p tbody) = defaultPvs (replacePreds "defaultPvs" tbody [(p, trueSpecProp p)])
defaultPvs t               = t

trueSpecProp :: RPVar -> SpecProp
trueSpecProp p = RProp [(s, t) | (t, s, _) <- pargs p] (ofRSort (pvType p))

checkTyCon :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkTyCon _ _ t@RApp{} = t
checkTyCon x g t        = checkErr x g t

checkFun :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkFun _ _ t@RFun{} = t
checkFun x g t        = checkErr x g t

checkAll :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkAll _ _ t@RAllT{} = t
checkAll x g t         = checkErr x g t

checkErr :: (Outputable a) => (String, a) -> CGEnv -> SpecType -> SpecType
checkErr (msg, e) γ t = panic (Just sp) $ msg ++ GM.showPpr e ++ ", type: " ++ showpp t
  where
    sp                = getLocation γ

varAnn :: CGEnv -> Var -> t -> Annot t
varAnn γ x t
  | x `S.member` recs γ = AnnLoc (getSrcSpan x)
  | otherwise           = AnnUse t

-----------------------------------------------------------------------
-- | Helpers: Creating Fresh Refinement -------------------------------
-----------------------------------------------------------------------
--------------------------------------------------------------------------------
-- | Helpers: Creating Refinement Types For Various Things ---------------------
--------------------------------------------------------------------------------
argType :: Type -> Maybe F.Expr
argType (LitTy (NumTyLit i)) = mkI i
argType (LitTy (StrTyLit s)) = Just $ mkS $ bytesFS s
argType (TyVarTy x)          = Just $ F.EVar $ F.symbol $ varName x
argType t
  | F.symbol (GM.showPpr t) == anyTypeSymbol
                             = Just $ F.EVar anyTypeSymbol
argType _                    = Nothing


argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr γ e | Just meaning <- wiredBoolean (emb γ) e = Just meaning
argExpr _ (Var v) = Just $ F.eVar v
argExpr γ (Lit c) = snd $ literalConst (emb γ) c
argExpr γ e@App{} | Just l <- boxedLiteralExpr γ e = Just l
argExpr γ (Tick _ e) = argExpr γ e
argExpr γ (App e (Type _)) = argExpr γ e
argExpr _ _ = Nothing


lamExpr :: CGEnv -> CoreExpr -> CG (Maybe F.Expr)
lamExpr g e = logicExpr g (coreToLogic e)

logicExpr :: CGEnv -> LogicM F.Expr -> CG (Maybe F.Expr)
logicExpr g interpretation = do
    adts <- gets cgADTs
    let dm = dataConMap adts
        translated = runToLogic (gsConstructorBoxes (gsName (giSpec (cgInfo g)))) (emb g) mempty dm (getConfig g)
          (\x -> todo Nothing ("coreToLogic not working lamExpr: " ++ x))
          interpretation
    return $ case eitherToMaybe translated of
      Just (meaning, _) | logicSymbolsInScope g adts meaning -> Just meaning
      _ -> Nothing

-- A synthesized singleton is optional, but every observation it mentions must
-- be declared in the checking environment. Test after substitution so unused
-- constructor fields do not require logical projections. Authored equations
-- remain subject to the mandatory specification checks.
logicSymbolsInScope :: CGEnv -> [F.DataDecl] -> F.Expr -> Bool
logicSymbolsInScope γ adts = all inScope . S.toList . F.syms
  where
    declarations = constEnv γ <> feEnv (fenv γ)
      <> fmap F.tsSort (maybe mempty F.theorySymbols (smtsolver (getConfig γ)))
      <> fmap F.tsSort (F.theorySymbols (if adtFlag γ then adts else []))
    inScope symbol = isJust (F.lookupSEnv symbol declarations)

--------------------------------------------------------------------------------
(??=) :: (?callStack :: CallStack) => CGEnv -> Var -> CG SpecType
--------------------------------------------------------------------------------
γ ??= x = case M.lookup x' (lcb γ) of
    Just e
        | Just _ <- dictionaryConstructorAt γ e -> do
            let recursive = maybe [] snd (recursiveDictionary γ e)
            unless (recursiveDictionaryInScope γ recursive) $
                addWarning $
                    ErrTermin
                        (getLocation γ)
                        [F.pprint x]
                        (text "Recursive dictionary is used before its decreasing argument is in scope")
            actual <- consE (γ -= x') e
            -- Named contracts constrain this additional constructor view.
            -- In particular, contravariance must not widen a captured
            -- callback's original admitted domain.
            addC (SubC γ tx actual) "recursive dictionary named contract"
            return actual
    Just e -> consE (γ -= x') e
    Nothing -> refreshTy tx
  where
    x' = F.symbol x
    tx = fromMaybe tt (γ ?= x')
    tt
        | isCoVar x =
            panic (Just (getLocation γ)) ("Coercion evidence is out of scope: " ++ GM.showPpr x)
        | otherwise = ofType $ varType x

recursiveDictionary :: CGEnv -> CoreExpr -> Maybe (CoreExpr, [SpecType])
recursiveDictionary γ expression = do
    recursive <- trec γ
    constructor <- dictionaryConstructorAt γ expression
    let fields =
            [ ty
            | owner <- nonDetEltsUniqSet (exprFreeVars constructor)
            , Just ty <- [M.lookup (F.symbol owner) recursive]
            ]
    if null fields then Nothing else Just (constructor, fields)

recursiveDictionaryInScope :: CGEnv -> [SpecType] -> Bool
recursiveDictionaryInScope γ = all (all inScope . S.toList . F.syms)
  where
    inScope symbol =
        isJust (γ ?= symbol)
            || isJust (F.lookupSEnv symbol (feEnv (fenv γ)))
            || isJust (F.lookupSEnv symbol (constEnv γ))
            || isJust (F.lookupSEnv symbol (litEnv γ))

--------------------------------------------------------------------------------
varRefType :: (?callStack :: CallStack) => CGEnv -> Var -> CG SpecType
--------------------------------------------------------------------------------
varRefType γ x =
  varRefType' γ x <$> (γ ??= x) -- F.tracepp (printf "varRefType x = [%s]" (showpp x))

varRefType' :: CGEnv -> Var -> SpecType -> SpecType
varRefType' γ x t'
  | Just tys <- trec γ, Just tr  <- M.lookup x' tys
  = strengthen' tr xr
  | otherwise
  = strengthen' t' xr
  where
    xr = singletonReft x
    x' = F.symbol x
    strengthen' | higherOrderFlag γ = strengthenMeet
                | otherwise         = strengthenTop

-- | create singleton types for function application
makeSingleton :: CGEnv -> CoreExpr -> SpecType -> SpecType
makeSingleton γ cexpr t
    | Just e <- wiredBoolean (emb γ) (simplify cexpr) =
        strengthenMeet t (uTop $ F.exprReft e)
    | Just e <- boxedLiteralExpr γ (simplify cexpr) =
        strengthenMeet t (uTop $ F.exprReft e)
    | higherOrderFlag γ
    , Var owner <- simplify cexpr =
        strengthenMeet t (uTop $ F.exprReft (F.eVar owner))
    | higherOrderFlag γ
    , App f x <- simplify cexpr =
        case (funExpr γ f, argForAllExpr x) of
            (Just f', Just x')
                | not (GM.isEmbeddedDictExpr x) -> -- (isClassPred $ exprType x)
                    strengthenMeet t (uTop $ F.exprReft (F.EApp f' x'))
            (Just f', Just _) ->
                strengthenMeet t (uTop $ F.exprReft f')
            _ -> t
    | rankNTypes (getConfig γ) =
        case argExpr γ (simplify cexpr) of
            Just e' -> strengthenMeet t $ uTop (F.exprReft e')
            _ -> t
    | otherwise =
        t
  where
    argForAllExpr (Var x)
      | rankNTypes (getConfig γ)
      , Just e <- M.lookup x (forallcb γ)
      = Just e
    argForAllExpr e
      = argExpr γ e

boxedLiteralExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
boxedLiteralExpr γ e
  | Just magnitude <- GM.integerLiteral (targetIntBits (getConfig γ)) e
  , typeSort (emb γ) (exprType e) == F.intSort
  = Just (F.expr magnitude)
boxedLiteralExpr γ e
  | (Var box, args) <- collectArgs e
  , [Lit c] <- filter isTermArg args
  , box == dataConWorkId intDataCon
      || simpleSymbolVar box `elem` ["I#", "W#", "F#", "D#"]
  = snd $ literalConst (emb γ) c
boxedLiteralExpr _ _ = Nothing

isTermArg :: CoreExpr -> Bool
isTermArg Type{}     = False
isTermArg Coercion{} = False
isTermArg _          = True



funExpr :: CGEnv -> CoreExpr -> Maybe F.Expr

funExpr _ (Var v)
  = Just $ F.EVar (F.symbol v)

funExpr γ (App e1 e2) =
    case (funExpr γ e1, argExpr γ e2) of
        (Just e1', Just e2')
            | not (GM.isEmbeddedDictExpr e2) -> -- (isClassPred $ exprType e2)
                Just (F.EApp e1' e2')
        (Just e1', Just _) -> Just e1'
        _                       -> Nothing
funExpr _ _
  = Nothing

simplify :: CoreExpr -> CoreExpr
simplify (Tick _ e)            = simplify e
simplify (App e (Type _))      = simplify e
simplify (App e1 e2)           = App (simplify e1) (simplify e2)
simplify (Lam x e) | isTyVar x = simplify e
simplify e                     = e


singletonReft :: (F.Symbolic a) => a -> UReft
singletonReft = uTop . F.symbolReft . F.symbol

-- | RJ: `nomeet` replaces `strengthenS` for `strengthen` in the definition
--   of `varRefType`. Why does `tests/neg/strata.hs` fail EVEN if I just replace
--   the `otherwise` case? The fq file holds no answers, both are sat.
strengthenTop :: (PPrint r, Meet r) => RType c tv r -> r -> RType c tv r
strengthenTop (RApp c ts rs r) r'   = RApp c ts rs   $ meet r r'
strengthenTop (RVar a r) r'         = RVar a         $ meet r r'
strengthenTop (RFun b i t1 t2 r) r' = RFun b i t1 t2 $ meet r r'
strengthenTop (RAppTy t1 t2 r) r'   = RAppTy t1 t2   $ meet r r'
strengthenTop (RAllT a t r)    r'   = RAllT a t      $ meet r r'
strengthenTop t _                   = t

-- TODO: this is almost identical to RT.strengthen! merge them!
strengthenMeet :: (PPrint r, Meet r) => RType c tv r -> r -> RType c tv r
strengthenMeet (RApp c ts rs r) r'  = RApp c ts rs (r `meet` r')
strengthenMeet (RVar a r) r'        = RVar a       (r `meet` r')
strengthenMeet (RFun b i t1 t2 r) r'= RFun b i t1 t2 (r `meet` r')
strengthenMeet (RAppTy t1 t2 r) r'  = RAppTy t1 t2 (r `meet` r')
strengthenMeet (RAllT a t r) r'     = RAllT a (strengthenMeet t r') (r `meet` r')
strengthenMeet t _                  = t

--------------------------------------------------------------------------------
-- | Cleaner Signatures For Rec-bindings ---------------------------------------
--------------------------------------------------------------------------------
exprLoc                         :: CoreExpr -> Maybe SrcSpan
exprLoc (Tick tt _)             = Just $ GM.tickSrcSpan tt
exprLoc (App e a) | isType a    = exprLoc e
exprLoc _                       = Nothing

isType :: Expr CoreBndr -> Bool
isType (Type _)                 = True
isType a                        = eqType (exprType a) predType

-- instance MonadFail CG where
--  fail msg = panic Nothing msg

instance MonadFail Data.Functor.Identity.Identity where
  fail msg = panic Nothing msg
