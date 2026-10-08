{-# LANGUAGE TupleSections #-}
-- | This module defines code for generating termination constraints.

module Language.Haskell.Liquid.Constraint.Termination (
  TCheck(..)
, mkTCheck
, doTermCheck
, makeTermEnvs
, makeDecrIndex
, checkIndex
, unOCons
, consCBSourceTys
, consCBWithExprs
, dictionaryConstructor
, dictionaryConstructorAt
) where

import           Data.Maybe ( isJust )
import qualified Data.List                          as L
import qualified Data.Graph                         as Graph
import qualified Data.HashSet                       as S
import qualified Data.Traversable                   as T
import qualified Data.HashMap.Strict                as M
import           Control.Monad ( foldM, forM, guard )
import           Control.Monad.State ( gets )
import           Text.PrettyPrint.HughesPJ ( (<+>), text )
import qualified Language.Haskell.Liquid.GHC.Misc                    as GM
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.SortCheck        as FC
import           Language.Haskell.Liquid.Constraint.Types (CG, CGInfo (..), CGEnv (..), FEnv (..), SubC (..), makeRecInvariants)
import           Language.Haskell.Liquid.Bare.Class (instanceDictionaryOwners)
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Constraint.Monad (addC, addWarning)
import           Language.Haskell.Liquid.Constraint.Env (addSortBind, setBind, setTRec)
import Language.Haskell.Liquid.Constraint.Template (Template (..), extender, recursiveCallable, recursiveHypothesis, unTemplate, varTemplate)
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types.Visitors (letVars)
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType (isDecreasing, mkDecrFun, makeLexRefa, makeNumEnv, ofType, rTypeSort, strengthen, uTop)
import           Language.Haskell.Liquid.Misc ((<->), safeFromJust, fst5)
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.Constraint.ToFixpoint (sourceNativeEnv)
import qualified Liquid.GHC.API as GHC
import           GHC.Types.Unique.Set (nonDetEltsUniqSet)
import           GHC.Core (mkVarApps)
import           GHC.Core.FVs (exprFreeIds)
import           GHC.Core.Utils (cheapEqExpr)
import           GHC.Core.Type (typeLevity_maybe)
import           GHC.Types.Basic (Levity (Lifted))
import           GHC.Types.Var (isTyCoVar)


data TCheck = TerminationCheck | StrataCheck | NoCheck
  deriving Show

mkTCheck :: Bool -> Bool -> TCheck
mkTCheck tc is
  | not is    = StrataCheck
  | tc        = TerminationCheck
  | otherwise = NoCheck

doTermCheck :: Config -> GHC.Bind GHC.Var -> CG Bool
doTermCheck cfg bind = do
    lazyVs <- gets specLazy
    termVs <- gets specTmVars
    let skip = any (\x -> S.member x lazyVs || nocheck x) xs
    let chk = not (structuralTerm cfg) || any (`S.member` termVs) xs
    return $ chk && not skip
  where
    nocheck = GM.isEmbeddedDictVar
    xs = GHC.bindersOf bind

makeTermEnvs ::
    CGEnv ->
    [(GHC.Var, [F.Located F.Expr])] ->
    [(GHC.Var, GHC.CoreExpr)] ->
    [SpecType] ->
    [(GHC.Var, Int, SpecType, SpecType)] ->
    [CGEnv]
makeTermEnvs γ xtes xes ts callees = setTRec γ . zip callOwners <$> rts
  where
    vs = zipWith collectArgs' ts ces
    syms = fst5 . bkArrowDeep . unOCons <$> ts
    (callOwners, prefixes, declarations, ts') = L.unzip4 callees
    callSyms = fst5 . bkArrowDeep . unOCons <$> declarations
    syms' = fst5 . bkArrowDeep . unOCons <$> ts'
    sus' = zipWith mkSub callSyms syms'
    sus = zipWith mkSub syms ((F.symbol <$>) <$> vs)
    ess = (\x -> safeFromJust (err x) (x `L.lookup` xtes)) <$> xs
    callEss = (\x -> safeFromJust (err x) (x `L.lookup` xtes)) <$> callOwners
    tes = zipWith (\su es -> F.subst su <$> es) sus ess
    tes' = zipWith (\su es -> F.subst su <$> es) sus' callEss
    rss = zipWith makeLexRefa tes' <$> (repeat <$> tes)
    rts = zipWith3 (\n t r -> addObligation n OTerm t r) prefixes ts' <$> rss
    (xs, ces) = unzip xes
    mkSub ys ys' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip ys ys']
    collectArgs' = collectArguments . length . ty_binds . toRTypeRep . unOCons
    err x = "Constant: makeTermEnvs: no terminating expression for " ++ GM.showPpr x

-- The source may return a function before binding every arrow in its type.
-- Check the recursive demand at that source boundary; a later function domain
-- is not a premise available while producing the closure itself.
-- Before that boundary, even a partially applied function's value predicates
-- are unproved. Preserve input domains, erase exposed value predicates, and
-- retain the complete result contract only behind the decrease obligation.
addObligation :: Int -> Oblig -> SpecType -> RReft -> SpecType
addObligation n o (RAllT a t _) obligation = RAllT a (addObligation n o t obligation) mempty
addObligation n o (RAllP p t) obligation = RAllP p (addObligation n o t obligation)
addObligation n o (RRTy xts r OCons t) obligation = RRTy xts r OCons (addObligation n o t obligation)
addObligation 0 o t obligation = RRTy [] obligation o t
addObligation n o (RFun x i tx t _) obligation = RFun x i tx (addObligation (n - 1) o t obligation) mempty
addObligation _ _ _ _ = panic Nothing "Termination.addObligation: source prefix exceeds callable telescope"

--------------------------------------------------------------------------------
-- | TERMINATION TYPE ----------------------------------------------------------
--------------------------------------------------------------------------------

makeDecrIndex :: CGEnv -> (GHC.Var, Template SpecType) -> CG (Maybe Int)
makeDecrIndex γ (x, Assumed t) =
    do
        dindex <- makeDecrIndexTy x t
        case dindex of
            Left msg -> requireUnreachable γ x msg >> return Nothing
            Right i -> return $ Just i
makeDecrIndex γ (x, Asserted t) =
    do
        dindex <- makeDecrIndexTy x t
        case dindex of
            Left msg -> requireUnreachable γ x msg >> return Nothing
            Right i -> return $ Just i
makeDecrIndex _ _ = return Nothing

-- Without a metric this group can only be checked in an unreachable scope.
-- Use the scope before extending it with this group's recursive hypotheses;
-- its unproved postconditions must not discharge its own termination goal.
requireUnreachable :: CGEnv -> GHC.Var -> Error -> CG ()
requireUnreachable γ owner err =
    addC (SubC ((γ `setBind` owner){cerr = Just err}) inhabited impossible) "unreachable recursive group"
  where
    inhabited = ofType GHC.boolTy
    impossible = strengthen inhabited (uTop F.falseReft)

makeDecrIndexTy :: GHC.Var -> SpecType -> CG (Either (TError t) Int)
makeDecrIndexTy x st
  = do autosz <- gets autoSize
       return $ case dindex autosz of
         Nothing -> Left msg
         Just i  -> Right i
    where
       msg  = ErrTermin (GHC.getSrcSpan x) [F.pprint x] (text "No decreasing parameter")
       trep = toRTypeRep $ unOCons st
       ts   = ty_args trep
       cenv = makeNumEnv ts

       p autosz t = isDecreasing autosz cenv t
       dindex     autosz = L.findIndex (p autosz) ts

checkIndex ::
    (GHC.NamedThing t, PPrint t, PPrint a) =>
    (t, [a], Template (RType c tv r), Maybe Int) ->
    CG (Maybe (RType c tv r))
checkIndex (_, _, _, Nothing) = return Nothing
checkIndex (x, vs, t, Just index) = do
    argument <- safeLogIndex msg1 vs index
    parameter <- safeLogIndex msg2 ts index
    pure (parameter <* argument)
  where
    loc = GHC.getSrcSpan x
    ts = ty_args $ toRTypeRep $ unOCons $ unTemplate t
    msg1 = ErrTermin loc [xd] (text "No decreasing" <+> F.pprint index <-> text "-th argument on" <+> xd <+> text "with" <+> F.pprint vs)
    msg2 = ErrTermin loc [xd] (text "No decreasing parameter")
    xd = F.pprint x

unOCons :: RType c tv r -> RType c tv r
unOCons (RAllT v t r)      = RAllT v (unOCons t) r
unOCons (RAllP p t)        = RAllP p $ unOCons t
unOCons (RFun x i tx t r)  = RFun x i (unOCons tx) (unOCons t) r
unOCons (RRTy _ _ OCons t) = unOCons t
unOCons t                  = t

safeLogIndex :: Error -> [a] -> Int -> CG (Maybe a)
safeLogIndex err ls n
    | n >= length ls = addWarning err >> return Nothing
    | otherwise = return $ Just $ ls !! n

-- RJ: AAAAAAARGHHH!!!!!! THIS CODE IS HORRIBLE!!!!!!!!!
consCBSourceTys ::
    (Bool -> CGEnv -> (GHC.Var, GHC.CoreExpr, Template SpecType) -> CG (Template SpecType)) ->
    CGEnv ->
    [(GHC.Var, GHC.CoreExpr)] ->
    CG CGEnv
consCBSourceTys consBind γ allXes =
    do
        scoped <- foldM scopeIntroduction γ introductions
        checked <- foldM checkGroup scoped groups
        foldM checkIntroduction checked introductions
  where
    (introductions, definitions) = L.partition (isJust . dictionaryConstructor γ . fst) allXes
    -- A finite record's identity is in the recursive source scope, including
    -- reflected applications in its fields. Its methods and constructor must
    -- still establish their contracts below; this supplies only a logical sort.
    scopeIntroduction env (owner, _) =
        addSortBind env
            (F.symbol owner, rTypeSort (emb env) (ofType (GHC.varType owner) :: SpecType))
    aliases =
        [ (owner, body, target)
        | (owner, body) <- definitions
        , Just target <- [aliasTarget [] owner]
        , target /= owner
        , target `elem` map fst definitions
        ]
    canonical owner = maybe owner (\(_, _, target) -> target) (L.find (\(alias, _, _) -> alias == owner) aliases)
    aliasTarget seen owner
        | owner `elem` seen = Nothing
        | Just target <- lookup owner definitions >>= aliasRhs
        , GHC.isFunTy (snd (GHC.splitForAllTyCoVars (GHC.varType owner)))
        , GHC.eqType (GHC.varType owner) (GHC.varType target) =
            aliasTarget (owner : seen) target
        | otherwise = Just owner
    -- Type/coercion abstraction introduces no runtime argument. Recognize
    -- its exact eta expansion too, without reducing value lambdas (which
    -- would change definedness) or instantiating the target differently.
    aliasRhs (GHC.Tick _ body) = aliasRhs body
    aliasRhs body = do
        let (binders, rhs) = GHC.collectBinders body
        guard (all isTyCoVar binders)
        (GHC.Var target, arguments, _) <- pure (GHC.collectArgsTicks (const True) rhs)
        guard (cheapEqExpr (GHC.mkApps (GHC.Var target) arguments) (mkVarApps (GHC.Var target) binders))
        pure target
    ordinary = [(owner, body) | (owner, body) <- definitions, canonical owner == owner]
    fields dictionary = lookup dictionary dictionaryFields
    dictionaryFields =
        [(owner, methods) | (owner, _) <- introductions, Just methods <- [instanceDictionaryOwners program owner]]
    program = giCbs (giSrc (cgInfo γ))
    spec = giSpec (cgInfo γ)
    -- A let-bound dictionary is an introduction, not a call of every method.
    -- Follow its lexical aliases only when identifying the field selected at
    -- a use. An escaping dictionary still depends on every field. All source
    -- bindings and their contracts remain separate constraint-generation goals.
    dependencies = demand []
    demand bindings expression
        | Just (owner, arguments) <- selectedField bindings [] expression =
            canonical owner : concatMap (demand bindings) arguments
    demand bindings (GHC.Let (GHC.NonRec owner rhs) body)
        | not (capturedByRefinement owner)
        , Just (_, arguments) <- knownDictionary bindings [] rhs =
            concatMap (demand bindings) arguments ++ demand ((owner, rhs) : bindings) body
    demand bindings expression
        | Just (methods, arguments) <- knownDictionary bindings [] expression =
            map (canonical . snd) methods ++ concatMap (demand bindings) arguments
    demand _ (GHC.Var owner) = [canonical owner]
    demand bindings (GHC.App function argument) = demand bindings function ++ demand bindings argument
    demand bindings (GHC.Lam _ body) = demand bindings body
    demand bindings (GHC.Let binding body) = concatMap (demand bindings . snd) (GHC.flattenBinds [binding]) ++ demand bindings body
    demand bindings (GHC.Case scrutinee _ _ alternatives) = demand bindings scrutinee ++ concat [demand bindings body | GHC.Alt _ _ body <- alternatives]
    demand bindings (GHC.Cast body _) = demand bindings body
    demand bindings (GHC.Tick _ body) = demand bindings body
    demand _ _ = []

    -- Open refinement queries are checked separately in their owner's scope.
    -- A captured record escapes this traversal, so retain all of its fields.
    capturedByRefinement owner =
        any (GHC.elemVarSet owner . exprFreeIds . refinementCheckExpr) (gsReftChecks (gsSig spec))
    selectedField bindings seen expression = do
        (GHC.Var selector, arguments, _) <- pure (GHC.collectArgsTicks (const True) expression)
        (_, dictionary : rest) <- pure (span isTypeArgument arguments)
        (methods, supplied) <- knownDictionary bindings seen dictionary
        owner <- lookup selector methods
        pure (owner, supplied ++ rest)
    knownDictionary bindings seen expression = do
        (GHC.Var owner, arguments, _) <- pure (GHC.collectArgsTicks (const True) expression)
        guard (owner `notElem` seen)
        case lookup owner bindings of
            Just rhs -> knownDictionary bindings (owner : seen) (GHC.mkApps rhs arguments)
            Nothing
                | Just methods <- fields owner -> Just (methods, arguments)
                | otherwise -> do
                    (field, supplied) <- selectedField bindings (owner : seen) expression
                    knownDictionary bindings (owner : seen) (GHC.mkApps (GHC.Var field) supplied)
    isTypeArgument GHC.Type{} = True
    isTypeArgument GHC.Coercion{} = True
    isTypeArgument _ = False
    associated owner = [(alias, body) | (alias, body, target) <- aliases, target == owner]
    symbols = M.fromList [(F.symbol owner, canonical owner) | (owner, _) <- definitions]
    logical (owner, body) =
        [ target
        | symbol <-
            concat
                [ foldReft False (\_ refinement acc -> S.toList (F.syms refinement) ++ acc) [] (F.val ty)
                | (declared, ty) <- gsTySigs (gsSig spec)
                , declared == owner
                ]
        , Just target <- [M.lookup symbol symbols]
        ]
            ++ concat
                [ dependencies (refinementCheckExpr check)
                | check <- gsReftChecks (gsSig spec)
                , refinementCheckOwner check `elem` letVars (GHC.NonRec owner body)
                ]
    groups =
        Graph.stronglyConnComp
            [ ((owner, body), F.symbol owner, map F.symbol (dependencies body ++ concatMap logical ((owner, body) : associated owner)))
            | (owner, body) <- ordinary
            ]
    checkGroup env (Graph.AcyclicSCC definition@(owner, _)) =
        checkIntroduction env definition >>= \checked -> foldM checkIntroduction checked (orderedAliases [owner])
    checkGroup env (Graph.CyclicSCC []) = pure env
    checkGroup env (Graph.CyclicSCC definitions') =
        consCBWithExprs consBind env definitions' (orderedAliases (map fst definitions')) canonical
    orderedAliases owners =
        map (\(owner, body, _) -> (owner, body)) $
            L.sortOn (aliasDepth . (\(owner, _, _) -> owner)) [row | row@(_, _, target) <- aliases, target `elem` owners]
    aliasDepth owner = case lookup owner definitions >>= aliasRhs of
        Just target | canonical owner /= owner -> 1 + aliasDepth target
        _ -> 0 :: Int
    checkIntroduction env (owner, body) = do
        target <- varTemplate env (owner, Just body)
        checked <- consBind False env (owner, body, target)
        extender env (owner, checked)

-- Recognize an actual dictionary constructor under its instance telescope.
-- The complete field application, not its polymorphic owner's type, decides
-- whether it stores a closure or a value. Every owner keeps its checking goal.
-- Cyclic values retain the ordinary recursive checking path; no field
-- contract is supplied by this test.
dictionaryConstructor :: CGEnv -> GHC.Var -> Maybe GHC.CoreExpr
dictionaryConstructor env owner = do
    guard (GHC.isDFunId owner)
    (body, parameters, fields) <- dictionaryDefinition owner
    guard (all (finiteField [owner] parameters . snd) fields)
    pure body
  where
    program = giCbs (giSrc (cgInfo env))
    definitions = GHC.flattenBinds program
    dictionaryDefinition dictionary = do
        body <- lookup dictionary definitions
        fields <- instanceDictionaryOwners program dictionary
        guard (not (null fields))
        pure (body, fst (GHC.collectBinders body), fields)
    finiteDictionary seen dictionary
        | dictionary `elem` seen = False
        | Just (_, parameters, fields) <- dictionaryDefinition dictionary =
            all (finiteField (dictionary : seen) parameters . snd) fields
        | otherwise = False
    finiteField seen parameters field
        | GHC.isFunTy (snd (GHC.splitForAllTyCoVars (GHC.exprType application))) = True
        | GHC.isDFunId field = finiteDictionary seen field
        | Just body <- lookup field definitions =
            all (finiteValue (field : seen)) (nonDetEltsUniqSet (exprFreeIds body))
        | otherwise = False
      where
        application = mkVarApps (GHC.Var field) parameters
    finiteValue seen field
        | field `elem` seen = False
        | GHC.isDFunId field, Just _ <- lookup field definitions = finiteDictionary seen field
        | GHC.isFunTy (snd (GHC.splitForAllTyCoVars (GHC.varType field))) = True
        | Just body <- lookup field definitions =
            all (finiteValue (field : seen)) (nonDetEltsUniqSet (exprFreeIds body))
        | otherwise = True

-- Instantiate only a fully applied, known introduction after its original call
-- is checked by Generate. Preserve its existing ANF field lets; rebuilding a
-- constructor with field applications would lose their dependent result scope.
-- GHC substitutes the actual type/evidence arguments and avoids capture in
-- those administrative binders. No method body is expanded.
dictionaryConstructorAt :: CGEnv -> GHC.CoreExpr -> Maybe GHC.CoreExpr
dictionaryConstructorAt env expression = do
    (GHC.Var owner, arguments, _) <- pure (GHC.collectArgsTicks (const True) expression)
    body <- dictionaryConstructor env owner
    let (parameters, constructor) = GHC.collectBinders body
    guard (length arguments == length parameters)
    let scope = GHC.mkInScopeSet (GHC.exprFreeVars expression `GHC.unionVarSet` GHC.exprFreeVars constructor)
    let substitution = GHC.extendSubstList (GHC.mkEmptySubst scope) (zip parameters arguments)
    pure (GHC.substExpr substitution constructor)

-- All elements of the input are equal to each other
allEqual :: Eq a => [a] -> Bool
allEqual []     = True
allEqual (x:xs) = all (== x) xs

-- See Note [Shape of normalized terms] in
-- Language.Haskell.Liquid.Transforms.ANF
collectArguments :: Int -> GHC.CoreExpr -> [GHC.Var]
collectArguments n = take n . fst . collectValBinders'

collectValBinders' :: GHC.CoreExpr -> ([GHC.Var], GHC.CoreExpr)
collectValBinders' = go []
  where
    go tvs (GHC.Lam b e) | isTyCoVar b = go tvs e
    go tvs (GHC.Lam b e) | GHC.isId b = go (b : tvs) e
    go tvs (GHC.Tick _ e) = go tvs e
    -- Lifted lets are lazy: exposing a following lambda does not demand the
    -- RHS. A strict/unlifted binding or a case is a real evaluation boundary.
    go tvs (GHC.Let (GHC.NonRec binder _) e)
        | typeLevity_maybe (GHC.varType binder) == Just Lifted = go tvs e
    go tvs e = (reverse tvs, e)

consCBWithExprs ::
    (Bool -> CGEnv -> (GHC.Var, GHC.CoreExpr, Template SpecType) -> CG (Template SpecType)) ->
    CGEnv ->
    [(GHC.Var, GHC.CoreExpr)] ->
    [(GHC.Var, GHC.CoreExpr)] ->
    (GHC.Var -> GHC.Var) ->
    CG CGEnv
consCBWithExprs consBind γ xes aliases canonical = do
    declarations <- forM xes $ \(owner, body) -> varTemplate γ (owner, Just body)
    authored <- gets termExprs
    autoenv <- gets autoSize
    let sourceTypes = unTemplate <$> declarations
    metrics <- forM (zip xes declarations) $ \((owner, body), target) ->
        case M.lookup owner authored of
            Just metric -> pure (Just (owner, metric))
            Nothing -> do
                index <- makeDecrIndex γ (owner, target)
                let ty = unTemplate target
                    binders = arguments ty
                    values = collectArguments (length binders) body
                parameter <- checkIndex (owner, values, target, index)
                pure $ do
                    i <- index
                    input <- parameter
                    pure (owner, [F.dummyLoc (mkDecrFun autoenv input (binders !! i))])
    checkedMetrics <- case sequence metrics of
        Nothing -> refuse missingMetric >> pure Nothing
        Just xtes -> case metricError xtes sourceTypes of
            Just problem -> refuse problem >> pure Nothing
            Nothing -> pure (Just xtes)
    targets <- mapM (T.mapM refreshArgs) declarations
    callables <- sequence $ zipWith (recursiveCallable γ) xs (unTemplate <$> targets)
    aliasDeclarations <- forM aliases $ \(owner, body) -> varTemplate γ (owner, Just body)
    aliasTargets <- mapM (T.mapM refreshArgs) aliasDeclarations
    aliasCallables <- sequence $ zipWith (recursiveCallable γ) (map fst aliases) (unTemplate <$> aliasTargets)
    let xts = zip xs targets
        owners = xs ++ map fst aliases
        sourcePrefixes =
            [(owner, length (collectArguments (length (arguments ty)) body)) | ((owner, body), ty) <- zip xes sourceTypes]
        prefix owner = safeFromJust "Termination: missing canonical source prefix" (lookup (canonical owner) sourcePrefixes)
        callees = L.zip4 owners (prefix <$> owners) (sourceTypes ++ map unTemplate aliasDeclarations) (callables ++ aliasCallables)
        aliasMetrics xtes =
            [ (owner, F.subst (F.mkSubst (zip (arguments source) (F.EVar <$> arguments (unTemplate target)))) <$> metric)
            | ((owner, _), target) <- zip aliases aliasDeclarations
            , Just source <- [lookup (canonical owner) (zip xs sourceTypes)]
            , Just metric <- [lookup (canonical owner) xtes]
            ]
    -- A recursive identity has a sort before it has established a value.
    -- Ordinary insertion would expose its claimed refinement, existential
    -- witnesses, and datatype invariants before a recursive demand is checked.
    -- Its callable contract is available only through the guarded trec entry.
    γ' <-
        foldM
            (\env owner -> addSortBind env (F.symbol owner, rTypeSort (emb env) (ofType (GHC.varType owner) :: SpecType)))
            γ
            owners
    let recursiveEnvs = case checkedMetrics of
            Just xtes -> makeTermEnvs γ' (xtes ++ aliasMetrics xtes) xes sourceTypes callees
            Nothing -> repeat $ setTRec γ' (zip owners (recursiveHypothesis <$> (callables ++ aliasCallables)))
        values = zipWith (\ty body -> filter (not . GM.isPredVar) (collectArguments (length (arguments ty)) body)) sourceTypes es
        environments = zipWith3 ownerInvariants xs recursiveEnvs values
        ownerInvariants owner env arguments
            | owner `M.member` authored = env
            | otherwise = makeRecInvariants env arguments
    mapM_ (uncurry $ consBind True) (zip environments (zip3 xs es targets))
    checked <- foldM extender γ xts
    foldM checkAlias checked (zip aliases aliasTargets)
  where
    -- Both sources describe ranks, not interchangeable input carriers. Infer
    -- each owner's expression in its own telescope, then use the same checked
    -- lexicographic obligation and alias transport as authored expressions.
    metricError xtes ts
        | not (allEqual (map (length . snd) xtes)) =
            Just (problem "Mutually recursive termination metrics must have the same number of components")
        | (owner, missing) : _ <-
            [ (owner, missing)
            | ((owner, body), ty) <- zip xes ts
            , Just metric <- [lookup owner xtes]
            , let unbound = drop (length (collectArguments (length (arguments ty)) body)) (arguments ty)
                  mentioned = F.syms (F.val <$> metric)
                  missing = filter (`S.member` mentioned) unbound
            , not (null missing)
            ] =
            Just
                ( ErrTermin
                    (GHC.getSrcSpan owner)
                    [F.pprint owner]
                    (text "Termination metric requires arguments not bound by this recursive definition:" <+> F.pprint missing)
                )
        | (owner, metric) : _ <-
            [ (owner, metric)
            | (owner, ty) <- zip xs ts
            , Just metrics <- [lookup owner xtes]
            , metric <- metrics
            , FC.checkSortExpr (sourceNativeEnv (getConfig γ) (gsADTs (gsName (giSpec (cgInfo γ))))) (GM.srcSpanFSrcSpan (GHC.getSrcSpan owner)) (metricEnv ty) (F.val metric) /= Just F.FInt
            ] =
            Just
                ( ErrTermin
                    (GHC.getSrcSpan owner)
                    [F.pprint owner]
                    (text "Termination metric must have an integer sort in its owner's argument scope:" <+> F.pprint metric)
                )
        | otherwise = Nothing
    metricEnv :: SpecType -> F.SEnv F.Sort
    metricEnv ty =
        F.fromListSEnv (zip (arguments ty) (rTypeSort (emb γ) <$> ty_args (toRTypeRep (unOCons ty))))
            <> feEnv (fenv γ)
            <> litEnv γ
            <> constEnv γ
    refuse err = mapM_ (\owner -> requireUnreachable γ owner err) xs
    missingMetric = problem "Every mutually recursive source binder requires a valid, bound termination metric"
    problem message = ErrTermin (GHC.getSrcSpan (head xs)) (F.pprint <$> xs) (text message)
    (xs, es) = unzip xes
    arguments = fst5 . bkArrowDeep . unOCons
    checkAlias env ((owner, body), target) = do
        checked <- consBind False env (owner, body, target)
        extender env (owner, checked)
